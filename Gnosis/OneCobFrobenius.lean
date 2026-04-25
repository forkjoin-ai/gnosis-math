import Init

/-!
# One-Dimensional TQFT as a Frobenius Algebra (finite instance)

This module realizes the algebraic skeleton of a 1D TQFT on the explicit
Frobenius algebra `A = (ℤ/2)[x] / (x²)` — the "dual numbers" over `ℤ/2`.

Under the Atiyah–Segal dictionary for Cob₁ a 1D TQFT `Z : Cob₁ → Vect_R`
maps the generating cobordisms to algebraic data on `A = Z(point)`:

    point         ↦ A
    birth  ∅ → pt ↦ η : R → A             (unit)
    death  pt → ∅ ↦ ε : A → R             (counit / trace)
    pants  pt⊔pt → pt ↦ m : A ⊗ A → A     (multiplication)
    copants pt → pt⊔pt ↦ Δ : A → A ⊗ A    (comultiplication)

The functoriality on the full cobordism category is not formalized here;
building Cob₁ in Lean is not tractable in a single module. What this
file proves is the core algebraic identity — the Frobenius relation

    (m ⊗ id) ∘ (id ⊗ Δ)  =  Δ ∘ m

on the explicit four-element algebra over `ℤ/2` with basis `{1, x}` and
`x² = 0`, closed by finite case analysis (`decide`).
-/

namespace Gnosis
namespace OneCobFrobenius

/-- The base ring `R = ℤ/2`, represented as `Bool` with
addition `xor` and multiplication `and`. -/
abbrev R := Bool

/-- Scalar addition in `ℤ/2`. -/
@[inline] def radd (a b : R) : R := xor a b

/-- Scalar multiplication in `ℤ/2`. -/
@[inline] def rmul (a b : R) : R := a && b

/--
An element of `A = (ℤ/2)[x]/(x²)` is a pair `(a₀, a₁)` representing
`a₀ · 1 + a₁ · x`. The underlying set has four elements.
-/
structure A where
  /-- Coefficient of the basis vector `1`. -/
  one : R
  /-- Coefficient of the basis vector `x`. -/
  x   : R
deriving DecidableEq, Repr

/-- Zero element of `A`. -/
def A.zero : A := ⟨false, false⟩

/-- Componentwise addition in `A` (`ℤ/2` coefficients). -/
def A.add (a b : A) : A := ⟨radd a.one b.one, radd a.x b.x⟩

/--
An element of `A ⊗ A` expressed in the tensor basis
`{1⊗1, 1⊗x, x⊗1, x⊗x}` as four `ℤ/2` coefficients.
-/
structure AA where
  /-- Coefficient of `1 ⊗ 1`. -/
  c11 : R
  /-- Coefficient of `1 ⊗ x`. -/
  c1x : R
  /-- Coefficient of `x ⊗ 1`. -/
  cx1 : R
  /-- Coefficient of `x ⊗ x`. -/
  cxx : R
deriving DecidableEq, Repr

/-- Zero element of `A ⊗ A`. -/
def AA.zero : AA := ⟨false, false, false, false⟩

/-- Componentwise addition in `A ⊗ A`. -/
def AA.add (p q : AA) : AA :=
  ⟨radd p.c11 q.c11, radd p.c1x q.c1x, radd p.cx1 q.cx1, radd p.cxx q.cxx⟩

/-- The pure tensor `a ⊗ b ∈ A ⊗ A` expanded in the four-element basis. -/
def tensor (a b : A) : AA :=
  { c11 := rmul a.one b.one
  , c1x := rmul a.one b.x
  , cx1 := rmul a.x   b.one
  , cxx := rmul a.x   b.x }

/-! ### Structure maps -/

/-- Unit `η : R → A`, sending `r ↦ r · 1`. -/
def unit (r : R) : A := ⟨r, false⟩

/-- Counit (trace form) `ε : A → R`, sending `a₀·1 + a₁·x ↦ a₁`. -/
def counit (a : A) : R := a.x

/--
Multiplication `m : A ⊗ A → A`. On a pure tensor this is the algebra
product `(a₀+a₁x)(b₀+b₁x) = a₀b₀ + (a₀b₁+a₁b₀)x` (with `x² = 0`),
extended linearly through the four tensor-basis coefficients.
-/
def mult (p : AA) : A :=
  { one := p.c11
  , x   := radd p.c1x p.cx1 }

/--
Comultiplication `Δ : A → A ⊗ A`, the unique `R`-linear map that pairs
with the counit `ε` above as a Frobenius form. Concretely:

    Δ(1) = 1⊗x + x⊗1,       Δ(x) = x⊗x.
-/
def comult (a : A) : AA :=
  { c11 := false
  , c1x := a.one
  , cx1 := a.one
  , cxx := a.x }

/-! ### Sanity checks on unit and counit -/

/-- Left unit law: `m(η(1) ⊗ a) = a` for every `a : A`. -/
theorem mult_unit_left (a : A) : mult (tensor (unit true) a) = a := by
  cases a with
  | mk o x1 => cases o <;> cases x1 <;> decide

/-- Right unit law: `m(a ⊗ η(1)) = a` for every `a : A`. -/
theorem mult_unit_right (a : A) : mult (tensor a (unit true)) = a := by
  cases a with
  | mk o x1 => cases o <;> cases x1 <;> decide

/-- The counit pairs `1 ↔ x`: `ε(1·x) = 1`. -/
theorem counit_pairs_one_x :
    counit (mult (tensor (unit true) ⟨false, true⟩)) = true := by
  decide

/-- The counit kills `1·1`: `ε(1·1) = 0`. -/
theorem counit_kills_one_one :
    counit (mult (tensor (unit true) (unit true))) = false := by
  decide

/-! ### Main theorem: the Frobenius identity

We prove, on pure tensors `a ⊗ b`, that

    Δ(m(a, b))  =  (m ⊗ id)(a ⊗ Δ(b)).

This is the Frobenius condition in element form. Because `A` has
exactly four elements over `ℤ/2`, the identity is closed by finite
case analysis (`decide`).
-/

/-- Left-hand side of the Frobenius identity: `Δ ∘ m` on `a ⊗ b`. -/
def frobeniusLHS (a b : A) : AA := comult (mult (tensor a b))

/--
Right-hand side of the Frobenius identity: `(m ⊗ id)` applied to
`a ⊗ Δ(b)`. Expanding `Δ(b)` into the four basis components
`(left_i, right_i) = (1,1), (1,x), (x,1), (x,x)` and multiplying each
left factor by `a` gives the coefficient formulas below in `{1⊗1,
1⊗x, x⊗1, x⊗x}`.
-/
def frobeniusRHS (a b : A) : AA :=
  let d := comult b
  { c11 := rmul a.one d.c11
  , c1x := rmul a.one d.c1x
  , cx1 := radd (rmul a.x d.c11) (rmul a.one d.cx1)
  , cxx := radd (rmul a.x d.c1x) (rmul a.one d.cxx) }

/--
The Frobenius identity on `A = (ℤ/2)[x]/(x²)`.

`Δ ∘ m` and `(m ⊗ id) ∘ (id ⊗ Δ)` agree on every pure tensor `a ⊗ b`.
With four elements in `A`, this is 16 cases, each verified by `decide`.
-/
theorem frobenius_identity (a b : A) : frobeniusLHS a b = frobeniusRHS a b := by
  cases a with
  | mk ao ax =>
    cases b with
    | mk bo bx =>
      cases ao <;> cases ax <;> cases bo <;> cases bx <;> decide

/--
Global form: the Frobenius identity as equality of functions
`A → A → AA`. Follows from `frobenius_identity` by `funext`.
-/
theorem frobenius_identity_global :
    (fun a b => frobeniusLHS a b) = (fun a b => frobeniusRHS a b) := by
  funext a b
  exact frobenius_identity a b

end OneCobFrobenius
end Gnosis
