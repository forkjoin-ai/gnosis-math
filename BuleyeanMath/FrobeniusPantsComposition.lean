import Init

/-!
# Frobenius Pants Composition — Atiyah–Segal Bridge Module

This module bridges `OneCobFrobenius.lean` and
`MoonshotTopologicalWitnessCobordism.lean`. It witnesses the
Atiyah–Segal 1-TQFT dictionary

    point              ↦ A = (ℤ/2)[x]/(x²)
    identity   ∥       ↦ id_A
    cap        ∩       ↦ ε ∘ m       (pair-and-trace)
    cup        ∪       ↦ Δ ∘ η       (co-pair)
    pants      ⋎       ↦ m
    copants    ⋏       ↦ Δ

on a specific finite algebra and specific cobordisms drawn from the
peer modules. The full functor category `Cob₁ → Vect` is not built;
this module realizes four concrete compositional identities closed by
kernel `decide`.

## What is witnessed

* `Z_identity_preserves_one` and `Z_identity_preserves_x`: the
  identity-cobordism acts as the identity map on the algebra.
* `snake_on_one` and `snake_on_x`: the left zig-zag
  `(id ⊗ ε ∘ m) ∘ ((Δ ∘ η) ⊗ id)` is the identity on `A` on both
  basis elements.
* `y_pants_eq_h_pants` and `y_pants_eq_h_pants_right`: the two pants
  decompositions `Δ ∘ m = (m ⊗ id) ∘ (id ⊗ Δ) = (id ⊗ m) ∘ (Δ ⊗ id)`
  agree on every pure tensor `(a, b) ∈ A × A`.
* `torus_partition_value`: the genus-1 partition function
  `Z(torus) = ε(Σᵢ m(eᵢ, e^i))` on the dual-basis pairing of `A`
  evaluates to `0` in `ℤ/2`.

## Not witnessed

* The functor category `Cob₁`. No object-morphism infrastructure.
* General 2D TQFT content. No handle decompositions beyond the
  finite algebra examples here.
* A topological triangulation of the torus. Item 4 computes the
  partition value from the algebraic trace formula
  `ε(Σᵢ m(eᵢ, e^i))`, not from a surface-level combinatorial model.

No `sorry`, no new `axiom`. `import Init` only. Peer definitions are
inlined to keep the module self-contained.
-/

namespace BuleyeanMath
namespace FrobeniusPantsComposition

/-! ## Inlined from `OneCobFrobenius.lean` -/

/-- Base ring `R = ℤ/2`, represented as `Bool`. -/
abbrev R := Bool

/-- Scalar addition in `ℤ/2`. -/
@[inline] def radd (a b : R) : R := xor a b

/-- Scalar multiplication in `ℤ/2`. -/
@[inline] def rmul (a b : R) : R := a && b

/-- Algebra `A = (ℤ/2)[x]/(x²)` in the basis `{1, x}`. -/
structure A where
  /-- Coefficient of the basis vector `1`. -/
  one : R
  /-- Coefficient of the basis vector `x`. -/
  x   : R
deriving DecidableEq, Repr

/-- Zero element of `A`. -/
def A.zero : A := ⟨false, false⟩

/-- Componentwise addition in `A`. -/
def A.add (a b : A) : A := ⟨radd a.one b.one, radd a.x b.x⟩

/-- Tensor algebra `A ⊗ A` in the four-element basis. -/
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

/-- Pure tensor `a ⊗ b`. -/
def tensor (a b : A) : AA :=
  { c11 := rmul a.one b.one
  , c1x := rmul a.one b.x
  , cx1 := rmul a.x   b.one
  , cxx := rmul a.x   b.x }

/-- Unit `η : R → A`, `r ↦ r · 1`. -/
def unit (r : R) : A := ⟨r, false⟩

/-- Counit `ε : A → R`, reading off the `x`-coefficient. -/
def counit (a : A) : R := a.x

/-- Multiplication `m : A ⊗ A → A`. -/
def mult (p : AA) : A :=
  { one := p.c11
  , x   := radd p.c1x p.cx1 }

/-- Comultiplication `Δ : A → A ⊗ A`. -/
def comult (a : A) : AA :=
  { c11 := false
  , c1x := a.one
  , cx1 := a.one
  , cxx := a.x }

/-! ## Inlined boundary alphabet from
`MoonshotTopologicalWitnessCobordism.lean` -/

/-- Fixed boundary alphabet size. -/
abbrev n : Nat := 4

/-- A boundary is an ordered list of points on `Fin n`. -/
abbrev Boundary := List (Fin n)

/-- The two-point boundary `[0, 1]`. -/
def σTwo : Boundary := [⟨0, by decide⟩, ⟨1, by decide⟩]

/-- The empty boundary. -/
def σEmpty : Boundary := []

/-- The one-point boundary `[0]`. -/
def σOne : Boundary := [⟨0, by decide⟩]

/-- Combinatorial cobordism: routing plus interior pair-offs. -/
structure Cobordism (σ₀ σ₁ : Boundary) where
  /-- Interior pair-offs. -/
  interiorPairs : List (Fin n × Fin n)
  /-- The points that flow through to `σ₁`. -/
  routed        : Boundary
  /-- The routed list equals the outgoing boundary. -/
  routed_eq     : routed = σ₁
  /-- Count bookkeeping. -/
  count_eq      : σ₀.length = σ₁.length + 2 * interiorPairs.length

/-- Identity cobordism on a boundary `σ`. -/
def idCob (σ : Boundary) : Cobordism σ σ :=
  { interiorPairs := []
  , routed        := σ
  , routed_eq     := rfl
  , count_eq      := by simp }

/-- Cap cobordism `σTwo → σEmpty`. -/
def capCob : Cobordism σTwo σEmpty :=
  { interiorPairs := [(⟨0, by decide⟩, ⟨1, by decide⟩)]
  , routed        := []
  , routed_eq     := rfl
  , count_eq      := by decide }

/-! ## Atiyah–Segal functor `Z` on inlined generators -/

/-- The TQFT image of `point`. Definitionally `A`, labeled for clarity. -/
abbrev ZPoint : Type := A

/-- The TQFT image of the identity cobordism `idCob σOne`. -/
def Zid (a : A) : A := a

/-- Concrete basis vectors. -/
def e1 : A := ⟨true, false⟩   -- 1
def ex : A := ⟨false, true⟩   -- x

/-! ### Target 1 — `Z(identity)` is the identity map on `A` -/

/-- The TQFT acts as the identity on the basis vector `1`. -/
theorem Z_identity_preserves_one : Zid e1 = e1 := by decide

/-- The TQFT acts as the identity on the basis vector `x`. -/
theorem Z_identity_preserves_x : Zid ex = ex := by decide

/-- The TQFT acts as the identity on every `a : A`. -/
theorem Z_identity_preserves_all (a : A) : Zid a = a := by
  cases a with
  | mk o x1 => cases o <;> cases x1 <;> decide

/-! ### Target 2 — Snake (zig-zag) identity on a single point

The left zig-zag of the Frobenius duality pairing:

    A  →^{γ ⊗ id}  (A ⊗ A) ⊗ A  →^{id ⊗ β}  A

with copairing `γ(r) = Δ(η(r)) = r · (1 ⊗ x + x ⊗ 1)` and pairing
`β(a, b) = ε(m(a, b))`. We verify `(id ⊗ β) ∘ (γ ⊗ id) = id_A` on both
basis elements.
-/

/-- Scalar multiplication of `a : A` by `r : R`. -/
@[inline] def smulR (r : R) (a : A) : A :=
  ⟨rmul r a.one, rmul r a.x⟩

/-- The pairing `β : A ⊗ A → R`, `β(a, b) = ε(m(a ⊗ b))`. -/
def beta (a b : A) : R := counit (mult (tensor a b))

/-- The copairing `γ : R → A ⊗ A`, `γ(r) = Δ(η(r))`. -/
def gamma (r : R) : AA := comult (unit r)

/--
Left-snake map. Starting from `a`, apply `γ` on the left slot to lift
to `A ⊗ A ⊗ A`, then pair the two rightmost slots with `β`. The
result re-lands in `A` by recombining the surviving leftmost factor.

Using `γ(1) = 1 ⊗ x + x ⊗ 1`, this unfolds to

    a ↦ β(x, a) · 1 + β(1, a) · x.
-/
def snake (a : A) : A :=
  A.add (smulR (beta ex a) e1) (smulR (beta e1 a) ex)

/-- Snake on `1` returns `1`. -/
theorem snake_on_one : snake e1 = e1 := by decide

/-- Snake on `x` returns `x`. -/
theorem snake_on_x : snake ex = ex := by decide

/-- Snake is the identity on every `a : A` (exhaustive 4-case check). -/
theorem snake_identity (a : A) : snake a = a := by
  cases a with
  | mk o x1 => cases o <;> cases x1 <;> decide

/-! ### Target 3 — Frobenius Y-pants = H-pants

`Δ ∘ m` (*Y-pants decomposition*), `(m ⊗ id) ∘ (id ⊗ Δ)` (*H-pants
decomposition, left form*), and `(id ⊗ m) ∘ (Δ ⊗ id)` (*H-pants
decomposition, right form*) all agree as maps `A ⊗ A → A ⊗ A` on every
pure tensor `(a, b)`.
-/

/-- Y-pants: multiply then comultiply. -/
def yPants (a b : A) : AA := comult (mult (tensor a b))

/-- H-pants, left form: `(m ⊗ id)(a ⊗ Δ(b))`. -/
def hPantsLeft (a b : A) : AA :=
  let d := comult b
  { c11 := rmul a.one d.c11
  , c1x := rmul a.one d.c1x
  , cx1 := radd (rmul a.x d.c11) (rmul a.one d.cx1)
  , cxx := radd (rmul a.x d.c1x) (rmul a.one d.cxx) }

/-- H-pants, right form: `(id ⊗ m)(Δ(a) ⊗ b)`. -/
def hPantsRight (a b : A) : AA :=
  let d := comult a
  { c11 := rmul d.c11 b.one
  , c1x := radd (rmul d.c11 b.x) (rmul d.c1x b.one)
  , cx1 := rmul d.cx1 b.one
  , cxx := radd (rmul d.cx1 b.x) (rmul d.cxx b.one) }

/-- Y-pants equals H-pants-left on every pure tensor `(a, b)`. -/
theorem y_pants_eq_h_pants (a b : A) : yPants a b = hPantsLeft a b := by
  cases a with
  | mk ao ax =>
    cases b with
    | mk bo bx =>
      cases ao <;> cases ax <;> cases bo <;> cases bx <;> decide

/-- Y-pants equals H-pants-right on every pure tensor `(a, b)`. -/
theorem y_pants_eq_h_pants_right (a b : A) : yPants a b = hPantsRight a b := by
  cases a with
  | mk ao ax =>
    cases b with
    | mk bo bx =>
      cases ao <;> cases ax <;> cases bo <;> cases bx <;> decide

/-- Transitively, the two H-pants decompositions agree. -/
theorem h_pants_left_eq_right (a b : A) : hPantsLeft a b = hPantsRight a b := by
  cases a with
  | mk ao ax =>
    cases b with
    | mk bo bx =>
      cases ao <;> cases ax <;> cases bo <;> cases bx <;> decide

/-! ### Target 4 — Genus-1 torus partition function

For the Frobenius form `β(a, b) = ε(m(a, b))` on `A`, the Gram matrix in
basis `{1, x}` is

    β(1, 1) = 0,  β(1, x) = 1,
    β(x, 1) = 1,  β(x, x) = 0,

so the dual basis under `β` is `1^* = x`, `x^* = 1`. The torus
partition function is

    Z(torus) = ε(Σᵢ m(eᵢ, e^i)) = ε(m(1, x) + m(x, 1)) = ε(x + x) = ε(0) = 0.

We compute the `A`-valued inner sum and the scalar `ε`-reduction.
-/

/-- Inner sum `Σᵢ m(eᵢ, e^i) = m(1, x) + m(x, 1)` as an element of `A`. -/
def torusInnerSum : A :=
  A.add (mult (tensor e1 ex)) (mult (tensor ex e1))

/-- The inner torus sum collapses to `0` in `A` (because `x + x = 0`). -/
theorem torus_inner_sum_zero : torusInnerSum = A.zero := by decide

/-- The torus partition function `Z(torus) = ε(Σᵢ m(eᵢ, e^i))`. -/
def Ztorus : R := counit torusInnerSum

/-- Genus-1 partition value vanishes in `ℤ/2`. -/
theorem torus_partition_value : Ztorus = false := by decide

/-! ### Cobordism-level labels

Witness that the peer cobordism objects — `idCob σOne` and `capCob` —
correspond under `Z` to the algebra maps `Zid` and
`λ (a, b) => counit (mult (tensor a b))`. The correspondence is
*definitional* here, recorded as two small sanity identities.
-/

/-- `Z(idCob σOne)` as the identity map, routed through `Zid`. -/
def Z_idCob (_ : Cobordism σOne σOne) : A → A := Zid

/-- `Z(capCob)` as the pair-and-trace map `A × A → R`. -/
def Z_capCob (_ : Cobordism σTwo σEmpty) : A → A → R := beta

/-- The identity-cobordism image, evaluated on `1`, is `1`. -/
theorem Z_idCob_on_one :
    Z_idCob (idCob σOne) e1 = e1 := by decide

/-- The identity-cobordism image, evaluated on `x`, is `x`. -/
theorem Z_idCob_on_x :
    Z_idCob (idCob σOne) ex = ex := by decide

/-- The cap-cobordism image pairs `(1, x)` to `1`. -/
theorem Z_capCob_pairs_one_x :
    Z_capCob capCob e1 ex = true := by decide

/-- The cap-cobordism image pairs `(x, 1)` to `1`. -/
theorem Z_capCob_pairs_x_one :
    Z_capCob capCob ex e1 = true := by decide

/-- The cap-cobordism image pairs `(1, 1)` to `0`. -/
theorem Z_capCob_kills_one_one :
    Z_capCob capCob e1 e1 = false := by decide

/-- The cap-cobordism image pairs `(x, x)` to `0`. -/
theorem Z_capCob_kills_x_x :
    Z_capCob capCob ex ex = false := by decide

/-! ### Aggregate witness

A single decidable bundle tying together every bridge identity proved
in this module.
-/

/-- Aggregate Frobenius-pants composition witness. -/
theorem frobenius_pants_composition_witness :
    Zid e1 = e1 ∧
    Zid ex = ex ∧
    snake e1 = e1 ∧
    snake ex = ex ∧
    yPants e1 e1 = hPantsLeft e1 e1 ∧
    yPants e1 ex = hPantsLeft e1 ex ∧
    yPants ex e1 = hPantsLeft ex e1 ∧
    yPants ex ex = hPantsLeft ex ex ∧
    yPants e1 e1 = hPantsRight e1 e1 ∧
    yPants e1 ex = hPantsRight e1 ex ∧
    yPants ex e1 = hPantsRight ex e1 ∧
    yPants ex ex = hPantsRight ex ex ∧
    torusInnerSum = A.zero ∧
    Ztorus = false := by
  decide

end FrobeniusPantsComposition
end BuleyeanMath
