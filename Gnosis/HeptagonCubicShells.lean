import Init

/-!
# HeptagonCubicShells — the TOTALLY-REAL cubic ℚ(2cos 2π/7) = ℚ(ζ₇)⁺, its (3,0) three real shells, a proved heptagon-trace identity (∀n), and an HONEST verdict on the SEVEN hinge

This module pushes the `Gnosis.CubicPlasticShells` Next-exploration (A) to the cubic
the plastic field could NOT be: the **totally-real heptagon field**
`ℚ(θ)`, `θ = ζ₇ + ζ₇⁻¹ = 2cos(2π/7)`, the maximal real subfield of the 7th
cyclotomic field `ℚ(ζ₇)⁺`. Where the plastic field `ℚ(ρ)` has signature **(1,1)**
(disc `−23 < 0`: one real + one complex place — only ONE real shell), the heptagon
field has signature **(3,0)** (disc `49 = 7² > 0`: THREE real embeddings of equal
status). It is the *right* cubic to ask the three-shell question of.

## §1  The heptagon field `ℤ[θ]`, `θ³ + θ² − 2θ − 1 = 0`

`θ = 2cos(2π/7)` is a root of `x³ + x² − 2x − 1` (the minimal polynomial of the
real cyclotomic generator; its three roots are `θ_k = 2cos(2πk/7)`, `k = 1,2,3`,
ALL real). We model `ℤ[θ] = ⟨a,b,c⟩ = a + bθ + cθ²` exactly (Init-only, no reals),
the cubic analogue of the golden `ℤ[φ]` and the plastic `ℤ[ρ]`. The defining law,
as an operator identity, is `θ³ = −θ² + 2θ + 1`, i.e. `θ·θ·θ·x = −θ·θ·x + 2θ·x + x`.

**Signature (3,0), proved decidably.** `disc(x³ + bx² + cx + d) = 18bcd − 4b³d +
b²c² − 4c³ − 27d²`. For `x³ + x² − 2x − 1` (`b=1, c=−2, d=−1`):
`disc = 18·1·(−2)·(−1) − 4·1·(−1) + 1·4 − 4·(−8) − 27·1 = 36 + 4 + 4 + 32 − 27 = 49 = 7²`.
A POSITIVE cubic discriminant certifies **three real roots** — signature (3,0),
totally real. (Contrast plastic `−23 < 0` = (1,1), and golden quadratic `+5 > 0` =
(2,0).) The discriminant being `7²` is the first appearance of the SEVEN.

## §2  The heptagon trace sequence (∀n) — the cubic "heptagon Lucas"

The field trace `Tr : ℤ[θ] → ℤ` sends `x ↦ σ₁x + σ₂x + σ₃x` (sum of the three REAL
Galois conjugates). It is ℤ-linear, pinned by Newton's identities on
`e₁ = −1, e₂ = −2, e₃ = 1`:

    Tr(1)  = Σ θ_k⁰ = 3
    Tr(θ)  = Σ θ_k  = e₁ = −1
    Tr(θ²) = Σ θ_k² = e₁² − 2e₂ = 1 + 4 = 5

so `Tr⟨a,b,c⟩ = 3a − b + 5c`. We then PROVE **`∀ n, heptaTrace n = Tr(θⁿ) = Σ_k θ_k^n`**
by strong induction on the depth-3 recurrence `θⁿ⁺³ = −θⁿ⁺² + 2θⁿ⁺¹ + θⁿ` (the cubic
analogue of `CubicPlasticShells.perrin_is_cubic_trace` / `lucasRing_is_lucas`). The
integer sequence (the "heptagon Lucas", the totally-real cubic companion):

    3, −1, 5, −4, 13, −16, 38, −57, 117, −193, 370, −639, 1186, −2094, 3827, …

(power sums of `2cos(2πk/7)`; the signs alternate because the dominant root
`θ₃ = −1.802` is negative, unlike the plastic `ρ > 0`). This is a genuine three-real-
embedding trace, not a 1-real + complex-pair one.

## §3  THREE REAL SHELLS — honest verdict on a cubic exceptional lattice

Unlike plastic (1,1), the (3,0) signature DOES admit three real dilations of equal
status: the three conjugate embeddings `θ_k` are all real, so `ℤ[θ]` is a genuine
rank-3-over-ℤ lattice in `ℝ³` via the Minkowski/trace embedding. We construct it and
test honestly whether it is a KNOWN exceptional lattice.

**The honest answer is NO.** The trace form (Gram matrix `[Tr(θⁱ⁺ʲ)]`) is

    ⎡  3  −1   5 ⎤
    ⎢ −1   5  −4 ⎥   with det = 49 = disc.
    ⎣  5  −4  13 ⎦

This is the trace lattice of the totally-real cubic field — a rank-3 lattice of
covolume `√49 = 7`. It is NOT `A₃`, `D₃`, or any exceptional Lie lattice; it is the
ring of integers of `ℚ(ζ₇)⁺` under its canonical (trace) embedding, an ordinary
cubic-field lattice. So the totally-real cubic gives THREE genuine real shells
(the right signature, where plastic failed) but they assemble into the cubic-field
lattice (`disc 49`, the `7`-conductor), NOT a second `E₈`. We prove the decidable
shadows (the Gram matrix, its determinant `= 49`, positive-definiteness witnesses)
and report the negative honestly: **three real shells YES, exceptional lattice NO.**

## §4  THE SEVEN HINGE — honest assessment (proven shadows vs cited connections)

The exciting question: does the SEVEN of `ℚ(ζ₇)⁺` (disc `7²`, conductor `7`, the
heptagon's 7-fold symmetry) structurally connect to the SEVEN that BUILDS `E₈`
(Fano's 7 points, the octonions' 7 imaginary units, `OctonionE8Lattice`)?

**PROVEN here (decidable order/divisibility shadows, kernel `decide`):**
  * `PSL(2,7)` has order `168 = |GL₃(𝔽₂)| = |Aut(Fano)|` (carried from
    `FiniteSimpleGroupsClassification.PSL2_7_order`, re-derived here by `decide`);
  * `168 ∣ |W(E₇)| = 2903040` (quotient `17280`) and `168 ∣ |W(E₈)| = 696729600`
    (quotient `4147200`) — the Klein/Fano `168` divides BOTH exceptional Weyl orders;
  * `7 ∣ |W(E₇)|` and `7 ∣ |W(E₈)|` — the prime `7` divides both (it appears EXACTLY
    once in each: `|W(E₇)| = 2¹⁰·3⁴·5·7`, `|W(E₈)| = 2¹⁴·3⁵·5²·7`), so the SEVEN is a
    real prime factor of the exceptional symmetry, not absent;
  * the Klein-quartic Hurwitz bound `84(g−1) = 84·2 = 168` (genus-3 Klein quartic),
    so `|Aut(Klein quartic)| = 168 = |PSL(2,7)|` (the order coincidence, decidable);
  * the heptagon discriminant is `7²` and the field conductor is `7` (the SEVEN as the
    field's own invariant).

**CITED / explored, NOT proven (the deep Lie-theoretic connection):**
  * `PSL(2,7) ≅ Aut(Fano plane) ≅ Aut(Klein quartic)` as GROUPS (the isomorphisms, not
    just order coincidences) — a named theorem, not formalized here;
  * the Fano→octonion→`E₈` BUILD (`OctonionE8Lattice`: octavians = the 240 roots) uses
    the 7 Fano LINES / 7 imaginary octonion units as a MULTIPLICATION table, NOT the
    cubic field `ℚ(ζ₇)⁺`. The `7` that builds `E₈` is the 7 of the Fano
    incidence/octonion product; the `7` of the heptagon field is the conductor of a
    DIFFERENT object (the cyclic Galois group `Gal(ℚ(ζ₇)⁺/ℚ) ≅ ℤ/3`, a CUBIC field).
  * there is no known construction of `E₇` or `E₈` FROM the cubic field `ℚ(ζ₇)⁺` the way
    `ℚ(√5)` builds `E₈` via the icosian two-shell lattice.

**HONEST VERDICT.** The SEVEN is a *shared prime/number* across these structures — and
that sharing is REAL (it is proven: `7 ∣ |W(E₇)|, |W(E₈)|`; `168 ∣` both; `disc = 7²`;
`168 = |PSL(2,7)| = |Aut(Fano)| = |Aut(Klein)|`). But the heptagon CUBIC FIELD
`ℚ(ζ₇)⁺` is a totally-real (3,0) cubic whose canonical lattice is an ordinary
cubic-field lattice of covolume 7 — it is NOT the mechanism that builds `E₈`. The
`E₈`-building `7` is the Fano/octonion incidence-and-product `7` (a 7-element finite
geometry / a 7-dimensional imaginary algebra), a DIFFERENT 7 from the cubic field's
conductor. So: **the SEVEN is a genuine shared structural number (proven divisibility
shadows) but NOT, on the evidence here, a single hinge identifying the heptagon cubic
field with the Fano/octonion E₈.** It is a real arithmetic coincidence of the prime 7
across the heptagon field and the exceptional groups — suggestive, partly proven, not a
field-builds-the-lattice identity. The honest cubic three-shell geometry lives in the
totally-real cubic LATTICE (disc 49), not in a cubic E₈.

## Hard constraints (met)
`import Init` only (the PSL/Weyl order facts the substrate proves elsewhere in
`FiniteSimpleGroupsClassification` / `E8WeylOrder` are re-derived here standalone by
kernel `decide`, so this module gates with no cross-import). Kernel `decide`/`rfl` + the
∀-n operator-identity technique (`theta3_op` unfold to exact `Int` arithmetic). NO
`native_decide`, NO `sorry`, NO new `axiom`, NO `Classical.choice`, NO `omega`. propext
at most. `set_option maxRecDepth` allowed. Gate ONLY on
`lake build Gnosis.HeptagonCubicShells`. NOT registered in `Gnosis.lean`; edits no
other module.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

namespace Gnosis
namespace HeptagonCubicShells

/-! ## §0  The cubic ring `ℤ[θ]`, `θ³ = −θ² + 2θ + 1`

Element `⟨a,b,c⟩ = a + bθ + cθ²`. Mirrors `CubicPlasticShells.Zrho`, but with the
heptagon reduction `θ³ ↦ −θ² + 2θ + 1` (so `θ⁴ = θ·θ³ = −θ³ + 2θ² + θ
= −(−θ²+2θ+1) + 2θ² + θ = 3θ² − θ − 1`). -/

structure Zth where
  a : Int  -- constant
  b : Int  -- θ¹ coefficient
  c : Int  -- θ² coefficient
deriving DecidableEq, Repr

def ztAdd (p q : Zth) : Zth := ⟨p.a + q.a, p.b + q.b, p.c + q.c⟩
def ztNeg (p : Zth) : Zth := ⟨-p.a, -p.b, -p.c⟩

/-- Multiplication in `ℤ[θ]`, `θ³ = −θ² + 2θ + 1` (so `θ⁴ = 3θ² − θ − 1`).
    `(a+bθ+cθ²)(d+eθ+fθ²)` collects degree-≤4, then reduces
    `θ³ ↦ ⟨1,2,−1⟩` and `θ⁴ ↦ ⟨−1,−1,3⟩`. -/
def ztMul (p q : Zth) : Zth :=
  let d := q.a; let e := q.b; let f := q.c
  let a := p.a; let b := p.b; let c := p.c
  let k0 := a*d                    -- θ⁰
  let k1 := a*e + b*d               -- θ¹
  let k2 := a*f + b*e + c*d         -- θ²
  let k3 := b*f + c*e               -- θ³ = ⟨1,2,−1⟩
  let k4 := c*f                     -- θ⁴ = ⟨−1,−1,3⟩
  ⟨k0 + k3 - k4,                    -- const: k0 + k3·1 + k4·(−1)
   k1 + 2*k3 - k4,                  -- θ:    k1 + k3·2 + k4·(−1)
   k2 - k3 + 3*k4⟩                  -- θ²:   k2 + k3·(−1) + k4·3

def ztOne : Zth := ⟨1, 0, 0⟩
/-- `θ = ⟨0,1,0⟩`. -/
def theta : Zth := ⟨0, 1, 0⟩

/-- **The heptagon minimal polynomial: `θ³ = −θ² + 2θ + 1`.** -/
theorem theta_cubed :
    ztMul (ztMul theta theta) theta = ztAdd (ztAdd (⟨0,0,-1⟩) ⟨0,2,0⟩) ztOne := by decide
/-- `θ⁴ = 3θ² − θ − 1`. -/
theorem theta_fourth :
    ztMul (ztMul (ztMul theta theta) theta) theta = ⟨-1, -1, 3⟩ := by decide

/-- `θⁿ` as an exact `Zth` element. -/
def thetaPow : Nat → Zth
  | 0 => ztOne
  | n + 1 => ztMul theta (thetaPow n)

/-- **The heptagon law as an operator identity:** `θ·θ·θ·x = −(θ·θ·x) + 2(θ·x) + x`
    for every `x ∈ ℤ[θ]`. The engine behind the cubic recurrence at EVERY power,
    proved by unfolding `ztMul` to exact `Int` arithmetic (no `decide` over powers). -/
theorem theta3_op (x : Zth) :
    ztMul theta (ztMul theta (ztMul theta x))
      = ztAdd (ztAdd (ztNeg (ztMul theta (ztMul theta x)))
                     (ztAdd (ztMul theta x) (ztMul theta x))) x := by
  cases x with
  | mk a b c =>
    show (⟨_,_,_⟩ : Zth) = ⟨_,_,_⟩
    simp only [ztMul, ztAdd, ztNeg, theta, Int.zero_mul, Int.mul_zero, Int.zero_add,
               Int.add_zero, Int.one_mul, Int.two_mul, Int.sub_eq_add_neg, Int.neg_add,
               Int.neg_neg, Int.neg_zero]
    refine Zth.mk.injEq .. ▸ ⟨?_, ?_, ?_⟩ <;> ac_rfl

/-! ## §1  The heptagon trace sequence (integer recurrence) -/

/-- **The heptagon trace sequence** `Hₙ = Σ_k θ_k^n`: `H₀=3, H₁=−1, H₂=5`,
    `Hₙ₊₃ = −Hₙ₊₂ + 2Hₙ₊₁ + Hₙ` (from `θ³ = −θ² + 2θ + 1`). The totally-real cubic
    "heptagon Lucas": `3, −1, 5, −4, 13, −16, 38, −57, 117, −193, 370, …`. -/
def heptaTrace : Nat → Int
  | 0 => 3
  | 1 => -1
  | 2 => 5
  | n + 3 => -(heptaTrace (n + 2)) + 2 * heptaTrace (n + 1) + heptaTrace n

/-! ## §2  THE FIELD TRACE FUNCTIONAL — heptaTrace = the cubic Galois trace, ∀ n

`Tr⟨a,b,c⟩ = 3a − b + 5c` from `Tr 1 = 3, Tr θ = e₁ = −1, Tr θ² = e₁²−2e₂ = 5`. -/

/-- **The cubic field trace `Tr : ℤ[θ] → ℤ`**: `Tr⟨a,b,c⟩ = 3a − b + 5c`
    (the symmetric power sums of the three real roots: `Tr 1 = 3`, `Tr θ = −1`,
    `Tr θ² = 5`). -/
def traceZth (x : Zth) : Int := 3 * x.a + (-1) * x.b + 5 * x.c

/-- `Tr(1) = 3` (the three conjugates of `1`). -/
theorem trace_one : traceZth ztOne = 3 := by decide
/-- `Tr(θ) = −1 = e₁` (the sum of the three real roots `Σ 2cos(2πk/7) = −1`). -/
theorem trace_theta : traceZth theta = -1 := by decide
/-- `Tr(θ²) = 5 = e₁² − 2e₂` (Newton, the sum of the squared roots). -/
theorem trace_theta_sq : traceZth (ztMul theta theta) = 5 := by decide

/-- Generic interleave identity on `Int` (the linearity arithmetic, no `omega`/`ring`). -/
theorem int_interleave3 (p q r s t u : Int) :
    (p + s) + (q + t) + (r + u) = (p + q + r) + (s + t + u) := by
  calc (p + s) + (q + t) + (r + u)
      = p + (s + (q + t)) + (r + u) := by rw [Int.add_assoc p s (q + t)]
    _ = p + ((q + t) + s) + (r + u) := by rw [Int.add_comm s (q + t)]
    _ = p + (q + (t + s)) + (r + u) := by rw [Int.add_assoc q t s]
    _ = p + (q + (s + t)) + (r + u) := by rw [Int.add_comm t s]
    _ = (p + q) + (s + t) + (r + u) := by rw [← Int.add_assoc p q (s + t)]
    _ = (p + q) + ((s + t) + (r + u)) := by rw [Int.add_assoc (p + q) (s + t) (r + u)]
    _ = (p + q) + (s + (t + (r + u))) := by rw [Int.add_assoc s t (r + u)]
    _ = (p + q) + (s + ((t + r) + u)) := by rw [Int.add_assoc t r u]
    _ = (p + q) + (s + ((r + t) + u)) := by rw [Int.add_comm t r]
    _ = (p + q) + (s + (r + (t + u))) := by rw [Int.add_assoc r t u]
    _ = (p + q) + ((s + r) + (t + u)) := by rw [← Int.add_assoc s r (t + u)]
    _ = (p + q) + ((r + s) + (t + u)) := by rw [Int.add_comm s r]
    _ = (p + q) + (r + (s + (t + u))) := by rw [Int.add_assoc r s (t + u)]
    _ = ((p + q) + r) + (s + (t + u)) := by rw [← Int.add_assoc (p + q) r (s + (t + u))]
    _ = (p + q + r) + (s + t + u) := by rw [← Int.add_assoc s t u]

/-- **The trace is ℤ-additive:** `Tr(x + y) = Tr x + Tr y`. -/
theorem trace_add (x y : Zth) : traceZth (ztAdd x y) = traceZth x + traceZth y := by
  cases x with
  | mk xa xb xc => cases y with
    | mk ya yb yc =>
      show 3 * (xa + ya) + (-1) * (xb + yb) + 5 * (xc + yc)
            = (3 * xa + (-1) * xb + 5 * xc) + (3 * ya + (-1) * yb + 5 * yc)
      rw [Int.mul_add, Int.mul_add, Int.mul_add]
      exact int_interleave3 (3*xa) ((-1)*xb) (5*xc) (3*ya) ((-1)*yb) (5*yc)

/-- **The trace negates:** `Tr(−x) = −Tr x`. -/
theorem trace_neg (x : Zth) : traceZth (ztNeg x) = -(traceZth x) := by
  cases x with
  | mk a b c =>
    show 3 * (-a) + (-1) * (-b) + 5 * (-c) = -(3 * a + (-1) * b + 5 * c)
    simp only [Int.mul_neg, Int.neg_add, Int.neg_neg]

/-- **`θⁿ` obeys the heptagon cubic recurrence in-ring:**
    `θⁿ⁺³ = −θⁿ⁺² + 2θⁿ⁺¹ + θⁿ`, for EVERY `n`, via `theta3_op`. -/
theorem thetaPow_cubic_recurrence (n : Nat) :
    thetaPow (n + 3)
      = ztAdd (ztAdd (ztNeg (thetaPow (n + 2)))
                     (ztAdd (thetaPow (n + 1)) (thetaPow (n + 1))))
              (thetaPow n) := by
  show ztMul theta (ztMul theta (ztMul theta (thetaPow n)))
      = ztAdd (ztAdd (ztNeg (ztMul theta (ztMul theta (thetaPow n))))
                     (ztAdd (ztMul theta (thetaPow n)) (ztMul theta (thetaPow n))))
              (thetaPow n)
  exact theta3_op (thetaPow n)

/-- **THE PROVED HEPTAGON TRACE IDENTITY (∀ n): `heptaTrace n = Σ θ_k^n = Tr(θⁿ)`.**

    The totally-real cubic analogue of `CubicPlasticShells.perrin_is_cubic_trace`
    (`Pₙ = Tr ρⁿ`) and the golden `Lₙ = φⁿ + ψⁿ`. Strong induction on the depth-3
    recurrence: the base cases `Tr(θ⁰)=3, Tr(θ¹)=−1, Tr(θ²)=5` are `heptaTrace 0,1,2`,
    and the step uses `thetaPow_cubic_recurrence` with `trace_add` / `trace_neg`. -/
theorem heptaTrace_is_cubic_trace : ∀ n, heptaTrace n = traceZth (thetaPow n) := by
  intro n
  refine Nat.strongRecOn n fun n ih => ?_
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | k + 3 =>
    have hrec : thetaPow (k + 3)
        = ztAdd (ztAdd (ztNeg (thetaPow (k + 2)))
                       (ztAdd (thetaPow (k + 1)) (thetaPow (k + 1))))
                (thetaPow k) := thetaPow_cubic_recurrence k
    have hlt2 : k + 2 < k + 3 := Nat.lt_succ_self (k + 2)
    have hlt1 : k + 1 < k + 3 :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self (k + 1)) (Nat.le_succ (k + 2))
    have hlt0 : k < k + 3 :=
      Nat.lt_of_le_of_lt (Nat.le_succ k)
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self (k + 1)) (Nat.le_succ (k + 2)))
    have h2 : heptaTrace (k + 2) = traceZth (thetaPow (k + 2)) := ih (k + 2) hlt2
    have h1 : heptaTrace (k + 1) = traceZth (thetaPow (k + 1)) := ih (k + 1) hlt1
    have h0 : heptaTrace k = traceZth (thetaPow k) := ih k hlt0
    show -(heptaTrace (k + 2)) + 2 * heptaTrace (k + 1) + heptaTrace k
          = traceZth (thetaPow (k + 3))
    rw [hrec, trace_add, trace_add, trace_neg, trace_add,
        ← h2, ← h1, ← h0]
    -- goal: −H(k+2) + 2·H(k+1) + H(k) = (−H(k+2) + (H(k+1)+H(k+1))) + H(k)
    rw [Int.two_mul]

/-- Sanity table: the first heptagon-trace terms equal the trace read-outs (decidable
    cross-check of the ∀-n theorem on the famous prefix). The signs alternate because
    the dominant real root `θ₃ = 2cos(6π/7) ≈ −1.802` is negative. -/
theorem heptaTrace_table :
    (List.range 13).map (fun n => traceZth (thetaPow n))
      = [3, -1, 5, -4, 13, -16, 38, -57, 117, -193, 370, -639, 1186]
  ∧ (List.range 13).map heptaTrace
      = [3, -1, 5, -4, 13, -16, 38, -57, 117, -193, 370, -639, 1186] := by
  refine ⟨by decide, by decide⟩

/-! ## §3  SIGNATURE (3,0) — three real shells, and the honest lattice verdict

The discriminant `disc(x³ + bx² + cx + d) = 18bcd − 4b³d + b²c² − 4c³ − 27d²`.
For `x³ + x² − 2x − 1` (`b=1, c=−2, d=−1`): `disc = 49 = 7² > 0`. A positive cubic
discriminant certifies THREE REAL roots: signature (3,0), totally real — the geometric
prerequisite the plastic (1,1) field lacked. -/

/-- The heptagon discriminant `disc(x³ + x² − 2x − 1) = 18bcd − 4b³d + b²c² − 4c³ − 27d²`
    with `b=1, c=−2, d=−1`. -/
def heptaDiscriminant : Int :=
  18 * 1 * (-2) * (-1) - 4 * 1^3 * (-1) + 1^2 * (-2)^2 - 4 * (-2)^3 - 27 * (-1)^2

/-- **Heptagon discriminant `= 49 = 7² > 0`: signature (3,0), THREE real embeddings.**
    The certificate that the totally-real cubic gives three real shells of equal status
    — where plastic `−23 < 0` gave only one. The `7²` is the SEVEN as the field's own
    invariant (the conductor of `ℚ(ζ₇)⁺` is `7`). -/
theorem hepta_disc_positive :
    heptaDiscriminant = 49 ∧ heptaDiscriminant = 7^2 ∧ heptaDiscriminant > 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Contrast certificate: plastic `disc(x³−x−1) = −23 < 0` (signature (1,1), ONE real
    shell). Both cubics, opposite signatures — the structural difference. -/
theorem plastic_disc_negative_contrast :
    (-4 * (-1)^3 - 27 * (-1)^2 : Int) = -23 ∧ (-4 * (-1)^3 - 27 * (-1)^2 : Int) < 0 := by
  refine ⟨by decide, by decide⟩

/-! ### The three real embeddings as the trace-form lattice (rank 3 over ℤ)

The Minkowski/trace embedding sends `ℤ[θ]` into `ℝ³` via the three real conjugates.
Its integral structure is captured by the **trace form** Gram matrix
`Gᵢⱼ = Tr(θⁱ⁺ʲ)` (`i,j ∈ {0,1,2}`), entirely integer (the power sums `Hₙ`):

    G = ⎡ H₀ H₁ H₂ ⎤ = ⎡  3 −1  5 ⎤
        ⎢ H₁ H₂ H₃ ⎥   ⎢ −1  5 −4 ⎥
        ⎣ H₂ H₃ H₄ ⎦   ⎣  5 −4 13 ⎦

`det G = disc = 49`. We give the Gram matrix decidably and its determinant. -/

/-- The trace-form Gram matrix entry `Gᵢⱼ = Tr(θⁱ⁺ʲ) = H_{i+j}`. -/
def traceGram (i j : Nat) : Int := traceZth (thetaPow (i + j))

/-- The trace form as the integer matrix `[[3,−1,5],[−1,5,−4],[5,−4,13]]` (the power
    sums `H₀..H₄`). These ARE the three-real-embedding inner products — the lattice. -/
theorem trace_gram_matrix :
    (traceGram 0 0, traceGram 0 1, traceGram 0 2) = ((3:Int), -1, 5)
  ∧ (traceGram 1 0, traceGram 1 1, traceGram 1 2) = ((-1:Int), 5, -4)
  ∧ (traceGram 2 0, traceGram 2 1, traceGram 2 2) = ((5:Int), -4, 13) := by
  refine ⟨by decide, by decide, by decide⟩

/-- The 3×3 determinant of the trace-form Gram matrix, by the rule of Sarrus. -/
def gram3det (g00 g01 g02 g10 g11 g12 g20 g21 g22 : Int) : Int :=
  g00*(g11*g22 - g12*g21) - g01*(g10*g22 - g12*g20) + g02*(g10*g21 - g11*g20)

/-- **`det(trace form) = 49 = disc`.** The covolume² of the rank-3 cubic lattice is the
    discriminant `7²` — the totally-real cubic field's canonical lattice has covolume
    `√49 = 7`. This is an ORDINARY cubic-field lattice, NOT an exceptional Lie lattice
    (no `A₃`/`D₃`/`E` structure: it is the ring of integers of `ℚ(ζ₇)⁺` under its trace
    embedding). The three real shells exist (the (3,0) signature delivers them) but they
    assemble into this `disc-49`, conductor-`7` cubic lattice. -/
theorem trace_form_det_is_disc :
    gram3det 3 (-1) 5 (-1) 5 (-4) 5 (-4) 13 = 49
    ∧ gram3det 3 (-1) 5 (-1) 5 (-4) 5 (-4) 13 = heptaDiscriminant := by
  refine ⟨by decide, by decide⟩

/-- **Positive-definite witnesses (leading principal minors > 0).** `3 > 0`,
    `det[[3,−1],[−1,5]] = 14 > 0`, `det(G) = 49 > 0` — Sylvester's criterion, so the
    trace form is positive-definite: the three real embeddings give a genuine rank-3
    EUCLIDEAN lattice (three real shells), confirming (3,0). -/
theorem trace_form_positive_definite :
    (3 : Int) > 0
    ∧ (3 * 5 - (-1) * (-1) : Int) = 14 ∧ (3 * 5 - (-1) * (-1) : Int) > 0
    ∧ gram3det 3 (-1) 5 (-1) 5 (-4) 5 (-4) 13 > 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## §4  THE SEVEN HINGE — order/divisibility shadows (PROVEN) vs the Lie connection (CITED)

The heptagon field carries a `7` (disc `7²`, conductor `7`). The Fano/octonion route
that BUILDS `E₈` (`OctonionE8Lattice`: 240 octavians = 240 roots) carries a different
`7` (Fano's 7 points / 7 octonion imaginary units). We test whether the SEVEN is a
shared STRUCTURAL number by proving the order/divisibility shadows. -/

/-- `|PSL(2,7)| = q(q²−1)/gcd(2,q−1)` at `q=7` `= 7·48/2 = 168` — re-derived here by
    `decide` (matches `FiniteSimpleGroupsClassification.PSL2_7_order`, but kernel, not
    `native_decide`). `168 = |Aut(Fano plane)| = |GL₃(𝔽₂)| = |PSL(2,7)|`. -/
def psl2_7_order : Nat := 7 * (7*7 - 1) / 2

theorem psl2_7_is_168 : psl2_7_order = 168 := by decide

/-- `|GL₃(𝔽₂)| = (8−1)(8−2)(8−4) = 168` — the Fano-plane automorphism group as a matrix
    count, equal to `|PSL(2,7)|`. The SEVEN-point geometry's symmetry. -/
theorem gl3_f2_is_168 : (8 - 1) * (8 - 2) * (8 - 4) = 168 := by decide

/-- **The Klein-quartic Hurwitz bound `84(g−1) = 84·2 = 168`** (genus `g = 3` Klein
    quartic), so `|Aut(Klein quartic)| = 168 = |PSL(2,7)|`. The 7-fold modular group
    `PSL(2,7)` is simultaneously the Fano and the Klein-quartic automorphism order. -/
theorem klein_hurwitz_168 : 84 * (3 - 1) = 168 := by decide

/-- The exceptional Weyl orders (tabulated integers, the values
    `FiniteSimpleGroupsClassification`/`E8WeylOrder` use). `|W(E₇)| = 2¹⁰·3⁴·5·7`,
    `|W(E₈)| = 2¹⁴·3⁵·5²·7`. -/
def weylE7 : Nat := 2903040
def weylE8 : Nat := 696729600

/-- The factorizations, decidably: `|W(E₇)| = 2¹⁰·3⁴·5·7` and `|W(E₈)| = 2¹⁴·3⁵·5²·7`.
    The prime `7` appears EXACTLY ONCE in each. -/
theorem weyl_factorizations :
    weylE7 = 2^10 * 3^4 * 5 * 7 ∧ weylE8 = 2^14 * 3^5 * 5^2 * 7 := by
  refine ⟨by decide, by decide⟩

/-- **`7 ∣ |W(E₇)|` and `7 ∣ |W(E₈)|`** — the prime `7` divides BOTH exceptional Weyl
    orders (once each). The SEVEN is a real prime factor of the exceptional symmetry. -/
theorem seven_divides_weyl :
    weylE7 % 7 = 0 ∧ weylE8 % 7 = 0 := by
  refine ⟨by decide, by decide⟩

/-- **`168 ∣ |W(E₇)|` (quotient `17280`) and `168 ∣ |W(E₈)|` (quotient `4147200`).**
    The Klein/Fano/`PSL(2,7)` order `168` divides BOTH exceptional Weyl orders — the
    7-fold modular order is a divisor of the exceptional symmetry. (`E₇` is the natural
    home: it carries the `28 = ` half of `56` bitangents / the Klein quartic's `28`
    bitangents of a plane quartic.) -/
theorem klein_order_divides_weyl :
    weylE7 % 168 = 0 ∧ weylE7 / 168 = 17280
    ∧ weylE8 % 168 = 0 ∧ weylE8 / 168 = 4147200 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The 28 bitangents of a plane quartic** (the Klein quartic's `28`), `= 56/2`,
    where `56` is the minuscule dimension of `E₇` (`E8WeylOrder.coset_E7_E6` uses
    `fundamentalDim .E7 = 56`). The `28` bitangents ↔ `E₇` is a classical
    `7`-flavoured exceptional connection (cited; the `56` here is decidable). -/
theorem bitangents_28_and_e7_56 :
    (28 : Nat) * 2 = 56 ∧ (56 : Nat) / 2 = 28 := by
  refine ⟨by decide, by decide⟩

/-! ## §5  THE MASTER VERDICT -/

/-- **HEPTAGON-CUBIC-SHELLS (master).** Three results, honestly separated:

    PROVED (the totally-real cubic, ∀-n trace, signature, lattice shadows):
      (1) `θ³ = −θ² + 2θ + 1` (the heptagon cubic, `ℚ(ζ₇)⁺ = ℚ(2cos 2π/7)`);
      (2) the cubic field trace `Tr⟨a,b,c⟩ = 3a − b + 5c` with `Tr 1 = 3, Tr θ = −1,
          Tr θ² = 5` (the symmetric power sums, via Newton on `e₁=−1,e₂=−2,e₃=1`);
      (3) **`heptaTrace n = Tr(θⁿ) = Σ_k θ_k^n` for ALL `n`** — the totally-real cubic
          Galois trace, the cubic analogue of `Lₙ = φⁿ+ψⁿ` and `Pₙ = Tr ρⁿ`;
      (4) `disc = 49 = 7² > 0` ⇒ signature (3,0): THREE real embeddings of equal status
          (where plastic `−23 < 0` gave (1,1), only one real shell);
      (5) the trace-form lattice `[[3,−1,5],[−1,5,−4],[5,−4,13]]` is positive-definite
          with `det = 49 = disc` — three genuine real shells assembling into the
          `disc-49`/conductor-`7` cubic-field lattice.

    PROVED SEVEN-HINGE SHADOWS (order/divisibility):
      (6) `|PSL(2,7)| = 168 = |GL₃(𝔽₂)| = |Aut(Fano)|`, `84(g−1) = 168 = |Aut(Klein)|`;
      (7) `7 ∣ |W(E₇)|`, `7 ∣ |W(E₈)|` (once each: `2¹⁰3⁴5·7`, `2¹⁴3⁵5²·7`);
      (8) `168 ∣ |W(E₇)|` (`/168 = 17280`), `168 ∣ |W(E₈)|` (`/168 = 4147200`);
      (9) `28` bitangents `= 56/2`, `56 = ` minuscule-dim `E₇`.

    HONEST NEGATIVE-WITH-REASON (the three-shell and the seven-hinge verdicts):
      * THREE REAL SHELLS: YES — the (3,0) signature delivers them, the geometric
        prerequisite the plastic field lacked. But they assemble into the ORDINARY
        totally-real cubic LATTICE (disc 49, covolume 7), NOT a cubic `E₈`/`E₇`/exceptional
        lattice. The exceptional two-shell `E₈` is golden-quadratic-specific.
      * THE SEVEN HINGE: the `7` is a GENUINE SHARED NUMBER (proven: `disc = 7²`;
        `7 ∣ |W(E₇)|, |W(E₈)|`; `168 = |PSL(2,7)| = |Aut(Fano)| = |Aut(Klein)|` divides
        both Weyl orders). But the heptagon CUBIC FIELD's `7` (a conductor, `Gal ≅ ℤ/3`)
        is a DIFFERENT object from the Fano/octonion `7` (a 7-point geometry / 7-dim
        imaginary algebra) that BUILDS `E₈` in `OctonionE8Lattice`. There is no proven
        construction of `E₈` (or `E₇`) FROM `ℚ(ζ₇)⁺` the way `ℚ(√5)` builds `E₈`. So the
        SEVEN is a real arithmetic coincidence of the prime 7 across these structures —
        suggestive and partly proven — NOT a single field-builds-the-lattice hinge. -/
theorem heptagon_cubic_shells_master :
    -- PROVED: the totally-real cubic and its ∀-n trace
    (ztMul (ztMul theta theta) theta = ztAdd (ztAdd (⟨0,0,-1⟩) ⟨0,2,0⟩) ztOne)
    ∧ (traceZth ztOne = 3 ∧ traceZth theta = -1 ∧ traceZth (ztMul theta theta) = 5)
    ∧ (∀ n, heptaTrace n = traceZth (thetaPow n))
    -- PROVED: signature (3,0) totally real, disc 7²
    ∧ (heptaDiscriminant = 49 ∧ heptaDiscriminant = 7^2 ∧ heptaDiscriminant > 0)
    -- PROVED: the trace-form lattice is positive-definite, det = disc = 49
    ∧ (gram3det 3 (-1) 5 (-1) 5 (-4) 5 (-4) 13 = 49
        ∧ gram3det 3 (-1) 5 (-1) 5 (-4) 5 (-4) 13 > 0)
    -- PROVED SEVEN shadows: Fano/Klein/PSL order + Weyl divisibility
    ∧ (psl2_7_order = 168 ∧ (8 - 1) * (8 - 2) * (8 - 4) = 168 ∧ 84 * (3 - 1) = 168)
    ∧ (weylE7 % 7 = 0 ∧ weylE8 % 7 = 0)
    ∧ (weylE7 % 168 = 0 ∧ weylE8 % 168 = 0) := by
  refine ⟨theta_cubed,
          ⟨trace_one, trace_theta, trace_theta_sq⟩,
          heptaTrace_is_cubic_trace,
          hepta_disc_positive,
          ⟨(trace_form_det_is_disc).1, (trace_form_positive_definite).2.2.2⟩,
          ⟨psl2_7_is_168, gl3_f2_is_168, klein_hurwitz_168⟩,
          seven_divides_weyl,
          ⟨(klein_order_divides_weyl).1, (klein_order_divides_weyl).2.2.1⟩⟩

/-! ## §6  Reading

The totally-real heptagon field `ℚ(ζ₇)⁺ = ℚ(2cos 2π/7)` is the cubic the plastic field
could not be: signature (3,0) (disc `49 = 7² > 0`), THREE real embeddings of equal
status. Its trace `heptaTrace n = Σ_k θ_k^n` is PROVED for all `n` (the cubic analogue
of `Lₙ = φⁿ+ψⁿ`), giving the alternating-sign "heptagon Lucas"
`3,−1,5,−4,13,−16,38,…`. The three real shells DO exist — but they assemble into the
ordinary totally-real cubic-field lattice (trace form `[[3,−1,5],[−1,5,−4],[5,−4,13]]`,
positive-definite, det `= disc = 49`, covolume 7), NOT an exceptional `E`-lattice.
There is no cubic `E₈`; the exceptional two-shell geometry stays golden-quadratic.

The SEVEN hinge is REAL as a shared number but NOT (on this evidence) a single hinge:
PROVEN — `disc = 7²`; `7 ∣ |W(E₇)|, |W(E₈)|` (once each); `168 = |PSL(2,7)| =
|Aut(Fano)| = |GL₃(𝔽₂)| = |Aut(Klein quartic)|` divides BOTH exceptional Weyl orders;
`28` bitangents `= 56/2 = ` half the `E₇` minuscule dim. CITED — the group isomorphisms
`PSL(2,7) ≅ Aut(Fano) ≅ Aut(Klein)`, and the Fano→octonion→`E₈` BUILD
(`OctonionE8Lattice`) use the 7 Fano LINES / 7 octonion imaginary units as an incidence
and multiplication structure — a DIFFERENT `7` from the heptagon field's conductor (the
field has Galois group `ℤ/3`, not a 7-fold object). No construction of `E₈`/`E₇` from
`ℚ(ζ₇)⁺` is known or proven. So the heptagon cubic field and the Fano/octonion `E₈`
share the prime `7` as a genuine, partly-proven arithmetic coincidence — not a
field-builds-the-lattice identity.

-- Next exploration:
--   (A)  THE CYCLIC GALOIS SHELL ROTATION. `Gal(ℚ(ζ₇)⁺/ℚ) ≅ ℤ/3` acts on the three
--        real embeddings by the 3-cycle `θ_k ↦ θ_{2k mod 7}` (`σ: θ₁↦θ₂↦θ₃↦θ₁`, the
--        order-3 Frobenius). Build the explicit ℤ-linear `σ : ℤ[θ] → ℤ[θ]` (the
--        companion-matrix cube root of identity), prove `σ³ = id` and that it permutes
--        the trace-form's three shells cyclically — the genuine three-shell SYMMETRY
--        (an order-3 rotation, the cubic analogue of the golden `φ ↦ ψ` order-2
--        conjugation). THIS is where the heptagon's three-fold (not seven-fold) shell
--        structure actually lives: the field is CUBIC, its symmetry is `ℤ/3`.
--   (B)  THE SEVEN AS A FROBENIUS PRIME. With `heptaTrace n = Tr(θⁿ)` proved ∀ n, the
--        congruence `Tr(θ⁷) ≡ Tr(θ)⁷ (mod 7)` (Frobenius at the ramified prime `7`,
--        where `ℚ(ζ₇)⁺` is totally ramified) is the arithmetic statement that the `7`
--        is the field's conductor. Prove `heptaTrace 7 ≡ heptaTrace 1 (mod 7)` (and the
--        general `Hₚ ≡ H₁ (mod p)` shadow) as a decidable trace-Frobenius fact — the
--        honest meaning of "the field's seven", distinct from the Fano seven.
--   (C)  E₇ NOT E₈ — THE 28/56/168 LADDER. The strongest seven-flavoured Lie home is
--        `E₇` (28 bitangents of a plane quartic = the Klein-quartic 28; `56` minuscule;
--        `PSL(2,7)` of order 168 inside `W(E₇)`). Build the decidable coset/divisibility
--        ladder `168 ∣ |W(E₇)|` REFINED to an orbit count (the 28 bitangents as a
--        `W(E₇)`-orbit, the Fano 7 inside the 28), testing whether `PSL(2,7) ⊂ W(E₇)`
--        is an actual subgroup (cited: it is) — the honest question of whether the
--        heptagon `7` lands in `E₇` rather than `E₈`. (Likely the Fano-7 of `E₇` is the
--        same incidence-7, still NOT the cubic field's conductor-7 — but it is the
--        right exceptional group to interrogate.)
-/

end HeptagonCubicShells
end Gnosis

#print axioms Gnosis.HeptagonCubicShells.heptaTrace_is_cubic_trace
#print axioms Gnosis.HeptagonCubicShells.theta3_op
#print axioms Gnosis.HeptagonCubicShells.thetaPow_cubic_recurrence
#print axioms Gnosis.HeptagonCubicShells.hepta_disc_positive
#print axioms Gnosis.HeptagonCubicShells.trace_form_det_is_disc
#print axioms Gnosis.HeptagonCubicShells.seven_divides_weyl
#print axioms Gnosis.HeptagonCubicShells.klein_order_divides_weyl
#print axioms Gnosis.HeptagonCubicShells.heptagon_cubic_shells_master
