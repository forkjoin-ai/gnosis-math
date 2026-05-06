import Init

/-!
# Determinant Anomaly Unified: Cassini Across Recurrence Families

This module witnesses a structural synthesis across three peer modules:

* `CFCobordismPartition.lean` — the continued-fraction step matrix
  `M_a = ⟨⟨0, 1⟩, ⟨1, a⟩⟩` with `det M_a = -1`, and the
  `cassini_det_phi_*` / `cassini_det_sqrt2_*` witnesses showing the
  tower determinant equals `(-1)^n`.
* `PellCatLucasTraceFamily.lean` — the two-parameter trace recurrence
  `t_{k+2} = s · t_{k+1} - d · t_k` with `(s, d) = (tr A, det A)`, the
  named matrices `fibF`, `catA`, `pellP`, and the discriminant
  classification `s² - 4d`.
* `FibLucasExtendedIdentities.lean` — the scalar Cassini identities
  `F_{n-1} · F_{n+1} - F_n² = (-1)^n` (Fibonacci) and
  `L_{n-1} · L_{n+1} - L_n² = ±5` (Lucas).

## The bridge

Each classical recurrence family (Fibonacci, Lucas, Pell, and the CF
tower) carries a step matrix whose determinant is a ±1 integer. When
several step matrices are composed, the determinant of the composite
equals the product of determinants. Reading this product as a Z-valued
anomaly coefficient attached to the composition, the Cassini constant
of a family computes to the `n`-fold product of the single-step
determinant.

The unified statement: for any list `[M_0, M_1, …, M_{n-1}]` of 2×2
integer matrices,

    det (M_0 · M_1 · … · M_{n-1}) = det M_0 · det M_1 · … · det M_{n-1}.

This file does not prove that identity in full generality (the general
multiplicativity of `det` on `Mat2` would need a polynomial-ring
computation outside the kernel-`decide` budget). Instead it witnesses
the identity pointwise on short towers across four families and closes
the Cassini-as-product-of-determinants correspondence at low depths.

## What this module witnesses

1. `Mat2` + `matMul` + `det` + `matPow` inlined on `Int`.
2. Step matrices for each family: `fibStep`, `pellStep`, `cfStep a`.
   (Lucas reuses `fibStep`: both are `[[1,1],[1,0]]` up to transpose,
   arising from `s = 1, d = -1`; Lucas differs from Fibonacci only in
   initial conditions.) Determinants closed at kernel.
3. Multiplicativity witness (pointwise): `det (matMul A B) = det A · det B`
   checked for three explicit pairs `(fibStep, fibStep)`,
   `(pellStep, pellStep)`, `(cfStep 2, cfStep 3)`.
4. Tower determinant witnesses: `det (matPow step n) = (det step)^n`
   checked at `n = 0..5` for `fibStep` and `pellStep`, and at `n = 0..4`
   for `cfStep 2` and `cfStep 3`.
5. Cassini-as-tower-determinant for each family:
   - Fibonacci: `fibStep^n` has determinant `(-1)^n`, which equals
     `F_{n+1} · F_{n-1} - F_n²` (the Cassini form read off the matrix
     entries; witnessed at `n = 2, 3, 4, 5`).
   - Pell: `pellStep^n` has determinant `(-1)^n`, witnessed at `n = 2..5`.
   - CF: `cfStep a ∘ cfStep b ∘ …` has determinant `(-1)^n` for any
     `a, b, …`, witnessed at several mixed sequences.
6. Anomaly list / parity bridge: `towerAnomaly : List Mat2 → Int`
   folds `det` across a list. Cassini sign equals anomaly parity:
   even count of `det = -1` step matrices yields `+1`, odd yields `-1`.
7. Cross-family composition: `det (matMul fibStep pellStep) = 1 = (-1) · (-1)`,
   witnessing that different family towers multiply anomaly-coefficients
   in the same ring. No new phenomenon arises — the product is exactly
   what multiplicativity predicts.

## What is *not* witnessed

- No general theorem `∀ A B : Mat2, det (matMul A B) = det A · det B`.
  This would require explicit polynomial identity checking on `Int`,
  which kernel `decide` handles only on closed ground terms.
- No connection to actual topological anomaly cancellation in the sense
  of characteristic classes, 't Hooft anomalies, or the Atiyah–Singer
  index theorem. The word "anomaly" here names the `Z`-valued
  composition-invariant of a tower, not a Chern-class computation.
- No claim that this recovers the full 2D TQFT. As in
  `CFCobordismPartition.lean`, the correspondence operates at the level
  of rank-2 `Z`-linear maps.
- No Binet formula, no eigen-decomposition, no spectral argument. The
  Cassini equality is read off at each fixed `n` by the kernel.

No `sorry`, no new `axiom`. `import Init` only. Every numerical item
closes by kernel `decide`.
-/

namespace Gnosis
namespace DeterminantAnomalyUnified

/-! ## `Mat2`: inline 2×2 integer matrix

Self-contained to avoid importing the peer modules. Matches the
structure used in `CFCobordismPartition.lean` and
`PellCatLucasTraceFamily.lean`, with entries `a b c d` laid out as

    ⟨⟨a, b⟩,
     ⟨c, d⟩⟩.
-/

/-- A 2×2 integer matrix with entries `a b` (top row) and `c d` (bottom row). -/
structure Mat2 where
  /-- Top-left entry. -/
  a : Int
  /-- Top-right entry. -/
  b : Int
  /-- Bottom-left entry. -/
  c : Int
  /-- Bottom-right entry. -/
  d : Int
deriving DecidableEq, Repr

/-- Matrix multiplication on `Mat2`. -/
def matMul (P Q : Mat2) : Mat2 :=
  { a := P.a * Q.a + P.b * Q.c
  , b := P.a * Q.b + P.b * Q.d
  , c := P.c * Q.a + P.d * Q.c
  , d := P.c * Q.b + P.d * Q.d }

/-- The 2×2 identity. -/
def matId : Mat2 := { a := 1, b := 0, c := 0, d := 1 }

/-- `n`-fold power `M^n = M · M · … · M` (identity when `n = 0`). -/
def matPow (M : Mat2) : Nat → Mat2
  | 0     => matId
  | k + 1 => matMul M (matPow M k)

/-- Determinant of a 2×2 matrix: `a · d - b · c`. -/
def det (P : Mat2) : Int := P.a * P.d - P.b * P.c

/-! ## Step matrices for each family

The Fibonacci / Lucas step matrix `[[1, 1], [1, 0]]` arises from the
recurrence `t_{k+2} = t_{k+1} + t_k` (parameters `s = 1, d = -1` in the
trace family of `PellCatLucasTraceFamily.lean`). The Lucas sequence
reuses the same matrix — only its initial conditions differ from
Fibonacci — so `lucasStep := fibStep` is the honest identification.

The Pell step matrix `[[2, 1], [1, 0]]` implements
`t_{k+2} = 2 · t_{k+1} + t_k` (parameters `s = 2, d = -1`).

The CF step matrix `[[a, 1], [1, 0]]` implements
`p_n = a · p_{n-1} + p_{n-2}` with partial quotient `a`. Its determinant
is `-1` for every `a : Int`.
-/

/-- Fibonacci / Lucas step matrix `[[1, 1], [1, 0]]`. -/
def fibStep : Mat2 := { a := 1, b := 1, c := 1, d := 0 }

/-- Lucas reuses the Fibonacci step matrix (same recurrence, different
seeds). -/
def lucasStep : Mat2 := fibStep

/-- Pell step matrix `[[2, 1], [1, 0]]`. -/
def pellStep : Mat2 := { a := 2, b := 1, c := 1, d := 0 }

/-- CF step matrix `[[a, 1], [1, 0]]` for partial quotient `a`. -/
def cfStep (a : Int) : Mat2 := { a := a, b := 1, c := 1, d := 0 }

/-! ## Step-matrix determinants

Each family's step matrix has `det = -1`. (Lucas same as Fibonacci.)
-/

/-- `det fibStep = -1`. -/
theorem det_fibStep : det fibStep = -1 := by decide

/-- `det lucasStep = -1` (identical to `det fibStep`). -/
theorem det_lucasStep : det lucasStep = -1 := by decide

/-- `det pellStep = -1`. -/
theorem det_pellStep : det pellStep = -1 := by decide

/-- `det (cfStep 0) = -1`. -/
theorem det_cfStep_0 : det (cfStep 0) = -1 := by decide

/-- `det (cfStep 1) = -1`. -/
theorem det_cfStep_1 : det (cfStep 1) = -1 := by decide

/-- `det (cfStep 2) = -1`. -/
theorem det_cfStep_2 : det (cfStep 2) = -1 := by decide

/-- `det (cfStep 3) = -1`. -/
theorem det_cfStep_3 : det (cfStep 3) = -1 := by decide

/-- `det (cfStep 7) = -1`. -/
theorem det_cfStep_7 : det (cfStep 7) = -1 := by decide

/-- `det (cfStep (-4)) = -1`: negative partial quotient still `-1`. -/
theorem det_cfStep_neg4 : det (cfStep (-4)) = -1 := by decide

/-! ## Pointwise multiplicativity witnesses

For three explicit pairs we check `det (matMul A B) = det A · det B`.
This is not the general theorem — it is the instantiation at specific
step matrices. Each row computes by ground kernel reduction.
-/

/-- `det (fibStep · fibStep) = det fibStep · det fibStep = 1`. -/
theorem det_mul_fib_fib :
    det (matMul fibStep fibStep) = det fibStep * det fibStep := by decide

/-- `det (pellStep · pellStep) = det pellStep · det pellStep = 1`. -/
theorem det_mul_pell_pell :
    det (matMul pellStep pellStep) = det pellStep * det pellStep := by decide

/-- `det (cfStep 2 · cfStep 3) = det (cfStep 2) · det (cfStep 3) = 1`. -/
theorem det_mul_cf2_cf3 :
    det (matMul (cfStep 2) (cfStep 3)) = det (cfStep 2) * det (cfStep 3) := by decide

/-- Cross-family pointwise multiplicativity: `fibStep · pellStep`. -/
theorem det_mul_fib_pell :
    det (matMul fibStep pellStep) = det fibStep * det pellStep := by decide

/-- Cross-family pointwise multiplicativity: `pellStep · cfStep 5`. -/
theorem det_mul_pell_cf5 :
    det (matMul pellStep (cfStep 5)) = det pellStep * det (cfStep 5) := by decide

/-! ## Tower determinant: `det (matPow step n) = (det step)^n = (-1)^n`

For each single-family step matrix the `n`-fold product has
determinant `(-1)^n`. Witnessed at small `n`.
-/

/-- `det (matPow fibStep 0) = 1`. -/
theorem det_fibPow_0 : det (matPow fibStep 0) = 1 := by decide

/-- `det (matPow fibStep 1) = -1`. -/
theorem det_fibPow_1 : det (matPow fibStep 1) = -1 := by decide

/-- `det (matPow fibStep 2) = 1`. -/
theorem det_fibPow_2 : det (matPow fibStep 2) = 1 := by decide

/-- `det (matPow fibStep 3) = -1`. -/
theorem det_fibPow_3 : det (matPow fibStep 3) = -1 := by decide

/-- `det (matPow fibStep 4) = 1`. -/
theorem det_fibPow_4 : det (matPow fibStep 4) = 1 := by decide

/-- `det (matPow fibStep 5) = -1`. -/
theorem det_fibPow_5 : det (matPow fibStep 5) = -1 := by decide

/-- `det (matPow pellStep 0) = 1`. -/
theorem det_pellPow_0 : det (matPow pellStep 0) = 1 := by decide

/-- `det (matPow pellStep 1) = -1`. -/
theorem det_pellPow_1 : det (matPow pellStep 1) = -1 := by decide

/-- `det (matPow pellStep 2) = 1`. -/
theorem det_pellPow_2 : det (matPow pellStep 2) = 1 := by decide

/-- `det (matPow pellStep 3) = -1`. -/
theorem det_pellPow_3 : det (matPow pellStep 3) = -1 := by decide

/-- `det (matPow pellStep 4) = 1`. -/
theorem det_pellPow_4 : det (matPow pellStep 4) = 1 := by decide

/-- `det (matPow pellStep 5) = -1`. -/
theorem det_pellPow_5 : det (matPow pellStep 5) = -1 := by decide

/-- `det (matPow (cfStep 2) 0) = 1`. -/
theorem det_cf2Pow_0 : det (matPow (cfStep 2) 0) = 1 := by decide

/-- `det (matPow (cfStep 2) 1) = -1`. -/
theorem det_cf2Pow_1 : det (matPow (cfStep 2) 1) = -1 := by decide

/-- `det (matPow (cfStep 2) 2) = 1`. -/
theorem det_cf2Pow_2 : det (matPow (cfStep 2) 2) = 1 := by decide

/-- `det (matPow (cfStep 2) 3) = -1`. -/
theorem det_cf2Pow_3 : det (matPow (cfStep 2) 3) = -1 := by decide

/-- `det (matPow (cfStep 2) 4) = 1`. -/
theorem det_cf2Pow_4 : det (matPow (cfStep 2) 4) = 1 := by decide

/-- `det (matPow (cfStep 3) 0) = 1`. -/
theorem det_cf3Pow_0 : det (matPow (cfStep 3) 0) = 1 := by decide

/-- `det (matPow (cfStep 3) 1) = -1`. -/
theorem det_cf3Pow_1 : det (matPow (cfStep 3) 1) = -1 := by decide

/-- `det (matPow (cfStep 3) 2) = 1`. -/
theorem det_cf3Pow_2 : det (matPow (cfStep 3) 2) = 1 := by decide

/-- `det (matPow (cfStep 3) 3) = -1`. -/
theorem det_cf3Pow_3 : det (matPow (cfStep 3) 3) = -1 := by decide

/-- `det (matPow (cfStep 3) 4) = 1`. -/
theorem det_cf3Pow_4 : det (matPow (cfStep 3) 4) = 1 := by decide

/-! ## Cassini-as-tower-determinant

For `fibStep = [[1,1],[1,0]]`, induction gives
`fibStep^n = [[F_{n+1}, F_n], [F_n, F_{n-1}]]` (with `F_{-1} = 1`),
so `det (fibStep^n) = F_{n+1} · F_{n-1} - F_n²`. Kernel reduction at
each fixed `n` computes `det (matPow fibStep n)` directly and reports
`(-1)^n`, which equals the Cassini quantity.

We witness the Cassini form by reading off `F_{n+1}, F_n, F_{n-1}` from
the matrix entries and showing the explicit equality at `n = 2..5`.
-/

/-- At `n = 2`: `fibStep^2 = [[2, 1], [1, 1]]`, so the Cassini form is
`2 · 1 - 1 · 1 = 1 = (-1)^2`. -/
theorem fib_cassini_det_2 :
    (matPow fibStep 2).a * (matPow fibStep 2).d
      - (matPow fibStep 2).b * (matPow fibStep 2).c = 1 := by decide

/-- At `n = 3`: Cassini form `3 · 1 - 2 · 2 = -1 = (-1)^3`. -/
theorem fib_cassini_det_3 :
    (matPow fibStep 3).a * (matPow fibStep 3).d
      - (matPow fibStep 3).b * (matPow fibStep 3).c = -1 := by decide

/-- At `n = 4`: Cassini form `5 · 2 - 3 · 3 = 1 = (-1)^4`. -/
theorem fib_cassini_det_4 :
    (matPow fibStep 4).a * (matPow fibStep 4).d
      - (matPow fibStep 4).b * (matPow fibStep 4).c = 1 := by decide

/-- At `n = 5`: Cassini form `8 · 3 - 5 · 5 = -1 = (-1)^5`. -/
theorem fib_cassini_det_5 :
    (matPow fibStep 5).a * (matPow fibStep 5).d
      - (matPow fibStep 5).b * (matPow fibStep 5).c = -1 := by decide

/-- Pell Cassini at `n = 2`: `det (pellStep^2) = 1`. -/
theorem pell_cassini_det_2 :
    (matPow pellStep 2).a * (matPow pellStep 2).d
      - (matPow pellStep 2).b * (matPow pellStep 2).c = 1 := by decide

/-- Pell Cassini at `n = 3`: `det (pellStep^3) = -1`. -/
theorem pell_cassini_det_3 :
    (matPow pellStep 3).a * (matPow pellStep 3).d
      - (matPow pellStep 3).b * (matPow pellStep 3).c = -1 := by decide

/-- Pell Cassini at `n = 4`: `det (pellStep^4) = 1`. -/
theorem pell_cassini_det_4 :
    (matPow pellStep 4).a * (matPow pellStep 4).d
      - (matPow pellStep 4).b * (matPow pellStep 4).c = 1 := by decide

/-- Pell Cassini at `n = 5`: `det (pellStep^5) = -1`. -/
theorem pell_cassini_det_5 :
    (matPow pellStep 5).a * (matPow pellStep 5).d
      - (matPow pellStep 5).b * (matPow pellStep 5).c = -1 := by decide

/-! ## CF mixed-sequence towers

`cfStep a_0 · cfStep a_1 · … · cfStep a_{n-1}` has determinant
`(-1)^n` for any `a_i`. We witness three mixed sequences. -/

/-- `cfTowerProduct as` folds `matMul` across a list of CF step
matrices, starting from the identity on the right. -/
def cfTowerProduct : List Int → Mat2
  | []      => matId
  | a :: as => matMul (cfStep a) (cfTowerProduct as)

/-- Mixed CF tower at length 3: `[1, 2, 3]` has determinant `-1`. -/
theorem cf_mixed_det_3 :
    det (cfTowerProduct [1, 2, 3]) = -1 := by decide

/-- Mixed CF tower at length 4: `[1, 2, 3, 4]` has determinant `1`. -/
theorem cf_mixed_det_4 :
    det (cfTowerProduct [1, 2, 3, 4]) = 1 := by decide

/-- Mixed CF tower at length 5: `[2, 1, 1, 4, 2]` has determinant `-1`. -/
theorem cf_mixed_det_5 :
    det (cfTowerProduct [2, 1, 1, 4, 2]) = -1 := by decide

/-! ## Tower anomaly

`towerAnomaly` folds `det` across a list of matrices, recording the
`Z`-valued composition invariant of a tower. For a tower whose step
matrices all have determinant `-1`, the anomaly is `(-1)^n` — exactly
the Cassini sign pattern. Even parity of `-1` factors yields `+1`; odd
parity yields `-1`.
-/

/-- Product of determinants across a list of 2×2 matrices. -/
def towerAnomaly : List Mat2 → Int
  | []      => 1
  | M :: Ms => det M * towerAnomaly Ms

/-- Even count of `fibStep`s yields anomaly `+1`. -/
theorem towerAnomaly_fib_even :
    towerAnomaly [fibStep, fibStep, fibStep, fibStep] = 1 := by decide

/-- Odd count of `fibStep`s yields anomaly `-1`. -/
theorem towerAnomaly_fib_odd :
    towerAnomaly [fibStep, fibStep, fibStep] = -1 := by decide

/-- Even count of `pellStep`s yields anomaly `+1`. -/
theorem towerAnomaly_pell_even :
    towerAnomaly [pellStep, pellStep] = 1 := by decide

/-- Odd count of `pellStep`s yields anomaly `-1`. -/
theorem towerAnomaly_pell_odd :
    towerAnomaly [pellStep, pellStep, pellStep, pellStep, pellStep] = -1 := by decide

/-- Mixed CF anomaly of length 4 is `+1`. -/
theorem towerAnomaly_cf_mixed_even :
    towerAnomaly [cfStep 1, cfStep 2, cfStep 3, cfStep 4] = 1 := by decide

/-- Mixed CF anomaly of length 3 is `-1`. -/
theorem towerAnomaly_cf_mixed_odd :
    towerAnomaly [cfStep 2, cfStep 7, cfStep (-1)] = -1 := by decide

/-! ## Cross-family composition

A tower whose step matrices come from different families (Fibonacci,
Pell, and CF) still has anomaly `= ∏ det M_i`. The product is what
multiplicativity predicts — no novel coupling emerges. The observation
here is the *uniformity*: the same `Z`-valued invariant governs
every recurrence family listed in the peer modules.
-/

/-- Two-matrix cross-family composition `fibStep · pellStep`. -/
theorem cross_det_fib_pell :
    det (matMul fibStep pellStep) = det fibStep * det pellStep := by decide

/-- Three-matrix cross-family composition `fibStep · pellStep · cfStep 3`. -/
theorem cross_det_fib_pell_cf3 :
    det (matMul fibStep (matMul pellStep (cfStep 3)))
      = det fibStep * det pellStep * det (cfStep 3) := by decide

/-- Four-matrix cross-family tower anomaly. -/
theorem cross_anomaly_four :
    towerAnomaly [fibStep, pellStep, cfStep 2, cfStep 5] = 1 := by decide

/-- Five-matrix cross-family tower anomaly. -/
theorem cross_anomaly_five :
    towerAnomaly [fibStep, pellStep, cfStep 2, cfStep 5, fibStep] = -1 := by decide

/-- `fibStep · pellStep` and `pellStep · fibStep` have the same
determinant despite non-commutation. Multiplicativity of the anomaly
is commutative even when matrix multiplication is not. -/
theorem det_commutes_across_families :
    det (matMul fibStep pellStep) = det (matMul pellStep fibStep) := by decide

/-! ## Aggregate witness

A single decidable bundle tying together the bridge: each family's
step matrix has `det = -1`; multiplicativity closes at the step level;
tower parity matches Cassini sign.
-/

/-- Aggregate determinant-anomaly bridge witness. -/
theorem determinant_anomaly_unified_witness :
    det fibStep = -1 ∧
    det pellStep = -1 ∧
    det (cfStep 2) = -1 ∧
    det (matMul fibStep fibStep) = det fibStep * det fibStep ∧
    det (matMul pellStep pellStep) = det pellStep * det pellStep ∧
    det (matMul fibStep pellStep) = det fibStep * det pellStep ∧
    det (matPow fibStep 4) = 1 ∧
    det (matPow pellStep 5) = -1 ∧
    towerAnomaly [fibStep, fibStep, fibStep, fibStep] = 1 ∧
    towerAnomaly [fibStep, pellStep, cfStep 2, cfStep 5, fibStep] = -1 := by
  decide

end DeterminantAnomalyUnified
end Gnosis
