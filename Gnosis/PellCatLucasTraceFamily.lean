import Init

/-!
# A Two-Parameter SL(2, ℤ) Trace Family: Fibonacci / Lucas / Cat / Pell

For any `2 × 2` integer matrix `A` with `tr(A) = s` and `det(A) = d`, the
Cayley–Hamilton theorem applied to `A` gives `A² = s · A - d · I`.
Multiplying by `A^k` and taking the trace yields the two-parameter linear
recurrence

    t_{k+2} = s · t_{k+1} - d · t_k

for the trace sequence `t_k := tr(A^k)`, with the arithmetic initial
conditions `t_0 = tr(I) = 2` and `t_1 = tr(A) = s`. Different choices of
`(s, d)` pick out different classical Lucas-type sequences:

| Matrix `A`              | `s = tr A` | `d = det A` | Sequence name                                   |
|-------------------------|-----------:|------------:|-------------------------------------------------|
| `[[1,1],[1,0]]` (Fib)   |        `1` |        `-1` | Lucas numbers `L_k` (initial `2, 1`)            |
| `[[2,1],[1,1]]` (Cat)   |        `3` |         `1` | Cat-trace `2, 3, 7, 18, 47, 123, 322, 843, …`   |
| `[[1,2],[1,1]]` (Pell)  |        `2` |        `-1` | Pell companion `2, 2, 6, 14, 34, 82, 198, 478`  |
| `[[3,1],[1,1]] = F³`    |        `4` |         `2` | Unnamed: `t_{k+2} = 4 t_{k+1} - 2 t_k`          |
| `[[1,1],[2,1]]`         |        `2` |        `-1` | Conjugate of Pell (same recurrence)             |

The key definition below is `genTrace (s d t₀ t₁ : Int) : Nat → Int`, the
two-parameter recurrence with user-supplied initial conditions. Each
classical sequence is realized as `genTrace s d 2 s k` (with `t₀ = 2` and
`t₁ = s` matching `tr(I)` and `tr(A)`).

## What this module witnesses

1. Generalized recurrence `genTrace : Int → Int → Int → Int → Nat → Int`.
2. Specialization tables for Lucas `(s, d) = (1, -1)`, cat-trace
   `(3, 1)`, Pell-companion `(2, -1)`, and the new `F³` instance `(4, 2)`,
   each checked at `k = 0, ..., 7`.
3. Matrix realization on `Int`-valued `2 × 2` matrices: `Mat2`,
   `matMul`, `matId`, `matPow`, `trace`, `det`. For each of the three
   named matrices `fibF`, `catA`, `pellP`, the equality
   `trace (matPow A k) = genTrace (trace A) (det A) 2 (trace A) k`
   is witnessed at `k = 2, 3, 4` (and `k = 0, 1` trivially).
4. Trace-pair mod-period certificates: `(t_k, t_{k+1}) mod 5` is
   periodic in `k`, with period dividing the cited bound.
   - Cat `(3, 1)`: divides `10` (`ord(A_cat, 5) = 10`).
   - Lucas `(1, -1)`: divides `20` (Pisano period `π(5) = 20`).
   - Pell `(2, -1)`: divides `12`.
   Each certificate is a single `decide` on the pair equality at the
   nominal period.
5. Cassini-analogue for the generalized recurrence:
   `t_{k-1} · t_{k+1} - t_k² = D_k`, where `D_k = -d^{k-1} · (s² - 4 d)`
   up to initial data. Concretely:
   - Lucas `d = -1`: `D_k = (-1)^k · 5` (sign alternates).
   - Cat-trace `d = 1`: `D_k = 5` constant.
   Verified at `k = 1, 2, 3, 4` for both.
6. Discriminant classification `discriminant s d := s² - 4 d`:
   - Fib `(1, -1)`: `1 - 4·(-1) = 5`.
   - Cat `(3, 1)`: `9 - 4 = 5`.
   - Pell `(2, -1)`: `4 - 4·(-1) = 8`.
   Fib and Cat realize the same discriminant `5` (both live in the ring
   `ℤ[(1+√5)/2]` up to scaling). Pell sits in `ℤ[√2]` via discriminant
   `8 = 4·2`.

## What this module does *not* claim

- No general `∀ k, trace (matPow A k) = genTrace (trace A) (det A) 2 (trace A) k`
  proof is produced. The identity is witnessed at finitely many `k` by
  kernel reduction. A full proof would require an inductive Cayley–Hamilton
  argument on `Int`-valued matrices, which is outside the `Init`-only
  scope of this module.
- The three matrix families `fibF`, `catA`, `pellP` are only a thin slice
  of `SL(2, ℤ)`. Nothing here witnesses the recurrence for an arbitrary
  `2 × 2` integer matrix.
- The discriminant classification is at the *formula level*: it records
  `s² - 4 d` and observes numerical coincidences. No minimal-polynomial
  or splitting-field argument over `ℤ` is carried out.
- The trace-pair period certificates verify the *necessary* matching of
  `(t_k, t_{k+1}) mod n` at the nominal period. They do not produce the
  converse — matrix identity from trace-pair match — which would require
  Cayley–Hamilton's uniqueness of the second-order recurrence from two
  consecutive values.

No `sorry`, no new `axiom`, `Init`-only. Each numerical item closes by
kernel `decide`; `maxRecDepth` is raised locally for the matrix-power
unfoldings where needed.
-/

namespace Gnosis
namespace PellCatLucasTraceFamily

/-! ## Generalized trace recurrence

`genTrace s d t₀ t₁ k` computes the `k`-th term of the two-parameter
linear recurrence `t_{k+2} = s · t_{k+1} - d · t_k` starting from
`(t₀, t₁)`. Entirely in `Int`. -/

/-- Two-parameter Lucas-type trace recurrence indexed by
`(s, d) = (tr A, det A)` with user-supplied initial conditions. -/
def genTrace (s d t₀ t₁ : Int) : Nat → Int
  | 0     => t₀
  | 1     => t₁
  | k + 2 => s * genTrace s d t₀ t₁ (k + 1) - d * genTrace s d t₀ t₁ k

/-! ## Specialization: Lucas numbers `(s, d) = (1, -1)`

`genTrace 1 (-1) 2 1 k` is the standard Lucas sequence
`2, 1, 3, 4, 7, 11, 18, 29, ...`. -/

/-- Specialization: `lucasViaGen k = genTrace 1 (-1) 2 1 k`. -/
def lucasViaGen (k : Nat) : Int := genTrace 1 (-1) 2 1 k

/-- First eight Lucas values via the generalized recurrence. -/
theorem lucasViaGen_table :
    lucasViaGen 0 = 2   ∧ lucasViaGen 1 = 1   ∧
    lucasViaGen 2 = 3   ∧ lucasViaGen 3 = 4   ∧
    lucasViaGen 4 = 7   ∧ lucasViaGen 5 = 11  ∧
    lucasViaGen 6 = 18  ∧ lucasViaGen 7 = 29  := by decide

/-! ## Specialization: cat-trace `(s, d) = (3, 1)`

`genTrace 3 1 2 3 k` is the Arnold cat-map trace sequence
`2, 3, 7, 18, 47, 123, 322, 843`. Matches `catTrace` in
`CatMapLucasBridge.lean` and `traceCatPow` in `ArnoldCatMapOrder5.lean`. -/

/-- Specialization: `catTraceViaGen k = genTrace 3 1 2 3 k`. -/
def catTraceViaGen (k : Nat) : Int := genTrace 3 1 2 3 k

/-- First eight cat-trace values via the generalized recurrence. -/
theorem catTraceViaGen_table :
    catTraceViaGen 0 = 2    ∧ catTraceViaGen 1 = 3    ∧
    catTraceViaGen 2 = 7    ∧ catTraceViaGen 3 = 18   ∧
    catTraceViaGen 4 = 47   ∧ catTraceViaGen 5 = 123  ∧
    catTraceViaGen 6 = 322  ∧ catTraceViaGen 7 = 843  := by decide

/-! ## Specialization: Pell-companion trace `(s, d) = (2, -1)`

`genTrace 2 (-1) 2 2 k` is the Pell companion sequence
`2, 2, 6, 14, 34, 82, 198, 478`. This is `tr(P^k)` for
`P = [[1, 2], [1, 1]]`. -/

/-- Specialization: `pellCompanionViaGen k = genTrace 2 (-1) 2 2 k`. -/
def pellCompanionViaGen (k : Nat) : Int := genTrace 2 (-1) 2 2 k

/-- First eight Pell-companion trace values via the generalized recurrence. -/
theorem pellCompanionViaGen_table :
    pellCompanionViaGen 0 = 2    ∧ pellCompanionViaGen 1 = 2    ∧
    pellCompanionViaGen 2 = 6    ∧ pellCompanionViaGen 3 = 14   ∧
    pellCompanionViaGen 4 = 34   ∧ pellCompanionViaGen 5 = 82   ∧
    pellCompanionViaGen 6 = 198  ∧ pellCompanionViaGen 7 = 478  := by decide

/-! ## Specialization: `F³` trace `(s, d) = (4, 2)` — new instance

For `A = F³ = [[3, 1], [1, 1]]` we have `tr(A) = 4`, `det(A) = 2`. The
recurrence `t_{k+2} = 4 t_{k+1} - 2 t_k` with `t_0 = 2, t_1 = 4` gives
`2, 4, 12, 40, 136, 464, 1584, 5408`. No standard name; recorded here as
a fourth instance of the generalized family. -/

/-- Specialization: `fibCubedTraceViaGen k = genTrace 4 2 2 4 k`. -/
def fibCubedTraceViaGen (k : Nat) : Int := genTrace 4 2 2 4 k

/-- First eight `F³`-trace values via the generalized recurrence. -/
theorem fibCubedTraceViaGen_table :
    fibCubedTraceViaGen 0 = 2     ∧ fibCubedTraceViaGen 1 = 4     ∧
    fibCubedTraceViaGen 2 = 12    ∧ fibCubedTraceViaGen 3 = 40    ∧
    fibCubedTraceViaGen 4 = 136   ∧ fibCubedTraceViaGen 5 = 464   ∧
    fibCubedTraceViaGen 6 = 1584  ∧ fibCubedTraceViaGen 7 = 5408  := by decide

/-! ## Int-valued `2 × 2` matrix algebra

Minimal structure for computing `trace (A^k)` and `det A` directly in
`Int`. -/

/-- A `2 × 2` matrix over `Int`, entries `a, b, c, d` in row-major
order `[[a, b], [c, d]]`. -/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

/-- Matrix multiplication on `Mat2`. -/
def matMul (M N : Mat2) : Mat2 :=
  { a := M.a * N.a + M.b * N.c
  , b := M.a * N.b + M.b * N.d
  , c := M.c * N.a + M.d * N.c
  , d := M.c * N.b + M.d * N.d }

/-- The `2 × 2` identity matrix over `Int`. -/
def matId : Mat2 := { a := 1, b := 0, c := 0, d := 1 }

/-- Iterated matrix power `M^k`. -/
def matPow (M : Mat2) : Nat → Mat2
  | 0     => matId
  | k + 1 => matMul M (matPow M k)

/-- Trace of a `Mat2`: `a + d`. -/
def trace (M : Mat2) : Int := M.a + M.d

/-- Determinant of a `Mat2`: `a · d - b · c`. -/
def det (M : Mat2) : Int := M.a * M.d - M.b * M.c

/-! ## Named matrices -/

/-- Fibonacci matrix `F = [[1, 1], [1, 0]]`, `tr = 1`, `det = -1`. -/
def fibF : Mat2 := { a := 1, b := 1, c := 1, d := 0 }

/-- Cat-map matrix `A = [[2, 1], [1, 1]] = F²`, `tr = 3`, `det = 1`. -/
def catA : Mat2 := { a := 2, b := 1, c := 1, d := 1 }

/-- Pell matrix `P = [[1, 2], [1, 1]]`, `tr = 2`, `det = -1`. -/
def pellP : Mat2 := { a := 1, b := 2, c := 1, d := 1 }

/-- Trace/det of the three named matrices match the header table. -/
theorem named_matrix_trace_det :
    trace fibF  = 1 ∧ det fibF  = -1 ∧
    trace catA  = 3 ∧ det catA  =  1 ∧
    trace pellP = 2 ∧ det pellP = -1 := by decide

/-! ## Matrix-trace bridge at `k = 0, 1, 2, 3, 4`

For each of the three named matrices, we witness

    trace (matPow A k) = genTrace (trace A) (det A) 2 (trace A) k

at `k = 0, 1, 2, 3, 4` by kernel computation. This realizes the
Cayley–Hamilton trace identity numerically at five indices per matrix.
`maxRecDepth` is raised where the unfolding at `k = 4` demands it. -/

-- Fibonacci matrix → Lucas sequence.
set_option maxRecDepth 2048 in
theorem fibF_matrix_bridge :
    trace (matPow fibF 0) = genTrace 1 (-1) 2 1 0 ∧
    trace (matPow fibF 1) = genTrace 1 (-1) 2 1 1 ∧
    trace (matPow fibF 2) = genTrace 1 (-1) 2 1 2 ∧
    trace (matPow fibF 3) = genTrace 1 (-1) 2 1 3 ∧
    trace (matPow fibF 4) = genTrace 1 (-1) 2 1 4 := by decide

-- Cat matrix → cat-trace sequence.
set_option maxRecDepth 2048 in
theorem catA_matrix_bridge :
    trace (matPow catA 0) = genTrace 3 1 2 3 0 ∧
    trace (matPow catA 1) = genTrace 3 1 2 3 1 ∧
    trace (matPow catA 2) = genTrace 3 1 2 3 2 ∧
    trace (matPow catA 3) = genTrace 3 1 2 3 3 ∧
    trace (matPow catA 4) = genTrace 3 1 2 3 4 := by decide

-- Pell matrix → Pell-companion sequence.
set_option maxRecDepth 2048 in
theorem pellP_matrix_bridge :
    trace (matPow pellP 0) = genTrace 2 (-1) 2 2 0 ∧
    trace (matPow pellP 1) = genTrace 2 (-1) 2 2 1 ∧
    trace (matPow pellP 2) = genTrace 2 (-1) 2 2 2 ∧
    trace (matPow pellP 3) = genTrace 2 (-1) 2 2 3 ∧
    trace (matPow pellP 4) = genTrace 2 (-1) 2 2 4 := by decide

/-! ## Trace-pair mod-period certificates

For a two-parameter recurrence `t_{k+2} = s · t_{k+1} - d · t_k`, the
sequence modulo `n` is determined by the pair `(t_k, t_{k+1}) mod n`.
If `(t_P, t_{P+1}) mod n = (t_0, t_1) mod n` then the period divides
`P`. We record such witnesses for each family at `n = 5`.

We use `Int.emod` (which returns a non-negative residue for positive
modulus). `n = 5` is chosen because `ord(A_cat, 5) = 10` is the
sharpest peer-verified cat-map period in this repo. -/

/-- Cat trace `(s, d) = (3, 1)` modulo `5`: period divides `10`.
`(catTraceViaGen 10, catTraceViaGen 11) mod 5 = (2, 3) = (t_0, t_1) mod 5`. -/
theorem catTraceViaGen_period_mod_5 :
    catTraceViaGen 10 % 5 = catTraceViaGen 0 % 5 ∧
    catTraceViaGen 11 % 5 = catTraceViaGen 1 % 5 ∧
    catTraceViaGen 10 % 5 = 2 ∧
    catTraceViaGen 11 % 5 = 3 := by decide

/-- Lucas `(s, d) = (1, -1)` modulo `5`: period divides `20` (Pisano
`π(5) = 20`). `(lucasViaGen 20, lucasViaGen 21) mod 5 = (t_0, t_1) mod 5`. -/
theorem lucasViaGen_period_mod_5 :
    lucasViaGen 20 % 5 = lucasViaGen 0 % 5 ∧
    lucasViaGen 21 % 5 = lucasViaGen 1 % 5 ∧
    lucasViaGen 20 % 5 = 2 ∧
    lucasViaGen 21 % 5 = 1 := by decide

/-- Pell `(s, d) = (2, -1)` modulo `5`: period divides `12`.
`(pellCompanionViaGen 12, pellCompanionViaGen 13) mod 5 = (t_0, t_1) mod 5`. -/
theorem pellCompanionViaGen_period_mod_5 :
    pellCompanionViaGen 12 % 5 = pellCompanionViaGen 0 % 5 ∧
    pellCompanionViaGen 13 % 5 = pellCompanionViaGen 1 % 5 ∧
    pellCompanionViaGen 12 % 5 = 2 ∧
    pellCompanionViaGen 13 % 5 = 2 := by decide

/-! ## Cassini-analogue

For the generalized recurrence, the Cassini difference
`t_{k-1} · t_{k+1} - t_k²` is a geometric sequence in `d` with ratio
`d`. Concretely, with the canonical initial conditions `(t_0, t_1)
= (2, s)`,

    t_{k-1} · t_{k+1} - t_k² = d^{k-1} · (2 · t_2 - t_1²)
                             = d^{k-1} · (2 (s² - 2 d) - s²)
                             = d^{k-1} · (s² - 4 d).

For Lucas `d = -1`, this gives `(-1)^{k-1} · 5`, which flips sign; for
cat-trace `d = 1` it stays constant at `5`. Witnessed at `k = 1, 2, 3, 4`.
`Int` subtraction is used (no sign issues). -/

/-- Lucas Cassini: sign-flipping `(-1)^{k-1} · 5` across `k = 1, 2, 3, 4`.
`k = 1`: `t_0 t_2 - t_1² = 2 · 3 - 1 = 5` (so `(-1)^0 · 5 = 5`).
`k = 2`: `t_1 t_3 - t_2² = 1 · 4 - 9 = -5`.
`k = 3`: `t_2 t_4 - t_3² = 3 · 7 - 16 = 5`.
`k = 4`: `t_3 t_5 - t_4² = 4 · 11 - 49 = -5`. -/
theorem lucasViaGen_cassini_sign_flip :
    lucasViaGen 0 * lucasViaGen 2 - lucasViaGen 1 ^ 2 =  5 ∧
    lucasViaGen 1 * lucasViaGen 3 - lucasViaGen 2 ^ 2 = -5 ∧
    lucasViaGen 2 * lucasViaGen 4 - lucasViaGen 3 ^ 2 =  5 ∧
    lucasViaGen 3 * lucasViaGen 5 - lucasViaGen 4 ^ 2 = -5 := by decide

/-- Cat-trace Cassini: constant `5` across `k = 1, 2, 3, 4`.
Matches `catTrace_cassini_*` in `CatMapLucasBridge.lean` but stated
over `Int`. -/
theorem catTraceViaGen_cassini_constant :
    catTraceViaGen 0 * catTraceViaGen 2 - catTraceViaGen 1 ^ 2 = 5 ∧
    catTraceViaGen 1 * catTraceViaGen 3 - catTraceViaGen 2 ^ 2 = 5 ∧
    catTraceViaGen 2 * catTraceViaGen 4 - catTraceViaGen 3 ^ 2 = 5 ∧
    catTraceViaGen 3 * catTraceViaGen 5 - catTraceViaGen 4 ^ 2 = 5 := by decide

/-- Pell Cassini: geometric in `d = -1`, value `(-1)^{k-1} · 8`.
`k = 1`: `2 · 6 - 4 = 8`.  `k = 2`: `2 · 14 - 36 = -8`.
`k = 3`: `6 · 34 - 196 = 8`.  `k = 4`: `14 · 82 - 1156 = -8`. -/
theorem pellCompanionViaGen_cassini_sign_flip :
    pellCompanionViaGen 0 * pellCompanionViaGen 2 - pellCompanionViaGen 1 ^ 2 =  8 ∧
    pellCompanionViaGen 1 * pellCompanionViaGen 3 - pellCompanionViaGen 2 ^ 2 = -8 ∧
    pellCompanionViaGen 2 * pellCompanionViaGen 4 - pellCompanionViaGen 3 ^ 2 =  8 ∧
    pellCompanionViaGen 3 * pellCompanionViaGen 5 - pellCompanionViaGen 4 ^ 2 = -8 := by decide

/-! ## Discriminant classification

The discriminant of the characteristic polynomial `x² - s x + d` is
`Δ = s² - 4 d`. Two `(s, d)` pairs "live in the same quadratic field"
when they realize the same squarefree part of `Δ`.

- Fib `(1, -1)`:  `Δ = 1 - 4 · (-1) = 5`. Squarefree part `5`.
- Cat `(3, 1)`:  `Δ = 9 - 4 · 1 = 5`. Squarefree part `5`.
- Pell `(2, -1)`: `Δ = 4 - 4 · (-1) = 8 = 4 · 2`. Squarefree part `2`.

Fib and Cat share `Δ = 5`, consistent with `A_cat = F²` (squaring
preserves the splitting field of the characteristic polynomial). Pell
sits in `ℤ[√2]`.

We record the discriminants and the Fib/Cat coincidence as decidable
facts. We do *not* go on to identify quadratic rings or minimal
polynomials in Lean; the "same family" claim is recorded here at the
formula level `Δ_Fib = Δ_Cat`. -/

/-- Discriminant `Δ = s² - 4 d` of the characteristic polynomial
`x² - s x + d`. -/
def discriminant (s d : Int) : Int := s ^ 2 - 4 * d

/-- Discriminants of the four recurrence instances. -/
theorem discriminant_table :
    discriminant 1 (-1) = 5 ∧
    discriminant 3  1   = 5 ∧
    discriminant 2 (-1) = 8 ∧
    discriminant 4  2   = 8 := by decide

/-- Fib and Cat share the same discriminant `5`: they realize
two-parameter recurrences in the same quadratic-field family `ℤ[√5]`
at the formula level. -/
theorem fib_cat_same_discriminant :
    discriminant 1 (-1) = discriminant 3 1 := by decide

/-- Pell does *not* share the Fib/Cat discriminant: `Δ_Pell = 8 ≠ 5 = Δ_Fib`. -/
theorem pell_distinct_discriminant :
    discriminant 2 (-1) ≠ discriminant 1 (-1) := by decide

/-- The new `F³` instance `(s, d) = (4, 2)` has discriminant `8`,
the *same* discriminant as Pell. (The squarefree part of `8` is `2`,
so `F³` traces and Pell traces share the underlying quadratic field
`ℤ[√2]` at the formula level — even though `F` itself sits in
`ℤ[√5]`. This records the instance; no deeper claim is made.) -/
theorem fibCubed_same_discriminant_as_pell :
    discriminant 4 2 = discriminant 2 (-1) := by decide

/-! ## Master synthesis

All six items packaged into one conjunction. Witnesses the unified
two-parameter trace family at all indices used above. -/

set_option maxRecDepth 2048 in
theorem trace_family_master :
    -- 1. Lucas, cat-trace, Pell-companion, F³ tables match at k = 0..7.
    (lucasViaGen 0 = 2 ∧ lucasViaGen 1 = 1 ∧ lucasViaGen 7 = 29) ∧
    (catTraceViaGen 0 = 2 ∧ catTraceViaGen 1 = 3 ∧ catTraceViaGen 7 = 843) ∧
    (pellCompanionViaGen 0 = 2 ∧ pellCompanionViaGen 1 = 2 ∧
     pellCompanionViaGen 7 = 478) ∧
    (fibCubedTraceViaGen 0 = 2 ∧ fibCubedTraceViaGen 1 = 4 ∧
     fibCubedTraceViaGen 7 = 5408) ∧
    -- 2. Named-matrix trace / det values.
    (trace fibF = 1 ∧ det fibF = -1 ∧
     trace catA = 3 ∧ det catA = 1 ∧
     trace pellP = 2 ∧ det pellP = -1) ∧
    -- 3. Matrix bridge at k = 2, 3, 4 for all three families.
    (trace (matPow fibF 2)  = genTrace 1 (-1) 2 1 2 ∧
     trace (matPow fibF 3)  = genTrace 1 (-1) 2 1 3 ∧
     trace (matPow fibF 4)  = genTrace 1 (-1) 2 1 4 ∧
     trace (matPow catA 2)  = genTrace 3 1 2 3 2 ∧
     trace (matPow catA 3)  = genTrace 3 1 2 3 3 ∧
     trace (matPow catA 4)  = genTrace 3 1 2 3 4 ∧
     trace (matPow pellP 2) = genTrace 2 (-1) 2 2 2 ∧
     trace (matPow pellP 3) = genTrace 2 (-1) 2 2 3 ∧
     trace (matPow pellP 4) = genTrace 2 (-1) 2 2 4) ∧
    -- 4. Trace-pair mod-5 periods.
    (catTraceViaGen 10 % 5 = 2 ∧ catTraceViaGen 11 % 5 = 3 ∧
     lucasViaGen 20 % 5 = 2   ∧ lucasViaGen 21 % 5 = 1   ∧
     pellCompanionViaGen 12 % 5 = 2 ∧ pellCompanionViaGen 13 % 5 = 2) ∧
    -- 5. Cassini analogues.
    (lucasViaGen 0 * lucasViaGen 2 - lucasViaGen 1 ^ 2 = 5 ∧
     lucasViaGen 1 * lucasViaGen 3 - lucasViaGen 2 ^ 2 = -5 ∧
     catTraceViaGen 0 * catTraceViaGen 2 - catTraceViaGen 1 ^ 2 = 5 ∧
     catTraceViaGen 1 * catTraceViaGen 3 - catTraceViaGen 2 ^ 2 = 5 ∧
     pellCompanionViaGen 0 * pellCompanionViaGen 2 - pellCompanionViaGen 1 ^ 2 = 8 ∧
     pellCompanionViaGen 1 * pellCompanionViaGen 3 - pellCompanionViaGen 2 ^ 2 = -8) ∧
    -- 6. Discriminant classification.
    (discriminant 1 (-1) = 5 ∧
     discriminant 3 1     = 5 ∧
     discriminant 2 (-1) = 8 ∧
     discriminant 4 2     = 8 ∧
     discriminant 1 (-1) = discriminant 3 1 ∧
     discriminant 2 (-1) ≠ discriminant 1 (-1)) := by decide

end PellCatLucasTraceFamily
end Gnosis
