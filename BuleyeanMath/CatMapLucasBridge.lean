import Init

/-!
# Cat-Map / Lucas Bridge

This module synthesizes content from `ArnoldCatMapOrder5.lean` and the
Lucas-sequence content in `FibLucasExtendedIdentities.lean` /
`IndependentSetCycleCnLucas.lean`. The Arnold cat-map matrix

    A = [ 2  1 ]
        [ 1  1 ]

has characteristic polynomial `x² - 3·x + 1`. The trace sequence
`t_k := tr(A^k)` satisfies the Lucas-type recurrence

    t_{k+2} = 3 · t_{k+1} - t_k,    t_0 = 2,  t_1 = 3,

which is structurally parallel to but numerically distinct from the
standard Lucas sequence `L` defined by `L_0 = 2, L_1 = 1,
L_{k+2} = L_{k+1} + L_k`.

## What this module witnesses

1. A direct `Nat`-valued definition `catTrace : Nat → Nat` satisfying
   the cat-trace recurrence.
2. An inline re-definition of the standard Lucas sequence `lucas`, so
   the file is self-contained.
3. A separation witness: `catTrace 2 = 7 ≠ 3 = lucas 2`. Both
   sequences are Lucas-type (linear two-term recurrence with
   trace-like initial conditions `(2, ·)`), but they differ.
4. A matrix realization of `catTrace` as `tr(A^k)`: an inline `matMul`,
   `matPow`, and `trace` on `2 × 2` `Nat` matrices, with pointwise
   equality `catTrace k = trace (matPow A k)` verified for
   `k = 0, 1, ..., 7`.
5. A Fibonacci-matrix sub-identity: the cat-map matrix `A` instantiates
   as `F²` where `F = [[1,1],[1,0]]` is the Fibonacci matrix. The
   equality `matPow F 2 = A` is closed by `decide`.
6. A Cassini-analogue for the cat-trace sequence:
   `catTrace (k-1) · catTrace (k+1) - catTrace k ^ 2 = 5`, verified
   for `k = 1, 2, 3, 4, 5`. The constant `5` witnesses the
   discriminant of `x² - 3·x + 1`.
7. A trace-based certificate for the period result `ord(A, 5) = 10`
   from `ArnoldCatMapOrder5.lean`: `catTrace 10 mod 5 = 2` and
   `catTrace 11 mod 5 = 3` match the initial conditions `(t_0, t_1)
   mod 5`, consistent with `A^10 ≡ I (mod 5)`. The `(mod 3)` analogue
   for the period `ord(A, 3) = 4` is also checked.

## What this module does *not* claim

- No general theorem `∀ k, catTrace k = tr(A^k)` is produced; the
  bridge is witnessed at the eight indices `k = 0, ..., 7`. The
  recurrence identity between `catTrace` and `tr · matPow A` is
  *computed* at those indices, not derived as a structural lemma.
- No continuous ergodic theory, no torus dynamics, no link to
  Kolmogorov-Sinai entropy or Pesin theory. The matrix `A` is fixed
  throughout and handled as a `Nat`-valued object.
- The Cassini-analogue constant `5` is identified as the discriminant
  of `x² - 3·x + 1` in prose; no characteristic-polynomial machinery
  is invoked in Lean.
- The trace-mod-`n` certificate (item 7) does *not* prove the
  converse: matching initial conditions mod `n` is necessary for
  `A^k ≡ I (mod n)` but not sufficient in general. Item 7 checks the
  necessary side at the known period.
- No import of peer modules: the `CatMap` definition, `lucas`,
  `catTrace`, and matrix operations are re-declared inline so this
  file compiles standalone under
  `lean Lean/BuleyeanMath/CatMapLucasBridge.lean`.

No `sorry`, no new `axiom`, `Init`-only. Each numerical identity
closes by kernel `decide`; `maxRecDepth` is raised locally where the
`matPow` unfolding at `k = 7` requires it.
-/

namespace BuleyeanMath
namespace CatMapLucasBridge

/-! ## Inline peer-module definitions

Re-declared here so the file compiles without `import
BuleyeanMath.*`. Values match the corresponding definitions
in `ArnoldCatMapOrder5.lean` and `IndependentSetCycleCnLucas.lean`. -/

/-- Cat-trace sequence `t_k = tr(A^k)` where `A = [[2,1],[1,1]]`.
Direct Lucas-type recurrence: `t_0 = 2, t_1 = 3,
t_{k+2} = 3 · t_{k+1} - t_k`. Values for small `k`: `2, 3, 7, 18, 47,
123, 322, 843, 2207, 5778, 15127, 39603, ...`. Monotone increasing,
so `Nat` subtraction is safe. Matches `traceCatPow` in
`ArnoldCatMapOrder5.lean`. -/
def catTrace : Nat → Nat
  | 0     => 2
  | 1     => 3
  | k + 2 => 3 * catTrace (k + 1) - catTrace k

/-- Standard Lucas numbers with `L_0 = 2, L_1 = 1, L_{k+2} = L_{k+1} +
L_k`. Matches `lucas` in `IndependentSetCycleCnLucas.lean` and
`FibLucasExtendedIdentities.lean`. -/
def lucas : Nat → Nat
  | 0     => 2
  | 1     => 1
  | k + 2 => lucas (k + 1) + lucas k

/-! ## Cat-trace table (sanity)

Matches `traceCatPow_table` in `ArnoldCatMapOrder5.lean`. -/

/-- First eight values of `catTrace`: `2, 3, 7, 18, 47, 123, 322, 843`. -/
theorem catTrace_table :
    catTrace 0 = 2   ∧ catTrace 1 = 3   ∧
    catTrace 2 = 7   ∧ catTrace 3 = 18  ∧
    catTrace 4 = 47  ∧ catTrace 5 = 123 ∧
    catTrace 6 = 322 ∧ catTrace 7 = 843 := by decide

/-! ## Separation: `catTrace ≠ lucas`

Both sequences begin with `2` at index `0` and are linear two-term
recurrences, but the next terms diverge. `catTrace 1 = 3` vs
`lucas 1 = 1`, and the recurrence coefficients differ (`3` vs `1`). -/

/-- The two sequences agree at `k = 0`: `catTrace 0 = lucas 0 = 2`. -/
theorem catTrace_lucas_agree_0 : catTrace 0 = lucas 0 := by decide

/-- The two sequences disagree at `k = 1`: `catTrace 1 = 3`, `lucas 1 = 1`. -/
theorem catTrace_lucas_disagree_1 : catTrace 1 ≠ lucas 1 := by decide

/-- The two sequences disagree at `k = 2`: `catTrace 2 = 7`, `lucas 2 = 3`. -/
theorem catTrace_lucas_disagree_2 : catTrace 2 = 7 ∧ lucas 2 = 3 := by decide

/-- Separation witness: `catTrace 2 ≠ lucas 2`. -/
theorem catTrace_ne_lucas_at_2 : catTrace 2 ≠ lucas 2 := by decide

/-! ## Inline `2 × 2` `Nat`-matrix algebra

Minimal structure for computing `tr(A^k)` directly. -/

/-- A `2 × 2` matrix over `Nat`, entries `a, b, c, d` in row-major
order `[[a, b], [c, d]]`. -/
structure Mat2 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
deriving DecidableEq, Repr

/-- Matrix multiplication on `Mat2`. -/
def matMul (M N : Mat2) : Mat2 :=
  { a := M.a * N.a + M.b * N.c
  , b := M.a * N.b + M.b * N.d
  , c := M.c * N.a + M.d * N.c
  , d := M.c * N.b + M.d * N.d }

/-- The `2 × 2` identity matrix. -/
def matId : Mat2 := { a := 1, b := 0, c := 0, d := 1 }

/-- Iterated matrix power `M^k`. -/
def matPow (M : Mat2) : Nat → Mat2
  | 0     => matId
  | k + 1 => matMul M (matPow M k)

/-- Trace of a `Mat2`: `a + d`. -/
def trace (M : Mat2) : Nat := M.a + M.d

/-- The Arnold cat-map matrix `A = [[2, 1], [1, 1]]`. -/
def catA : Mat2 := { a := 2, b := 1, c := 1, d := 1 }

/-- The Fibonacci matrix `F = [[1, 1], [1, 0]]`. -/
def fibF : Mat2 := { a := 1, b := 1, c := 1, d := 0 }

/-! ## Fibonacci-matrix sub-identity: `F² = A`

The Fibonacci matrix `F` satisfies `F² = [[2,1],[1,1]]`, which equals
the cat-map matrix `A`. Stated on `Mat2` via structural equality. -/

/-- **`F² = A`** as `Mat2`. Direct product:
`F² = [[1·1+1·1, 1·1+1·0], [1·1+0·1, 1·1+0·0]] = [[2,1],[1,1]]`. -/
theorem fibF_squared_eq_catA : matPow fibF 2 = catA := by decide

/-! ## Bridge: `catTrace k = trace (matPow catA k)`

Witness the Lucas-type recurrence `catTrace` as the matrix-trace
sequence of `A^k`, index by index from `0` to `7`. At each `k`
the left side is a pure `Nat` recurrence, the right side unfolds a
`matPow` chain and takes `a + d`. They agree. `maxRecDepth` is raised
locally to accommodate the `k = 6, 7` unfoldings. -/

/-- `tr(A^0) = tr(I) = 2 = catTrace 0`. -/
theorem catTrace_eq_trace_0 : catTrace 0 = trace (matPow catA 0) := by decide

/-- `tr(A^1) = 2 + 1 = 3 = catTrace 1`. -/
theorem catTrace_eq_trace_1 : catTrace 1 = trace (matPow catA 1) := by decide

/-- `tr(A^2) = 7 = catTrace 2`. -/
theorem catTrace_eq_trace_2 : catTrace 2 = trace (matPow catA 2) := by decide

/-- `tr(A^3) = 18 = catTrace 3`. -/
theorem catTrace_eq_trace_3 : catTrace 3 = trace (matPow catA 3) := by decide

/-- `tr(A^4) = 47 = catTrace 4`. -/
theorem catTrace_eq_trace_4 : catTrace 4 = trace (matPow catA 4) := by decide

/-- `tr(A^5) = 123 = catTrace 5`. -/
theorem catTrace_eq_trace_5 : catTrace 5 = trace (matPow catA 5) := by decide

-- `tr(A^6) = 322 = catTrace 6`.
set_option maxRecDepth 2048 in
theorem catTrace_eq_trace_6 : catTrace 6 = trace (matPow catA 6) := by decide

-- `tr(A^7) = 843 = catTrace 7`.
set_option maxRecDepth 4096 in
theorem catTrace_eq_trace_7 : catTrace 7 = trace (matPow catA 7) := by decide

-- Packaged bridge: `catTrace k = trace (matPow catA k)` for `k = 0, ..., 7`.
set_option maxRecDepth 4096 in
theorem catTrace_eq_trace_bridge :
    catTrace 0 = trace (matPow catA 0) ∧
    catTrace 1 = trace (matPow catA 1) ∧
    catTrace 2 = trace (matPow catA 2) ∧
    catTrace 3 = trace (matPow catA 3) ∧
    catTrace 4 = trace (matPow catA 4) ∧
    catTrace 5 = trace (matPow catA 5) ∧
    catTrace 6 = trace (matPow catA 6) ∧
    catTrace 7 = trace (matPow catA 7) := by decide

/-! ## Cassini analogue for the cat-trace sequence

For the standard Lucas sequence, Cassini's identity reads
`L_{k-1} · L_{k+1} - L_k² = -5 · (-1)^k`. For the cat-trace sequence
`catTrace` with recurrence coefficient `3` (in place of `1`), the
analogue collapses to a constant: `catTrace (k-1) · catTrace (k+1) -
catTrace k ^ 2 = 5`. The constant `5` realizes the discriminant of
the characteristic polynomial `x² - 3·x + 1`, i.e. `9 - 4 = 5`. No
sign alternation survives here because the discriminant is positive
and `det(A) = 1`.

Checked for `k = 1, 2, 3, 4, 5`. `Nat` subtraction is safe because
`catTrace` is strictly increasing from `k ≥ 1` and the Cassini
difference is manifestly non-negative (equal to `5`). -/

/-- **`catTrace 0 · catTrace 2 - catTrace 1 ^ 2 = 5`**. -/
theorem catTrace_cassini_1 :
    catTrace 0 * catTrace 2 - catTrace 1 ^ 2 = 5 := by decide

/-- **`catTrace 1 · catTrace 3 - catTrace 2 ^ 2 = 5`**. -/
theorem catTrace_cassini_2 :
    catTrace 1 * catTrace 3 - catTrace 2 ^ 2 = 5 := by decide

/-- **`catTrace 2 · catTrace 4 - catTrace 3 ^ 2 = 5`**. -/
theorem catTrace_cassini_3 :
    catTrace 2 * catTrace 4 - catTrace 3 ^ 2 = 5 := by decide

/-- **`catTrace 3 · catTrace 5 - catTrace 4 ^ 2 = 5`**. -/
theorem catTrace_cassini_4 :
    catTrace 3 * catTrace 5 - catTrace 4 ^ 2 = 5 := by decide

/-- **`catTrace 4 · catTrace 6 - catTrace 5 ^ 2 = 5`**. -/
theorem catTrace_cassini_5 :
    catTrace 4 * catTrace 6 - catTrace 5 ^ 2 = 5 := by decide

/-- Packaged Cassini-analogue: constant `5` at `k = 1, 2, 3, 4, 5`. -/
theorem catTrace_cassini_package :
    catTrace 0 * catTrace 2 - catTrace 1 ^ 2 = 5 ∧
    catTrace 1 * catTrace 3 - catTrace 2 ^ 2 = 5 ∧
    catTrace 2 * catTrace 4 - catTrace 3 ^ 2 = 5 ∧
    catTrace 3 * catTrace 5 - catTrace 4 ^ 2 = 5 ∧
    catTrace 4 * catTrace 6 - catTrace 5 ^ 2 = 5 := by decide

/-! ## Dynamical interpretation: trace certificate for period on `ℤ/n`

From `ArnoldCatMapOrder5.lean`, `ord(A, 5) = 10`, i.e. `A^10 ≡ I (mod
5)` and no smaller positive power is congruent to `I`. A necessary
condition for `A^k ≡ I (mod n)` is that the pair
`(tr(A^k), tr(A^{k+1}))` match the pair `(tr(I), tr(A)) = (2, 3)`
modulo `n` — because the trace sequence determines, via the
recurrence, every subsequent trace modulo `n` once two consecutive
traces are fixed. So if `(catTrace k, catTrace (k+1))` reduces mod
`n` to `(catTrace 0, catTrace 1) mod n`, then the `Nat` sequence
`(catTrace (k+j) mod n)_{j ≥ 0}` matches `(catTrace j mod n)_{j ≥ 0}`
going forward. This is the trace-based certificate we record here.

We state the certificate as *matching reductions* of the initial
pair, rather than as explicit residues, because the reduction of
`catTrace 1 = 3` differs by modulus: `3 mod 5 = 3`, `3 mod 3 = 0`,
`3 mod 2 = 1`. The period witness is pair-equality, not a specific
residue.

We verify this necessary condition at the known periods:

- `ord(A, 5) = 10`: `(catTrace 10, catTrace 11) ≡ (catTrace 0,
  catTrace 1) (mod 5)`, reducing to `(2, 3)`.
- `ord(A, 3) = 4`: `(catTrace 4, catTrace 5) ≡ (catTrace 0,
  catTrace 1) (mod 3)`, reducing to `(2, 0)`.
- `ord(A, 2) = 3`: `(catTrace 3, catTrace 4) ≡ (catTrace 0,
  catTrace 1) (mod 2)`, reducing to `(0, 1)`.

We do *not* prove the converse (matching trace pair implies matrix
identity) — that would require a Cayley-Hamilton / minimal-polynomial
argument we do not carry out here. -/

/-- Trace-pair certificate at the known period `ord(A, 5) = 10`:
`(catTrace 10, catTrace 11) mod 5 = (catTrace 0, catTrace 1) mod 5
= (2, 3)`. Consistent with `A^10 ≡ I (mod 5)` witnessed in
`ArnoldCatMapOrder5.lean`. -/
theorem catTrace_mod_5_period_10 :
    catTrace 10 % 5 = catTrace 0 % 5 ∧ catTrace 11 % 5 = catTrace 1 % 5 ∧
    catTrace 10 % 5 = 2 ∧ catTrace 11 % 5 = 3 := by decide

/-- Trace-pair certificate at the known period `ord(A, 3) = 4`:
`(catTrace 4, catTrace 5) mod 3 = (catTrace 0, catTrace 1) mod 3
= (2, 0)`. Consistent with `A^4 ≡ I (mod 3)` witnessed in
`ArnoldCatMapOrder5.lean`. Note `catTrace 1 = 3 ≡ 0 (mod 3)`. -/
theorem catTrace_mod_3_period_4 :
    catTrace 4 % 3 = catTrace 0 % 3 ∧ catTrace 5 % 3 = catTrace 1 % 3 ∧
    catTrace 4 % 3 = 2 ∧ catTrace 5 % 3 = 0 := by decide

/-- Trace-pair certificate at the known period `ord(A, 2) = 3`:
`(catTrace 3, catTrace 4) mod 2 = (catTrace 0, catTrace 1) mod 2
= (0, 1)`. Consistent with `A^3 ≡ I (mod 2)` witnessed in
`ArnoldCatMapOrder5.lean`. -/
theorem catTrace_mod_2_period_3 :
    catTrace 3 % 2 = catTrace 0 % 2 ∧ catTrace 4 % 2 = catTrace 1 % 2 ∧
    catTrace 3 % 2 = 0 ∧ catTrace 4 % 2 = 1 := by decide

/-! ## Fibonacci-via-matrix sub-bridge

The Fibonacci matrix `F` has `F^k = [[F_{k+1}, F_k], [F_k, F_{k-1}]]`
for `k ≥ 1`, so `tr(F^k) = F_{k+1} + F_{k-1} = L_k` (the standard
Lucas number, by the "Bragg Peak" identity recorded in
`FibLucasExtendedIdentities.lean`). This hands the standard `lucas`
sequence back through the matrix formalism via `F`, while `catTrace`
is handed back via `A = F²`. So `catTrace k = tr(F^{2k})`, i.e. the
cat-trace at index `k` equals the Fibonacci-matrix trace at index
`2k`. -/

-- `catTrace k = tr(F^{2k})` witnessed at `k = 0, 1, 2, 3`. Uses
-- `matPow fibF (2*k)` and compares to `catTrace k`. The identity
-- factors through `F² = A` together with `catTrace k = tr(A^k)`.
set_option maxRecDepth 4096 in
theorem catTrace_eq_trace_fibF_even :
    catTrace 0 = trace (matPow fibF 0) ∧
    catTrace 1 = trace (matPow fibF 2) ∧
    catTrace 2 = trace (matPow fibF 4) ∧
    catTrace 3 = trace (matPow fibF 6) := by decide

/-- **`lucas k = tr(F^k)`** witnessed at `k = 1, 2, 3, 4, 5`. The
"Bragg Peak" identity `L_k = F_{k-1} + F_{k+1}` realized via matrix
trace. Excludes `k = 0` because `matPow fibF 0 = I` has trace `2` and
`lucas 0 = 2` — which *does* match but needs no witnessing beyond
`decide`; we include it for completeness. -/
theorem lucas_eq_trace_fibF :
    lucas 0 = trace (matPow fibF 0) ∧
    lucas 1 = trace (matPow fibF 1) ∧
    lucas 2 = trace (matPow fibF 2) ∧
    lucas 3 = trace (matPow fibF 3) ∧
    lucas 4 = trace (matPow fibF 4) ∧
    lucas 5 = trace (matPow fibF 5) := by decide

/-! ## Master bridge package

Ties the six bridge identities above into a single conjunction for
downstream modules. -/

-- **Master synthesis**: the six bridge items, packaged.
set_option maxRecDepth 4096 in
theorem catMap_lucas_bridge :
    -- 1. catTrace table holds.
    (catTrace 0 = 2 ∧ catTrace 1 = 3 ∧ catTrace 2 = 7 ∧
     catTrace 3 = 18 ∧ catTrace 4 = 47 ∧ catTrace 5 = 123) ∧
    -- 2. lucas differs from catTrace at k = 2.
    catTrace 2 ≠ lucas 2 ∧
    -- 3. F² = A.
    matPow fibF 2 = catA ∧
    -- 4. catTrace k = tr(A^k) for k = 0..5.
    (catTrace 0 = trace (matPow catA 0) ∧
     catTrace 1 = trace (matPow catA 1) ∧
     catTrace 2 = trace (matPow catA 2) ∧
     catTrace 3 = trace (matPow catA 3) ∧
     catTrace 4 = trace (matPow catA 4) ∧
     catTrace 5 = trace (matPow catA 5)) ∧
    -- 5. Cassini-analogue constant 5, k = 1..5.
    (catTrace 0 * catTrace 2 - catTrace 1 ^ 2 = 5 ∧
     catTrace 1 * catTrace 3 - catTrace 2 ^ 2 = 5 ∧
     catTrace 2 * catTrace 4 - catTrace 3 ^ 2 = 5 ∧
     catTrace 3 * catTrace 5 - catTrace 4 ^ 2 = 5 ∧
     catTrace 4 * catTrace 6 - catTrace 5 ^ 2 = 5) ∧
    -- 6. Trace certificate at period mod 5 and mod 3.
    (catTrace 10 % 5 = catTrace 0 % 5 ∧ catTrace 11 % 5 = catTrace 1 % 5 ∧
     catTrace 4 % 3 = catTrace 0 % 3 ∧ catTrace 5 % 3 = catTrace 1 % 3) := by decide

end CatMapLucasBridge
end BuleyeanMath
