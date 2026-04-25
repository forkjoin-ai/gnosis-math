import Init

/-!
# Ramanujan Triplet Phase — Special vs Non-Special Primes

Extends `RamanujanPartitionMod5.lean` and the `GodFormulaPhaseManifestations`
catalog.

## The unknowable

Ramanujan showed:

  p(5n + 4) ≡ 0  (mod 5)
  p(7n + 5) ≡ 0  (mod 7)
  p(11n + 6) ≡ 0 (mod 11)

These are the **only** prime moduli `m` with a nontrivial congruence
`p(m·n + r) ≡ 0 (mod m)` for some fixed `r`. No `m ∈ {2, 3, 13, 17, …}`
admits such a congruence. The general statement — "exactly three
special primes {5, 7, 11}" — sits behind a deep wall of modular-form
theory (Ramanujan's τ-function, Hecke operators, Serre's theorem).
Ring-extension + category-machinery walls.

## What this module does

- Positive witnesses: the three Ramanujan congruences hold at three
  depths each.
- Negative witnesses: at every candidate residue `r` mod `m` for
  `m ∈ {2, 3, 13}`, exhibit a small `n` where `p(m·n + r) % m ≠ 0`.
  Each negative witness rules out a potential congruence at that `r`.
  Enumerating all `r ∈ {0 .. m-1}` and ruling each one out shows that
  *no* Ramanujan congruence exists at modulus `m`.

The special-vs-non-special distinction is the **phase**. Primes
`{5, 7, 11}` sit on the plus phase; primes `{2, 3, 13, …}` sit on the
minus phase. The god formula's two-piece decomposition manifests as
"residue `r` exists" (plus) vs "every residue fails" (minus).

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace BuleyeanMath
namespace RamanujanTripletPhase

/-! ## Partition function via nested max-part recursion with fuel -/

def partitionsAux (fuel n k : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    if n = 0 then 1
    else if k = 0 then 0
    else if n < k then partitionsAux fuel n (k - 1)
    else partitionsAux fuel n (k - 1) + partitionsAux fuel (n - k) k

def p (n : Nat) : Nat := partitionsAux (n + n + 2) n n

/-! ## Sanity values -/

theorem p_0  : p 0  = 1   := by decide
theorem p_1  : p 1  = 1   := by decide
theorem p_2  : p 2  = 2   := by decide
theorem p_3  : p 3  = 3   := by decide
theorem p_4  : p 4  = 5   := by decide
theorem p_5  : p 5  = 7   := by decide
theorem p_6  : p 6  = 11  := by decide
theorem p_7  : p 7  = 15  := by decide
theorem p_9  : p 9  = 30  := by decide
theorem p_12 : p 12 = 77  := by decide
theorem p_14 : p 14 = 135 := by decide
theorem p_17 : p 17 = 297 := by decide
theorem p_19 : p 19 = 490 := by decide
theorem p_28 : p 28 = 3718 := by decide

/-! ## Positive phase: the three Ramanujan congruences

Each prime in `{5, 7, 11}` admits a `r` such that
`p(m·n + r) ≡ 0 (mod m)` for every `n`. Witnessed at three depths each. -/

/-! ### Mod 5: `r = 4` — `p(5n + 4) ≡ 0 (mod 5)` -/

theorem rm5_n0 : p 4  % 5 = 0 := by decide
theorem rm5_n1 : p 9  % 5 = 0 := by decide
theorem rm5_n2 : p 14 % 5 = 0 := by decide
theorem rm5_n3 : p 19 % 5 = 0 := by decide

/-! ### Mod 7: `r = 5` — `p(7n + 5) ≡ 0 (mod 7)` -/

theorem rm7_n0 : p 5  % 7 = 0 := by decide
theorem rm7_n1 : p 12 % 7 = 0 := by decide
theorem rm7_n2 : p 19 % 7 = 0 := by decide

/-! ### Mod 11: `r = 6` — `p(11n + 6) ≡ 0 (mod 11)` -/

theorem rm11_n0 : p 6  % 11 = 0 := by decide
theorem rm11_n1 : p 17 % 11 = 0 := by decide
theorem rm11_n2 : p 28 % 11 = 0 := by decide

/-! ## Negative phase: non-special primes admit no Ramanujan congruence

For each `m ∈ {2, 3, 13}` and each residue `r ∈ {0, …, m-1}`, exhibit
a concrete `n` where `p(m·n + r) % m ≠ 0`. Each negative witness rules
out a potential congruence at that `r`. Enumerating all `r` shows no
Ramanujan congruence exists at modulus `m`. -/

/-! ### Mod 2: both residues scraped -/

/-- `r = 0`: `p(0) = 1`, odd. -/
theorem no_rm2_r0_witness : p 0 % 2 ≠ 0 := by decide
/-- `r = 1`: `p(1) = 1`, odd. -/
theorem no_rm2_r1_witness : p 1 % 2 ≠ 0 := by decide

/-! ### Mod 3: all three residues scraped -/

/-- `r = 0`: `p(6) = 11`, and `11 % 3 = 2`. -/
theorem no_rm3_r0_witness : p 6 % 3 ≠ 0 := by decide
/-- `r = 1`: `p(1) = 1`, and `1 % 3 = 1`. -/
theorem no_rm3_r1_witness : p 1 % 3 ≠ 0 := by decide
/-- `r = 2`: `p(2) = 2`, and `2 % 3 = 2`. -/
theorem no_rm3_r2_witness : p 2 % 3 ≠ 0 := by decide

/-! ### Mod 13: every residue `0..12` scraped -/

theorem no_rm13_r0  : p 0  % 13 ≠ 0 := by decide
theorem no_rm13_r1  : p 1  % 13 ≠ 0 := by decide
theorem no_rm13_r2  : p 2  % 13 ≠ 0 := by decide
theorem no_rm13_r3  : p 3  % 13 ≠ 0 := by decide
theorem no_rm13_r4  : p 4  % 13 ≠ 0 := by decide
theorem no_rm13_r5  : p 5  % 13 ≠ 0 := by decide
theorem no_rm13_r6  : p 6  % 13 ≠ 0 := by decide
theorem no_rm13_r7  : p 7  % 13 ≠ 0 := by decide
theorem no_rm13_r8  : p 8  % 13 ≠ 0 := by decide
theorem no_rm13_r9  : p 9  % 13 ≠ 0 := by decide
theorem no_rm13_r10 : p 10 % 13 ≠ 0 := by decide
theorem no_rm13_r11 : p 11 % 13 ≠ 0 := by decide
theorem no_rm13_r12 : p 12 % 13 ≠ 0 := by decide

/-! ## Phase-span witness -/

/-- On the plus phase (special primes), some residue `r` satisfies
`∀ n, p(m·n + r) ≡ 0 (mod m)`. We witness `r = 4, 5, 6` for `m = 5, 7,
11` respectively, at three depths each. On the minus phase (non-special
primes `2, 3, 13`), every candidate `r` fails at some small `n`. -/
theorem ramanujan_triplet_phase_witness :
    -- Plus phase: 3 congruences × 3 depths each
    (p 4 % 5 = 0 ∧ p 9 % 5 = 0 ∧ p 14 % 5 = 0)
    ∧ (p 5 % 7 = 0 ∧ p 12 % 7 = 0 ∧ p 19 % 7 = 0)
    ∧ (p 6 % 11 = 0 ∧ p 17 % 11 = 0 ∧ p 28 % 11 = 0)
    -- Minus phase mod 2: both r scraped
    ∧ (p 0 % 2 ≠ 0 ∧ p 1 % 2 ≠ 0)
    -- Minus phase mod 3: all r scraped
    ∧ (p 6 % 3 ≠ 0 ∧ p 1 % 3 ≠ 0 ∧ p 2 % 3 ≠ 0)
    -- Minus phase mod 13: all 13 r scraped (sampled at 4 of them)
    ∧ (p 0 % 13 ≠ 0 ∧ p 3 % 13 ≠ 0 ∧ p 7 % 13 ≠ 0 ∧ p 12 % 13 ≠ 0) := by
  decide

/-! ## Epistemic status

The general theorem "the only special primes are {5, 7, 11}" is
wall-blocked — it follows from Serre's theorem on mod-ℓ Galois
representations attached to Ramanujan's τ-function. Ring-extension +
category-machinery.

What this module reconstructs:

- **Plus phase**: three specific primes admit a Ramanujan congruence.
  Witnessed with 3 depths × 3 congruences = 9 positive witnesses.
- **Minus phase**: three non-special primes (2, 3, 13) each fail to
  admit a congruence at any residue. Witnessed by scraping EVERY
  residue in `{0, ..., m-1}` and exhibiting a concrete `n` for each.

The span between plus and minus is dense: 9 positives vs 18 scrapes.
The shape of "which primes are special" is reconstructed as far as
this module can reach — all we haven't done is show that 17, 19, 23,
… all fail (scrape-bound grows with modulus).

## The god-formula reading

Under the `GodFormulaPhaseManifestations` schema: the minus phase
carries the deficit (residue fails, p(m·n + r) ≢ 0), and the plus phase
carries the residue (r exists, congruence holds). The clinamen here is
the existence of *some* `r` making the congruence work — a positive
witness of a specific departure, not an arbitrary positive.

The non-trivial element of the plus phase isn't `+1` directly; it's
the *existence of a specific r*. This is a generalized clinamen —
a "specific departure" that the minus phase cannot produce for any
candidate. The god formula's two-piece structure generalizes: `-1`
becomes "no r works", `+1` becomes "this r works".
-/

end RamanujanTripletPhase
end BuleyeanMath
