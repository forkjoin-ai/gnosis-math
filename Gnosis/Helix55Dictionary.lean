import Gnosis.Braided.BraidedInfinity


/-!
# Helix-55 Rotation Dictionary

The knotchain wire format runs a 54-strand columnar helix
(`bitwise/knotchain-helix.ts`, `weave54Helix`). Adding a single
parity strand gives a 55-position structure on which the cyclic
group `ℤ/55ℤ` acts transitively.

55 is the highest gnostic-numerical domain, and is the natural
shape for a **rotation dictionary** over the helix: every position
is reachable from every other by exactly one rotation in
`[0, 55)`. Data on the helix is encoded as
`(rotation : [0, 55))` (≈ 5.78 bits) plus a small residual,
collapsing distance the same way ER=EPR collapses spatial
distance into entanglement structure.

## Theorems in this module

1. **`iterateSucc_succ_eq_addMod`** (helper) — the generic period
   lemma: `iterateSucc n (m+1) i = (i + 1 + m) % n` for any `n`.
2. **`helix55_period_55`** — 55 rotations return to start, on
   every position `i < 55`. The dictionary closes.
3. **`helix55_no_period_at_zero`** — for `0 < k < 55`,
   `iterateSucc 55 k 0 ≠ 0`. Genuine 55-cycle, not a sub-cycle.
4. **`helix55_transitive`** — for any `p, q < 55`, there exists
   `k < 55` with `iterateSucc 55 k p = q`. Every entry is reachable.
5. **`helix55_encode_decode`** — rotating `p` by `helixDistance p q`
   gives `q`. The dictionary is invertible.
6. **`helix54_plus_parity_covers_55`** — the 54 helix strands plus
   the parity strand exhaust `[0, 55)`. Bridge to
   `bitwise/knotchain-helix.ts`.
7. **`helix55Braid`** — the 55-position cycle as a
   `BraidedAsymptote`, with descriptor list of length 55.

`import Init` (transitively, via `Gnosis.BraidedInfinity`) only.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace Helix55Dictionary

open Gnosis.BraidedInfinity (BraidedAsymptote iterateSucc)

/-! ## Phase count: 54 helix strands + 1 parity strand -/

/-- The total number of helix-with-parity positions. -/
def helix55Count : Nat := 55

theorem helix55Count_eq_54_plus_1 : helix55Count = 54 + 1 := rfl
theorem helix55Count_pos : 0 < helix55Count := by decide

/-! ## Generic period lemma

After `m + 1` clinamen steps starting from any `i`, the result
is `(i + 1 + m) mod n`. This collapses 55 individual `decide`
proofs into one inductive argument. -/

private theorem mod_add_left (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private theorem add_mod_right (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private theorem iterateSucc_succ_eq_addMod (n : Nat) :
    ∀ m i, iterateSucc n (m + 1) i = (i + 1 + m) % n := by
  intro m
  induction m with
  | zero =>
    intro i
    show (i + 1) % n = (i + 1 + 0) % n
    congr 1
  | succ k ih =>
    intro i
    show iterateSucc n (k + 1) ((i + 1) % n) = (i + 1 + (k + 1)) % n
    rw [ih ((i + 1) % n)]
    have h1 : (i + 1) % n + 1 + k = (i + 1) % n + (1 + k) := by omega
    rw [h1, mod_add_left]
    congr 1
    omega

/-! ## Period-55 return: the dictionary closes -/

theorem helix55_period_55 (i : Nat) (hi : i < 55) :
    iterateSucc 55 55 i = i := by
  have h := iterateSucc_succ_eq_addMod 55 54 i
  show iterateSucc 55 (54 + 1) i = i
  rw [h]
  have h2 : i + 1 + 54 = i + 55 := by omega
  rw [h2]
  omega

/-! ## No shorter period at zero: genuine 55-cycle -/

theorem helix55_no_period_at_zero (k : Nat) (hk_pos : 0 < k) (hk_lt : k < 55) :
    iterateSucc 55 k 0 ≠ 0 := by
  have hk_succ : k = (k - 1) + 1 := by omega
  rw [hk_succ]
  rw [iterateSucc_succ_eq_addMod 55 (k - 1) 0]
  have h : 0 + 1 + (k - 1) = k := by omega
  rw [h]
  rw [Nat.mod_eq_of_lt hk_lt]
  omega

/-! ## Transitivity: every position reaches every other -/

/-- Rotation distance from `p` to `q`: the unique `k ∈ [0, 55)`
with `iterateSucc 55 k p = q` (when `p, q < 55`). -/
def helixDistance (p q : Nat) : Nat := (q + 55 - p) % 55

theorem helixDistance_lt_55 (p q : Nat) : helixDistance p q < 55 := by
  unfold helixDistance
  exact Nat.mod_lt _ (by decide)

theorem helix55_encode_decode (p q : Nat) (hp : p < 55) (hq : q < 55) :
    iterateSucc 55 (helixDistance p q) p = q := by
  unfold helixDistance
  by_cases hk_zero : (q + 55 - p) % 55 = 0
  · rw [hk_zero]
    show p = q
    omega
  · have hk_pos : 0 < (q + 55 - p) % 55 := Nat.pos_of_ne_zero hk_zero
    have hk_lt : (q + 55 - p) % 55 < 55 := Nat.mod_lt _ (by decide)
    have hk_succ : (q + 55 - p) % 55 = ((q + 55 - p) % 55 - 1) + 1 := by omega
    rw [hk_succ]
    rw [iterateSucc_succ_eq_addMod 55 ((q + 55 - p) % 55 - 1) p]
    have h1 : p + 1 + ((q + 55 - p) % 55 - 1) = p + (q + 55 - p) % 55 := by omega
    rw [h1]
    rw [add_mod_right]
    have h2 : p + (q + 55 - p) = q + 55 := by omega
    rw [h2]
    omega

theorem helix55_transitive (p q : Nat) (hp : p < 55) (hq : q < 55) :
    ∃ k, k < 55 ∧ iterateSucc 55 k p = q :=
  ⟨helixDistance p q, helixDistance_lt_55 p q, helix55_encode_decode p q hp hq⟩

theorem helix55_distance_self (p : Nat) (_hp : p < 55) :
    helixDistance p p = 0 := by
  unfold helixDistance
  have h : p + 55 - p = 55 := by omega
  rw [h]

/-! ## 54 strands + 1 parity partition -/

/-- The 54 knotchain helix strands, indexed `0..53`. -/
def helixStrands : List Nat := List.range 54

/-- The parity strand: position 54, the +1 above the 54-helix that
closes the dictionary into a 55-cycle. -/
def helixParity : Nat := 54

theorem helixStrands_length : helixStrands.length = 54 := by
  unfold helixStrands
  decide

theorem helixParity_lt_55 : helixParity < 55 := by decide

theorem helixStrands_all_lt_54 (s : Nat) (hs : s ∈ helixStrands) : s < 54 := by
  unfold helixStrands at hs
  exact List.mem_range.mp hs

theorem helixStrands_all_lt_55 (s : Nat) (hs : s ∈ helixStrands) : s < 55 := by
  have := helixStrands_all_lt_54 s hs
  omega

theorem helixParity_distinct_from_strands (s : Nat) (hs : s ∈ helixStrands) :
    s ≠ helixParity := by
  have := helixStrands_all_lt_54 s hs
  unfold helixParity
  omega

theorem helix54_plus_parity_covers_55 (i : Nat) (hi : i < 55) :
    i ∈ helixStrands ∨ i = helixParity := by
  unfold helixStrands helixParity
  by_cases h : i < 54
  · left
    exact List.mem_range.mpr h
  · right
    omega

/-! ## BraidedAsymptote bridge -/

def helix55Braid : BraidedAsymptote :=
  { phaseCount := 55
    descriptors :=
      ["s0",  "s1",  "s2",  "s3",  "s4",  "s5",  "s6",  "s7",  "s8",  "s9",
       "s10", "s11", "s12", "s13", "s14", "s15", "s16", "s17", "s18", "s19",
       "s20", "s21", "s22", "s23", "s24", "s25", "s26", "s27", "s28", "s29",
       "s30", "s31", "s32", "s33", "s34", "s35", "s36", "s37", "s38", "s39",
       "s40", "s41", "s42", "s43", "s44", "s45", "s46", "s47", "s48", "s49",
       "s50", "s51", "s52", "s53", "parity"] }

theorem helix55Braid_phaseCount : helix55Braid.phaseCount = 55 := rfl

theorem helix55Braid_descriptors_length :
    helix55Braid.descriptors.length = 55 := by decide

theorem helix55Braid_returns (i : Nat) (hi : i < 55) :
    iterateSucc helix55Braid.phaseCount 55 i = i :=
  helix55_period_55 i hi

theorem helix55Braid_no_shorter_period_at_zero :
    iterateSucc helix55Braid.phaseCount 1 0 ≠ 0
    ∧ iterateSucc helix55Braid.phaseCount 27 0 ≠ 0
    ∧ iterateSucc helix55Braid.phaseCount 54 0 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact helix55_no_period_at_zero 1 (by decide) (by decide)
  · exact helix55_no_period_at_zero 27 (by decide) (by decide)
  · exact helix55_no_period_at_zero 54 (by decide) (by decide)

/-! ## Compression cost: bits per dictionary index

A rotation index lives in `[0, 55)`, so it fits in `⌈log₂ 55⌉ = 6`
bits. Encoding a helix-bound datum as a rotation index therefore
costs 6 bits per datum, regardless of the datum's payload size.
This is the dictionary's compression floor. -/

def helix55_index_bit_cost : Nat := 6

theorem helix55_index_fits_in_6_bits :
    helix55Count ≤ 2 ^ helix55_index_bit_cost := by decide

theorem helix55_index_does_not_fit_in_5_bits :
    2 ^ 5 < helix55Count := by decide

end Helix55Dictionary
end Gnosis
