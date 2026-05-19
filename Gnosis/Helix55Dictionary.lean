import Gnosis.Braided.BraidedInfinity

/-!
# Helix-55 Rotation Dictionary

The knotchain wire format runs a 54-strand columnar helix
(`bitwise/knotchain-helix.ts`, `weave54Helix`). Adding a single
parity strand gives a 55-position structure on which the cyclic
group `ℤ/55ℤ` acts transitively.

55 is the highest gnostic-numerical domain, and is the natural
shape for a rotation dictionary over the helix: every position
is reachable from every other by exactly one rotation in
`[0, 55)`. Data on the helix is encoded as
`(rotation : [0, 55))` (≈ 5.78 bits) plus a small residual,
collapsing distance the same way ER=EPR collapses spatial
distance into entanglement structure.

## Theorems in this module

1. `iterateSucc_succ_eq_addMod` (helper) — the generic period
   lemma: `iterateSucc n (m+1) i = (i + 1 + m) % n` for any `n`.
2. `helix55_period_55` — 55 rotations return to start, on
   every position `i < 55`. The dictionary closes.
3. `helix55_no_period_at_zero` — for `0 < k < 55`,
   `iterateSucc 55 k 0 ≠ 0`. Genuine 55-cycle, not a sub-cycle.
4. `helix55_transitive` — for any `p, q < 55`, there exists
   `k < 55` with `iterateSucc 55 k p = q`. Every entry is reachable.
5. `helix55_encode_decode` — rotating `p` by `helixDistance p q`
   gives `q`. The dictionary is invertible.
6. `helix54_plus_parity_covers_55` — the 54 helix strands plus
   the parity strand exhaust `[0, 55)`. Bridge to
   `bitwise/knotchain-helix.ts`.
7. `helix55Braid` — the 55-position cycle as a
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
    have h1 : (i + 1) % n + 1 + k = (i + 1) % n + (1 + k) := Nat.add_assoc _ 1 k
    rw [h1, mod_add_left]
    congr 1
    -- (i + 1) + (1 + k) = i + 1 + (k + 1) — by add_comm on the inner pair.
    rw [Nat.add_comm 1 k]

/-! ## Period-55 return: the dictionary closes -/

theorem helix55_period_55 (i : Nat) (hi : i < 55) :
    iterateSucc 55 55 i = i := by
  have h := iterateSucc_succ_eq_addMod 55 54 i
  show iterateSucc 55 (54 + 1) i = i
  rw [h]
  -- i + 1 + 54 = i + 55: associativity (1 + 54 = 55).
  have h2 : i + 1 + 54 = i + 55 := by
    rw [Nat.add_assoc]
  rw [h2]
  -- (i + 55) % 55 = i % 55 = i (since i < 55).
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]

/-! ## No shorter period at zero: genuine 55-cycle -/

theorem helix55_no_period_at_zero (k : Nat) (hk_pos : 0 < k) (hk_lt : k < 55) :
    iterateSucc 55 k 0 ≠ 0 := by
  have hk_succ : k = (k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
  rw [hk_succ]
  rw [iterateSucc_succ_eq_addMod 55 (k - 1) 0]
  -- 0 + 1 + (k - 1) = 1 + (k - 1) = k.
  have h : 0 + 1 + (k - 1) = k := by
    rw [Nat.zero_add, Nat.add_comm 1 (k - 1), Nat.sub_add_cancel hk_pos]
  rw [h]
  rw [Nat.mod_eq_of_lt hk_lt]
  -- k ≠ 0 from 0 < k.
  exact Nat.pos_iff_ne_zero.mp hk_pos

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
    -- (q + 55 - p) % 55 = 0 with p, q < 55 forces q + 55 - p = 55, hence p = q.
    -- The divisibility argument: q + 55 - p ∈ (0, 110), only multiple of 55 is 55.
    have hDvd : 55 ∣ (q + 55 - p) := Nat.dvd_of_mod_eq_zero hk_zero
    have hpLeQ55 : p ≤ q + 55 := Nat.le_trans (Nat.le_of_lt hp) (Nat.le_add_left 55 q)
    -- q + 55 - p > 0 (since p < 55 ≤ q + 55, and we have hp).
    have hPos : 0 < q + 55 - p := Nat.sub_pos_of_lt
      (Nat.lt_of_lt_of_le hp (Nat.le_add_left 55 q))
    -- q + 55 - p < 110 (since q + 55 < 55 + 55 = 110).
    have hLt110 : q + 55 - p < 110 := Nat.lt_of_le_of_lt
      (Nat.sub_le (q + 55) p)
      (Nat.add_lt_add_right hq 55)
    -- The only multiple of 55 in (0, 110) is 55.
    obtain ⟨k, hkEq⟩ := hDvd
    -- k must be 1.
    have hkPos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkp
      · exfalso; rw [hk0, Nat.mul_zero] at hkEq; exact Nat.lt_irrefl 0 (hkEq ▸ hPos)
      · exact hkp
    have hkLt2 : k < 2 := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · exact hlt
      · exfalso
        have : 110 ≤ q + 55 - p := by
          rw [hkEq]
          exact Nat.le_trans (by decide : (110 : Nat) ≤ 55 * 2) (Nat.mul_le_mul_left 55 hge)
        exact absurd this (Nat.not_le_of_lt hLt110)
    have hkOne : k = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hkLt2) hkPos
    rw [hkOne, Nat.mul_one] at hkEq
    -- hkEq : q + 55 - p = 55. With p ≤ q + 55: q + 55 - p = 55 ⇒ q = p.
    have : q + 55 = p + 55 := by
      have hAdd : (q + 55 - p) + p = 55 + p := by rw [hkEq]
      rw [Nat.sub_add_cancel hpLeQ55] at hAdd
      rw [hAdd, Nat.add_comm 55 p]
    exact (Nat.add_right_cancel this).symm
  · have hk_pos : 0 < (q + 55 - p) % 55 := Nat.pos_of_ne_zero hk_zero
    have hk_lt : (q + 55 - p) % 55 < 55 := Nat.mod_lt _ (by decide)
    have hk_succ : (q + 55 - p) % 55 = ((q + 55 - p) % 55 - 1) + 1 :=
      (Nat.sub_add_cancel hk_pos).symm
    rw [hk_succ]
    rw [iterateSucc_succ_eq_addMod 55 ((q + 55 - p) % 55 - 1) p]
    have h1 : p + 1 + ((q + 55 - p) % 55 - 1) = p + (q + 55 - p) % 55 := by
      rw [Nat.add_assoc, Nat.add_comm 1 _, Nat.sub_add_cancel hk_pos]
    rw [h1]
    rw [add_mod_right]
    have hpLeQ55 : p ≤ q + 55 :=
      Nat.le_trans (Nat.le_of_lt hp) (Nat.le_add_left 55 q)
    have h2 : p + (q + 55 - p) = q + 55 := Nat.add_sub_of_le hpLeQ55
    rw [h2]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hq]

theorem helix55_transitive (p q : Nat) (hp : p < 55) (hq : q < 55) :
    ∃ k, k < 55 ∧ iterateSucc 55 k p = q :=
  ⟨helixDistance p q, helixDistance_lt_55 p q, helix55_encode_decode p q hp hq⟩

theorem helix55_distance_self (p : Nat) (_hp : p < 55) :
    helixDistance p p = 0 := by
  unfold helixDistance
  have h : p + 55 - p = 55 := Nat.add_sub_cancel_left p 55
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

theorem helixStrands_all_lt_55 (s : Nat) (hs : s ∈ helixStrands) : s < 55 :=
  Nat.lt_of_lt_of_le (helixStrands_all_lt_54 s hs) (by decide : (54 : Nat) ≤ 55)

theorem helixParity_distinct_from_strands (s : Nat) (hs : s ∈ helixStrands) :
    s ≠ helixParity := by
  unfold helixParity
  exact Nat.ne_of_lt (helixStrands_all_lt_54 s hs)

theorem helix54_plus_parity_covers_55 (i : Nat) (hi : i < 55) :
    i ∈ helixStrands ∨ i = helixParity := by
  unfold helixStrands helixParity
  by_cases h : i < 54
  · left
    exact List.mem_range.mpr h
  · right
    -- ¬(i < 54) ⇒ 54 ≤ i; combined with i < 55 ⇒ i = 54.
    exact Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.le_of_not_lt h)

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
