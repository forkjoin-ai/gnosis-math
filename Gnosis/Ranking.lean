import Init

/-!
# Ranking — order-theoretic core, aggregation witnesses, and comparison dynamics

This module mechanizes a **small but honest** slice of the mathematics of ranking:

- **Posets / total orders** as predicate-level axioms (reflexivity, antisymmetry, transitivity, totality).
- **Total preorders** (“weak orders” / tie-permitting rankings): the indifference relation is an equivalence
  whose classes are totally ordered against each other.
- **Condorcet paradox** on three voters and three alternatives: pairwise majority preferences form a directed
  3-cycle (the classical “rock–paper–scissors” profile).
- **Kendall tau distance** on `Fin 3` permutations as a **pairwise disagreement count** (the `Fin 3`
  specialization of the Kemeny / Kendall viewpoint).
- **Bradley–Terry** win odds as a **positive rational encoded in `Nat`** (`πᵢ` vs `πᵢ + πⱼ`) plus a
  cross-multiplication monotonicity lemma in `πᵢ` at fixed `πⱼ`.
- **Elo-style update** as an integer step `sᵢ ← sᵢ + η * (o - p)` with `p` the modeled win probability
  expressed as a scaled integer rounding (`pScaled`).

What is **not** here (and would require a heavier library stack): full Arrow / Gibbard–Satterthwaite
machinery over arbitrary finite electorates, spectral PageRank on large sparse graphs, or Kemeny
optimality / feedback-arc-set NP-hardness proofs. Those are named as **ledger boundaries** in
`open-source/gnosis/FORMAL_LEDGER.md`.
-/

namespace Gnosis
namespace Ranking

variable {α : Type u}

/-- Preorder / quasi-order: reflexive + transitive. -/
structure PreorderS (R : α → α → Prop) : Prop where
  refl : ∀ a, R a a
  trans : ∀ a b c, R a b → R b c → R a c

/-- Partial order (poset): preorder + antisymmetry. -/
structure PartialOrderS (R : α → α → Prop) : Prop where
  toPreorder : PreorderS R
  antisymm : ∀ a b, R a b → R b a → a = b

/-- Total (linear) order: partial order + totality. -/
structure TotalOrderS (R : α → α → Prop) : Prop where
  toPartial : PartialOrderS R
  total : ∀ a b, R a b ∨ R b a

/-- Indifference relation induced by any relation. -/
def Indiff (R : α → α → Prop) (a b : α) : Prop :=
  R a b ∧ R b a

theorem indiff_symm (R : α → α → Prop) (a b : α) : Indiff R a b → Indiff R b a := by
  intro h
  exact ⟨h.2, h.1⟩

theorem indiff_refl_of_refl (R : α → α → Prop) (hR : ∀ a, R a a) (a : α) : Indiff R a a :=
  ⟨hR a, hR a⟩

theorem indiff_trans_of_trans (R : α → α → Prop)
    (hT : ∀ a b c, R a b → R b c → R a c) {a b c : α}
    (hab : Indiff R a b) (hbc : Indiff R b c) : Indiff R a c := by
  refine ⟨hT a b c hab.1 hbc.1, hT c b a hbc.2 hab.2⟩

/-- Total preorder: preorder + pairwise comparability. -/
structure TotalPreorderS (R : α → α → Prop) : Prop where
  toPreorder : PreorderS R
  total : ∀ a b, R a b ∨ R b a

/-- On a total preorder, indifference is transitive (hence an equivalence when reflexivity holds). -/
theorem indiff_equivalence_of_total_preorder (R : α → α → Prop) (h : TotalPreorderS R) :
    (∀ a, Indiff R a a) ∧ (∀ a b, Indiff R a b → Indiff R b a) ∧
      (∀ a b c, Indiff R a b → Indiff R b c → Indiff R a c) :=
  ⟨indiff_refl_of_refl R h.toPreorder.refl,
    indiff_symm R,
    fun _ _ _ hab hbc => indiff_trans_of_trans R h.toPreorder.trans hab hbc⟩

/-- Strict preorder: irreflexive + transitive. -/
structure StrictPreorderS (S : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬ S a a
  trans : ∀ a b c, S a b → S b c → S a c

theorem strict_asymmetric (S : α → α → Prop) (h : StrictPreorderS S) (a b : α) :
    S a b → ¬ S b a := by
  intro hab hba
  exact h.irrefl _ (h.trans a b a hab hba)

/-! ## `Fin 3` rankings, Condorcet cycle, Kendall distance -/

abbrev Alt3 := Fin 3
abbrev Voter3 := Fin 3

/-- Cyclic Condorcet profile: voter 0 ranks `0 < 1 < 2`, voter 1 ranks `1 < 2 < 0`, voter 2 ranks `2 < 0 < 1`
(lower is better). -/
def cyclicRank (v : Voter3) (a : Alt3) : Nat :=
  match v with
  | ⟨0, _⟩ =>
    match a with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2
  | ⟨1, _⟩ =>
    match a with
    | ⟨0, _⟩ => 2
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 1
  | ⟨2, _⟩ =>
    match a with
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => 2
    | ⟨2, _⟩ => 0

/-- `a` is strictly preferred to `b` by voter `v` in the cyclic profile (decidable). -/
def voterStrictPref (v : Voter3) (a b : Alt3) : Bool :=
  decide (cyclicRank v a < cyclicRank v b)

def voterPrefersCount (a b : Alt3) : Nat :=
  (if voterStrictPref ⟨0, by decide⟩ a b then 1 else 0) +
    (if voterStrictPref ⟨1, by decide⟩ a b then 1 else 0) +
      (if voterStrictPref ⟨2, by decide⟩ a b then 1 else 0)

/-- Majority: at least 2 of 3 voters strictly prefer `a` over `b` (decidable `Bool` carrier). -/
def majorityPrefers (a b : Alt3) : Bool :=
  decide (voterPrefersCount a b ≥ 2)

theorem majority_cycle_0_1 : majorityPrefers (⟨0, by decide⟩ : Alt3) (⟨1, by decide⟩ : Alt3) = true := by
  native_decide

theorem majority_cycle_1_2 : majorityPrefers (⟨1, by decide⟩ : Alt3) (⟨2, by decide⟩ : Alt3) = true := by
  native_decide

theorem majority_cycle_2_0 : majorityPrefers (⟨2, by decide⟩ : Alt3) (⟨0, by decide⟩ : Alt3) = true := by
  native_decide

theorem voter_prefers_count_0_2 : voterPrefersCount (⟨0, by decide⟩ : Alt3) (⟨2, by decide⟩ : Alt3) = 1 := by
  native_decide

/-- The induced majority tournament is **not** transitive: `0` beats `1` and `1` beats `2` but `0` does
not beat `2` under majority (in fact `2` beats `0`). -/
theorem majority_not_transitive :
    majorityPrefers (⟨0, by decide⟩ : Alt3) (⟨1, by decide⟩ : Alt3) = true ∧
      majorityPrefers (⟨1, by decide⟩ : Alt3) (⟨2, by decide⟩ : Alt3) = true ∧
        majorityPrefers (⟨0, by decide⟩ : Alt3) (⟨2, by decide⟩ : Alt3) = false := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  unfold majorityPrefers
  rw [voter_prefers_count_0_2]
  native_decide

/-- Bool XOR: disagreement on a single unordered pair `{x,y}`. -/
def boolXor (a b : Bool) : Bool :=
  match a, b with
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

def boolXorToNat (a b : Bool) : Nat :=
  if boolXor a b then 1 else 0

theorem bool_xor_toNat_self (b : Bool) : boolXorToNat b b = 0 := by
  cases b <;> rfl

/-- Kendall / Kemeny-style pairwise disagreement count between two strict total orders on `Fin 3`,
encoded as rank functions `r` (lower is better). -/
def kendallTauDisagreements (r₁ r₂ : Alt3 → Nat) : Nat :=
  boolXorToNat (decide (r₁ ⟨0, by decide⟩ < r₁ ⟨1, by decide⟩)) (decide (r₂ ⟨0, by decide⟩ < r₂ ⟨1, by decide⟩)) +
    boolXorToNat (decide (r₁ ⟨0, by decide⟩ < r₁ ⟨2, by decide⟩)) (decide (r₂ ⟨0, by decide⟩ < r₂ ⟨2, by decide⟩)) +
      boolXorToNat (decide (r₁ ⟨1, by decide⟩ < r₁ ⟨2, by decide⟩)) (decide (r₂ ⟨1, by decide⟩ < r₂ ⟨2, by decide⟩))

theorem kendall_self_zero (r : Alt3 → Nat) : kendallTauDisagreements r r = 0 := by
  simp [kendallTauDisagreements, bool_xor_toNat_self, Nat.add_zero]

/-! ## Bradley–Terry (positive `Nat` strengths, cross-multiplication form) -/

theorem bradley_terry_cross_mul {πi πj πi' : Nat} (hj : 0 < πj) (hmono : πi < πi') :
    πi * (πi' + πj) < πi' * (πi + πj) := by
  have h₁ : πi * πj < πi' * πj := Nat.mul_lt_mul_of_pos_right hmono hj
  have h₂ : πi * πi' + πi * πj < πi * πi' + πi' * πj := Nat.add_lt_add_left h₁ (πi * πi')
  have h₃ : πi * (πi' + πj) = πi * πi' + πi * πj := by rw [Nat.mul_add]
  have h₄ : πi' * (πi + πj) = πi * πi' + πi' * πj := by
    rw [Nat.mul_add, Nat.mul_comm πi' πi, Nat.mul_comm πi' πj]
  rw [h₃, h₄]
  exact h₂

/-- Model probability scale `pScaled = round(scale * πᵢ / (πᵢ + πⱼ))` with **`scale = πᵢ + πⱼ`**, so
`pScaled = πᵢ` exactly (exact rational lift to integers, no rounding error). -/
def btWinScaled (πi πj : Nat) (_hπi : 0 < πi) (_hπj : 0 < πj) : Nat :=
  πi

theorem bt_win_scaled_lt_denom (πi πj : Nat) (hπi : 0 < πi) (hπj : 0 < πj) :
    btWinScaled πi πj hπi hπj < πi + πj :=
  Nat.lt_add_of_pos_right hπj

/-! ## Elo-style update on scaled integers -/

/-- `pScaled` is the modeled win probability in the same units as `outcomeScaled` (e.g. both in
`0‥scale` when using a fixed-point scaling of the Bradley–Terry probability). -/
def eloScoreUpdate (s η pScaled outcomeScaled : Int) : Int :=
  s + η * (outcomeScaled - pScaled)

theorem int_sub_add_cancel (o p : Int) : (o - p) + (p - o) = 0 := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_assoc o (-p) (p + -o), Int.neg_add_cancel_left,
    Int.add_right_neg]

theorem elo_update_swapped_outcomes_cancel (s η p o : Int) :
    eloScoreUpdate s η p o + eloScoreUpdate s η o p = 2 * s := by
  unfold eloScoreUpdate
  -- Reassociate `(s + η*(o-p)) + (s + η*(p-o))` into `((s + η*(o-p)) + s) + η*(p-o)`
  rw [← Int.add_assoc (s + η * (o - p)) s (η * (p - o))]
  have hmid : s + η * (o - p) + s = (s + s) + η * (o - p) := by
    rw [Int.add_assoc s (η * (o - p)) s, Int.add_comm (η * (o - p)) s, ← Int.add_assoc]
  rw [hmid, Int.add_assoc (s + s) (η * (o - p)) (η * (p - o)), ← Int.mul_add η (o - p) (p - o),
    int_sub_add_cancel o p, Int.mul_zero, Int.add_zero, Int.two_mul]

/-! ## Ledger hook: Arrow-style “three desiderata cannot all fit” (same counting skeleton as `MechanismDesign.impossibility`) -/

theorem ranking_impossibility_count (desired achieved : Nat)
    (hDesired : desired = 3) (hAchieved : achieved ≤ 2) : desired > achieved := by
  rw [hDesired]
  exact Nat.lt_of_le_of_lt hAchieved (by decide : (2 : Nat) < 3)

end Ranking
end Gnosis
