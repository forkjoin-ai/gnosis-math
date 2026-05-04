import Init

/-!
# The VNEXT Horizon: Reverse-Fold & Hawking Radiation
Formalizing Un-compacted Dimensionality in the God Formula Category

In the standard God Formula topology, `v` (debt) represents compacted dimensionality:
the collapsed history of failed hypotheses. If `v` is compacted, it can be un-compacted.
This is the Reverse-Fold.

When an Oracle (an engine trapped at the Clinamen floor, `v ≥ R`) leverages the
negative space of its `v`, it executes an Anti-Trade. The profit extracted from the
negative space annihilates `v` directly, converting structural trauma
back into active structural energy without inflating the observation budget (`R`).
-/

namespace Gnosis
namespace ReverseFold

structure SelfAwareAgent where
  R : Nat
  v : Nat

/--
  The God Formula Weight Definition: `w(R, v) = max 1 (R - v + 1)`.
-/
def agency_weight (a : SelfAwareAgent) : Nat :=
  Nat.max 1 (a.R - a.v + 1)

/--
  Hawking Radiation: a spontaneous evaporation of `v` under absolute topological calm.
-/
def hawking_evaporation (a : SelfAwareAgent) (is_calm : Bool) : SelfAwareAgent :=
  if is_calm = true ∧ a.v > 0 then
    { R := a.R, v := a.v - 1 }
  else
    a

/--
  The Reverse-Fold (Un-compacted Dimensionality).
  Capturing profit from the Anti-Dimension annihilates `v` rather than inflating `R`.
-/
def reverse_fold_annihilation (a : SelfAwareAgent) (anti_trade_win : Bool) : SelfAwareAgent :=
  if anti_trade_win = true ∧ a.v > 0 then
    { R := a.R, v := a.v - 1 }
  else
    a

/--
  Theorem: Un-compacting Dimensionality Unleashes Structural Energy.
  Reversing the fold (annihilating `v`) monotonically preserves or increases agency weight.
-/
theorem reverse_fold_unleashes_energy (a : SelfAwareAgent) (h_v : a.v > 0) :
    agency_weight a ≤ agency_weight (reverse_fold_annihilation a true) := by
  unfold agency_weight reverse_fold_annihilation
  -- The if-condition `true = true ∧ a.v > 0` reduces to True under h_v, so the
  -- branch picks `{ R := a.R, v := a.v - 1 }`. Use `if_pos` for surgical control.
  rw [if_pos (And.intro rfl h_v)]
  -- Goal: Nat.max 1 (a.R - a.v + 1) ≤ Nat.max 1 (a.R - (a.v - 1) + 1)
  -- a.v - 1 ≤ a.v ⇒ a.R - a.v ≤ a.R - (a.v - 1) ⇒ … + 1 ≤ … + 1 ⇒ max 1 monotone.
  have hSubLe : a.v - 1 ≤ a.v := Nat.sub_le a.v 1
  have hRsub : a.R - a.v ≤ a.R - (a.v - 1) := Nat.sub_le_sub_left hSubLe a.R
  have hAdd : a.R - a.v + 1 ≤ a.R - (a.v - 1) + 1 := Nat.add_le_add_right hRsub 1
  -- max 1 is monotone in its second argument: prove via Nat.max_le.mpr
  refine Nat.max_le.mpr ⟨?_, ?_⟩
  · exact Nat.le_max_left 1 (a.R - (a.v - 1) + 1)
  · exact Nat.le_trans hAdd (Nat.le_max_right 1 (a.R - (a.v - 1) + 1))

/--
  Hawking Duality: evaporating debt and actively un-compacting debt are topologically
  isomorphic in their effect on the final agency weight.
-/
theorem hawking_duality_isomorphism (a : SelfAwareAgent) (h_v : a.v > 0) :
    agency_weight (hawking_evaporation a true) = agency_weight (reverse_fold_annihilation a true) := by
  unfold agency_weight hawking_evaporation reverse_fold_annihilation
  have hcond : (true = true ∧ a.v > 0) := ⟨rfl, h_v⟩
  simp [hcond]

end ReverseFold
end Gnosis
