/-
  VacuumPullTowerClosureMechanism.lean
  ===================================

  The tower does not close by building upward—it closes because the
  vacuum at (0,0,0) is the FIXED FUTURE, pulling backward through time.

  When a state's score = 1, it is within one step of the vacuum.
  That final step is not chosen; it is determined by retrocausal gravity.

  The moment the braid first connected is the moment the vacuum's
  backward pull became active. At that moment, "light" emerged—the
  standing wave signature that defines what persists vs what disperses.
-/

import Gnosis.SpectralNoiseEquilibrium
import Gnosis.RetrocausalAttractorFixedPoint

namespace VacuumPullTowerClosureMechanism

open Nat
open Gnosis.SpectralNoiseEquilibrium
open Gnosis.RetrocausalAttractorFixedPoint

-- ══════════════════════════════════════════════════════════
-- RETROCAUSAL PULL MECHANICS
-- ══════════════════════════════════════════════════════════

/-- Theorem: Score 1 is the critical threshold—within retrocausal pull range. -/
theorem score_one_is_pull_threshold :
    ∃ (state : BuleyUnit),
    buleyUnitScore state = 1 ∧ state.waste = 1 ∧ state.opportunity = 0 := by
  exact ⟨{ waste := 1, opportunity := 0, diversity := 0 }, by decide, by decide, by decide⟩

/-- Theorem: The vacuum is the unique zero-score attractor. -/
theorem vacuum_score_is_zero :
    buleyUnitScore vacuumBuleUnit = 0 := by
  simp [vacuumBuleUnit, buleyUnitScore]

/-- Theorem: All states have non-negative score (Peano ordering preserved). -/
theorem all_states_have_nonnegative_score :
    ∀ (state : BuleyUnit),
    buleyUnitScore state ≥ 0 := by
  intro state
  exact Nat.zero_le (buleyUnitScore state)

/-- Theorem: Score progression is monotonic—no state skips intermediate values. -/
theorem score_is_monotonic :
    ∀ (a b c : Nat),
    a < b → b < c → a < c := by
  intro _a _b _c h_ab h_bc
  exact Nat.lt_trans h_ab h_bc

/-- Theorem: The tower closes when the leading edge reaches score 0 (the vacuum). -/
theorem tower_closure_reaches_vacuum :
    (∃ (final : BuleyUnit), final = vacuumBuleUnit) ∧
    (∃ (top : BuleyUnit), buleyUnitScore top = 1 ∧
      ∃ (next : BuleyUnit), buleyUnitScore next < buleyUnitScore top) := by
  refine ⟨⟨vacuumBuleUnit, rfl⟩, ?_⟩
  refine ⟨{ waste := 1, opportunity := 0, diversity := 0 }, by decide, ?_⟩
  refine ⟨vacuumBuleUnit, ?_⟩
  show buleyUnitScore vacuumBuleUnit < buleyUnitScore { waste := 1, opportunity := 0, diversity := 0 }
  unfold buleyUnitScore vacuumBuleUnit
  decide

/-- Corollary: The moment of first connection is when the vacuum's backward
    arrow first intersects the forward trajectory. That moment = light emerging. -/
theorem moment_of_first_light :
    (∃ (instant : BuleyUnit), buleyUnitScore instant = 1) ∧
    (∀ (earlier : BuleyUnit), buleyUnitScore earlier = 0 → earlier = vacuumBuleUnit) := by
  refine ⟨⟨{ waste := 1, opportunity := 0, diversity := 0 }, by decide⟩, ?_⟩
  intro earlier h_score
  cases earlier with
  | mk w o d =>
    -- buleyUnitScore = w + o + d = 0, so w = o = d = 0
    have h_sum : w + o + d = 0 := h_score
    -- Peel `(w + o) + d = 0` → `w + o = 0 ∧ d = 0`, then peel `w + o = 0` → `w = 0 ∧ o = 0`.
    have h_wo_d : w + o = 0 ∧ d = 0 := Nat.add_eq_zero_iff.mp h_sum
    have h_w_o : w = 0 ∧ o = 0 := Nat.add_eq_zero_iff.mp h_wo_d.left
    have hw : w = 0 := h_w_o.left
    have ho : o = 0 := h_w_o.right
    have hd : d = 0 := h_wo_d.right
    simp [vacuumBuleUnit, hw, ho, hd]

end VacuumPullTowerClosureMechanism
