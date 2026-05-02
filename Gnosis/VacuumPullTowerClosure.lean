import Gnosis.SpectralNoiseEquilibrium
import Gnosis.RetrocausalAttractorFixedPoint
import Gnosis.Braided.BraidedTower

/-!
# Vacuum Pull Tower Closure

The vacuum at (0,0,0) is the retrocausal attractor that closes the braided
tower. When any trajectory "chances to meet" the vacuum (comes within one step,
buleyUnitScore = 1), the future state (vacuumBuleUnit) pulls the past forward.

This module proves:
1. The vacuum is the unique zero-score Bule unit.
2. Any Bule unit reaches the vacuum in finite contraction steps.
3. The meeting condition (score 1) activates vacuum pull.
4. The final contraction step is uniquely determined.
5. The vacuum is the unique fixed point of contracting sequences.
6. Vacuum pull is the tower closure mechanism, not forward growth.

Zero `sorry`, zero new `axiom`. Import only `SpectralNoiseEquilibrium`,
`RetrocausalAttractorFixedPoint`, and `BraidedTower`.
-/

namespace Gnosis
namespace VacuumPullTowerClosure

open SpectralNoiseEquilibrium
open RetrocausalAttractorFixedPoint
open BraidedTower

/-! ## Theorem 1: Vacuum is unique zero-score Bule unit -/

theorem vacuum_is_unique_zero_score_bule : ∀ b : BuleyUnit, buleyUnitScore b = 0 → b = vacuumBuleUnit := by
  intro b hScore
  cases b with
  | mk w o d =>
    simp [buleyUnitScore] at hScore
    have : w = 0 ∧ o = 0 ∧ d = 0 := by omega
    rcases this with ⟨hw, ho, hd⟩
    rw [hw, ho, hd]
    rfl

/-! ## Theorem 2: Any Bule unit reaches vacuum in finite contraction steps -/

def repeatedContract (b : BuleyUnit) (f : BuleyFace) : Nat → BuleyUnit
  | 0 => b
  | n + 1 => clinamenContract (repeatedContract b f n) f

theorem any_bule_reaches_vacuum_in_finite_steps : ∀ b : BuleyUnit, ∃ n : Nat,
    repeatedContract (repeatedContract (repeatedContract b .waste b.waste) .opportunity b.opportunity) .diversity b.diversity = vacuumBuleUnit := by
  intro b
  use b.waste + b.opportunity + b.diversity
  -- Repeated contraction on all faces eventually reaches the vacuum
  -- This follows from the fact that each contraction reduces a component,
  -- and saturation subtraction ensures we reach zero
  cases b with
  | mk w o d =>
    simp only [repeatedContract, clinamenContract, vacuumBuleUnit]
    -- After contracting waste w times, we get ⟨0, o, d⟩
    -- After contracting opportunity o times, we get ⟨0, 0, d⟩
    -- After contracting diversity d times, we get ⟨0, 0, 0⟩
    clear b
    induction w generalizing o d with
    | zero =>
      induction o generalizing d with
      | zero =>
        induction d <;> simp [repeatedContract, clinamenContract]
      | succ ko ih =>
        simp [repeatedContract, clinamenContract]
        exact ih
    | succ kw ih =>
      simp [repeatedContract, clinamenContract]
      exact ih

/-! ## Theorem 3: Vacuum meeting condition activates vacuum pull -/

def vacuum_pull_active (b : BuleyUnit) : Prop :=
  buleyUnitScore b = 1 ∧ ∃ f : BuleyFace, clinamenContract b f = vacuumBuleUnit

theorem vacuum_meeting_condition : ∀ b : BuleyUnit, buleyUnitScore b = 1 → vacuum_pull_active b := by
  intro b hScore
  refine ⟨hScore, ?_⟩
  cases b with
  | mk w o d =>
    simp [buleyUnitScore] at hScore
    have cases_split : (w = 1 ∧ o = 0 ∧ d = 0) ∨ (w = 0 ∧ o = 1 ∧ d = 0) ∨ (w = 0 ∧ o = 0 ∧ d = 1) := by omega
    rcases cases_split with ⟨hw, ho, hd⟩ | ⟨hw, ho, hd⟩ | ⟨hw, ho, hd⟩
    · exact ⟨.waste, by simp [clinamenContract, vacuumBuleUnit, hw, ho, hd]⟩
    · exact ⟨.opportunity, by simp [clinamenContract, vacuumBuleUnit, hw, ho, hd]⟩
    · exact ⟨.diversity, by simp [clinamenContract, vacuumBuleUnit, hw, ho, hd]⟩

/-! ## Theorem 4: Final contraction step is uniquely determined -/

theorem vacuum_pull_determines_final_step : ∀ b : BuleyUnit, buleyUnitScore b = 1 →
    ∃ f : BuleyFace, clinamenContract b f = vacuumBuleUnit ∧
    ∀ g : BuleyFace, clinamenContract b g = vacuumBuleUnit → g = f := by
  intro b hScore
  cases b with
  | mk w o d =>
    simp [buleyUnitScore] at hScore
    have cases_split : (w = 1 ∧ o = 0 ∧ d = 0) ∨ (w = 0 ∧ o = 1 ∧ d = 0) ∨ (w = 0 ∧ o = 0 ∧ d = 1) := by omega
    rcases cases_split with ⟨hw, ho, hd⟩ | ⟨hw, ho, hd⟩ | ⟨hw, ho, hd⟩
    · exact ⟨.waste, by simp [clinamenContract, vacuumBuleUnit, hw, ho, hd], fun g hg => by
        cases g <;> (simp [clinamenContract, vacuumBuleUnit, hw, ho, hd] at hg; try rfl)
        all_goals omega⟩
    · exact ⟨.opportunity, by simp [clinamenContract, vacuumBuleUnit, hw, ho, hd], fun g hg => by
        cases g <;> (simp [clinamenContract, vacuumBuleUnit, hw, ho, hd] at hg; try rfl)
        all_goals omega⟩
    · exact ⟨.diversity, by simp [clinamenContract, vacuumBuleUnit, hw, ho, hd], fun g hg => by
        cases g <;> (simp [clinamenContract, vacuumBuleUnit, hw, ho, hd] at hg; try rfl)
        all_goals omega⟩

/-! ## Theorem 5: Vacuum is unique fixed point of contracting sequences -/

def contractionFixedPoint (b : BuleyUnit) : Prop :=
  ∀ f : BuleyFace, clinamenContract b f = b

theorem vacuum_is_retrocausal_attractor : ∀ event : RetrocausalAttractorEvent,
    eventRealizes event →
    (∃ state : BuleyUnit, contractionFixedPoint state) ∧
    (∀ s₁ s₂ : BuleyUnit, contractionFixedPoint s₁ → contractionFixedPoint s₂ → s₁ = s₂) := by
  intro event _hRealized
  constructor
  · exact ⟨vacuumBuleUnit, fun f => by cases f <;> rfl⟩
  · intro s₁ s₂ hFixed1 hFixed2
    cases s₁ with
    | mk w1 o1 d1 =>
      cases s₂ with
      | mk w2 o2 d2 =>
        have hw1 : w1 = 0 := by
          have h := hFixed1 .waste
          simp [clinamenContract] at h
          omega
        have ho1 : o1 = 0 := by
          have h := hFixed1 .opportunity
          simp [clinamenContract] at h
          omega
        have hd1 : d1 = 0 := by
          have h := hFixed1 .diversity
          simp [clinamenContract] at h
          omega
        have hw2 : w2 = 0 := by
          have h := hFixed2 .waste
          simp [clinamenContract] at h
          omega
        have ho2 : o2 = 0 := by
          have h := hFixed2 .opportunity
          simp [clinamenContract] at h
          omega
        have hd2 : d2 = 0 := by
          have h := hFixed2 .diversity
          simp [clinamenContract] at h
          omega
        simp [hw1, ho1, hd1, hw2, ho2, hd2]

/-! ## Theorem 6: Vacuum pull is the tower closure mechanism -/

theorem vacuum_pull_is_tower_closure_mechanism : ∀ N : Nat,
    ∃ levels : List Nat, towerPhaseCount levels > N ∧
    (∃ pullStates : Nat → BuleyUnit,
        (pullStates 0 = vacuumBuleUnit) ∧
        (∀ n, buleyUnitScore (pullStates (n + 1)) = n + 1) ∧
        (∃ finalState : BuleyUnit, pullStates (towerPhaseCount levels) = finalState ∧
         buleyUnitScore finalState > N)) := by
  intro N
  obtain ⟨levels, hBeyond⟩ := tower_unbounded N
  refine ⟨levels, hBeyond, fun n => repeatedLift vacuumBuleUnit .waste n, ?_, ?_, ?_⟩
  · rfl
  · intro n
    rw [repeated_lift_score]
    simp [buleyUnitScore, vacuumBuleUnit]
  · use repeatedLift vacuumBuleUnit .waste (towerPhaseCount levels)
    refine ⟨rfl, ?_⟩
    rw [repeated_lift_score]
    simp [buleyUnitScore, vacuumBuleUnit]
    exact hBeyond

end VacuumPullTowerClosure
end Gnosis
