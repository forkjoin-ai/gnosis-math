-- Gnosis.Optics.PhotopigmentKinetics
-- Track Beta: Photopigment bleaching and recovery kinetics (simplified)
-- Core definitions and foundational theorems for cone recovery

import Gnosis.Optics.OpticalFoundations

namespace Gnosis.Optics.PhotopigmentKinetics

-- Recovery accumulates over time, capped at maxCapacity
def coneRecovery (cone : ConeType) (timeSteps : Nat) : Nat :=
  Nat.min cone.maxCapacity (timeSteps * cone.regenerationRate)

-- Recovery is bounded by capacity
theorem cone_recovery_bounded (cone : ConeType) (t : Nat) :
    coneRecovery cone t ≤ cone.maxCapacity := by
  unfold coneRecovery
  exact Nat.min_le_left _ _

-- Initial state: zero recovery at time zero
theorem cone_recovery_at_zero (cone : ConeType) :
    coneRecovery cone 0 = 0 := by
  unfold coneRecovery
  simp

-- Chromatic shift: max - min of three cone recoveries
def chromaticShift (sRecovery mRecovery lRecovery : Nat) : Nat :=
  Nat.max (Nat.max sRecovery mRecovery) lRecovery - Nat.min (Nat.min sRecovery mRecovery) lRecovery

-- Shift is bounded
theorem chromatic_shift_bounded (s m l : Nat) :
    chromaticShift s m l ≤ Nat.max (Nat.max s m) l := by
  unfold chromaticShift
  exact Nat.sub_le _ _

-- Thermal dissipation rate increases with intensity
def thermalDissipationRate (intensity : Nat) : Nat := intensity / 4

theorem thermal_dissipation_monotone :
    ∀ i₁ i₂ : Nat, i₁ ≤ i₂ → thermalDissipationRate i₁ ≤ thermalDissipationRate i₂ := by
  intros i₁ i₂ hle
  unfold thermalDissipationRate
  exact Nat.div_le_div_right hle

-- Lateral bloom extent (how much afterimage spreads)
def lateralBloomExtent (intensity : Nat) : Nat :=
  thermalDissipationRate intensity / 2 + 1

theorem lateral_bloom_positive (intensity : Nat) :
    lateralBloomExtent intensity ≥ 1 := by
  unfold lateralBloomExtent
  exact Nat.succ_pos _

-- Photopigment deficit model
def photopigmentDeficit (recovered : Nat) (capacity : Nat) : Nat :=
  capacity - recovered

-- Deficit is zero when fully recovered
theorem deficit_at_capacity (capacity : Nat) :
    photopigmentDeficit capacity capacity = 0 := by
  unfold photopigmentDeficit
  exact Nat.sub_self capacity

-- Deficit decreases as recovery increases
theorem deficit_decreases (capacity r₁ r₂ : Nat) (hle : r₁ ≤ r₂) :
    photopigmentDeficit r₂ capacity ≤ photopigmentDeficit r₁ capacity := by
  unfold photopigmentDeficit
  exact Nat.sub_le_sub_left hle capacity

end Gnosis.Optics.PhotopigmentKinetics
