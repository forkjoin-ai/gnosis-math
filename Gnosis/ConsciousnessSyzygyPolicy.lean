import Init
import Gnosis.AntColonyCollectiveIntelligence

namespace Gnosis

/-!
# Consciousness Syzygy Policy (Constructive)

Three-state gender scaffold (`-1, 0, 1`) linked to:
- propagation/community/stability signals,
- reproductive-void amplification,
- mode selection under laminar vs shock conditions, and
- low-diversity network mapping for focused operation.

All results are constructive (no `-- placeholder`, no new axioms).
-/

inductive TriGender where
  | negOne
  | zero
  | posOne
deriving DecidableEq, Repr

def TriGender.code : TriGender → Int
  | .negOne => -1
  | .zero => 0
  | .posOne => 1

theorem tri_gender_code_three_values (g : TriGender) :
    g.code = -1 ∨ g.code = 0 ∨ g.code = 1 := by
  cases g <;> simp [TriGender.code]

theorem tri_gender_code_injective {a b : TriGender}
    (h : a.code = b.code) :
    a = b := by
  cases a <;> cases b <;> simp [TriGender.code] at h <;> rfl

structure TriGenderPopulation where
  negOneCount : Nat
  zeroCount : Nat
  posOneCount : Nat
  ventBurden : Nat
  kinLinks : Nat

def TriGenderPopulation.toFRF (p : TriGenderPopulation) : FRFProfile where
  fork := p.posOneCount + p.zeroCount
  race := p.negOneCount + p.zeroCount
  fold := p.negOneCount + p.posOneCount
  vent := p.ventBurden

def TriGenderPopulation.withExtraZero (p : TriGenderPopulation) (k : Nat) :
    TriGenderPopulation :=
  { p with zeroCount := p.zeroCount + k }

def TriGenderPopulation.kinStability (p : TriGenderPopulation) : Nat :=
  p.toFRF.stabilitySignal * (p.kinLinks + 1)

theorem stability_signal_fork_race_fold_reduce (p : TriGenderPopulation) :
    p.toFRF.stabilitySignal =
      p.toFRF.fork + p.toFRF.fold + (p.toFRF.race + p.toFRF.race) := by
  unfold TriGenderPopulation.toFRF
    FRFProfile.stabilitySignal FRFProfile.propagationPotential
    FRFProfile.communityPotential
  simp [Nat.add_left_comm, Nat.add_comm]

theorem stability_signal_reduces_to_count_weights (p : TriGenderPopulation) :
    p.toFRF.stabilitySignal =
      (p.posOneCount + p.posOneCount) +
        (p.negOneCount + p.negOneCount + p.negOneCount) +
        (p.zeroCount + p.zeroCount + p.zeroCount) := by
  unfold TriGenderPopulation.toFRF
    FRFProfile.stabilitySignal FRFProfile.propagationPotential
    FRFProfile.communityPotential
  simp [Nat.add_left_comm, Nat.add_comm]

theorem extra_zero_increases_stability_signal (p : TriGenderPopulation) (k : Nat) :
    (p.withExtraZero k).toFRF.stabilitySignal =
      p.toFRF.stabilitySignal + (k + k + k) := by
  unfold TriGenderPopulation.withExtraZero TriGenderPopulation.toFRF
    FRFProfile.stabilitySignal FRFProfile.propagationPotential
    FRFProfile.communityPotential
  simp [Nat.add_left_comm, Nat.add_comm]

theorem extra_one_zero_adds_three_stability_channels (p : TriGenderPopulation) :
    (p.withExtraZero 1).toFRF.stabilitySignal = p.toFRF.stabilitySignal + 3 := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    extra_zero_increases_stability_signal p 1

theorem extra_zero_strictly_increases_kin_stability
    (p : TriGenderPopulation)
    {k : Nat}
    (hk : 0 < k) :
    p.kinStability < (p.withExtraZero k).kinStability := by
  unfold TriGenderPopulation.kinStability
  rw [extra_zero_increases_stability_signal]
  have hTriplePos : 0 < k + k + k := by
    have hkLe : k ≤ k + k + k := by
      calc
        k ≤ k + k := Nat.le_add_right _ _
        _ ≤ k + k + k := Nat.le_add_right _ _
    exact Nat.lt_of_lt_of_le hk hkLe
  have hFactorPos : 0 < p.kinLinks + 1 := Nat.succ_pos _
  have hDeltaPos : 0 < (k + k + k) * (p.kinLinks + 1) :=
    Nat.mul_pos hTriplePos hFactorPos
  rw [Nat.add_mul]
  exact Nat.lt_add_of_pos_right hDeltaPos

inductive ConsciousnessMode where
  | focused
  | daydream
  | realityCheck
deriving DecidableEq, Repr

structure ConsciousnessSignals where
  laminar : Bool
  corridorSignal : Nat
  garbleRisk : Nat
  cvi : Nat
  perturbation : Nat
  correlatedShock : Nat

def daydreamWindow (s : ConsciousnessSignals) : Prop :=
  s.laminar = true ∧
  6 ≤ s.corridorSignal ∧
  s.garbleRisk ≤ 3 ∧
  3 ≤ s.cvi ∧
  s.cvi ≤ 5 ∧
  s.perturbation ≤ 6 ∧
  s.correlatedShock = 0

instance decidableDaydreamWindow (s : ConsciousnessSignals) : Decidable (daydreamWindow s) := by
  unfold daydreamWindow
  infer_instance

def decideMode (s : ConsciousnessSignals) : ConsciousnessMode :=
  if _hShock : s.correlatedShock = 0 then
    if daydreamWindow s then .daydream else .focused
  else
    .realityCheck

theorem shock_forces_reality_check
    (s : ConsciousnessSignals)
    (hShock : s.correlatedShock ≠ 0) :
    decideMode s = .realityCheck := by
  simp [decideMode, hShock]

theorem daydream_requires_laminar_and_zero_shock
    (s : ConsciousnessSignals)
    (hMode : decideMode s = .daydream) :
    s.laminar = true ∧ s.correlatedShock = 0 := by
  by_cases hShock : s.correlatedShock = 0
  · have hWindow : daydreamWindow s := by
      simpa [decideMode, hShock] using hMode
    exact ⟨hWindow.1, hShock⟩
  · have hReality : decideMode s = .realityCheck := by
      simp [decideMode, hShock]
    rw [hReality] at hMode
    cases hMode

structure SyzygyPlan where
  stageCount : Nat
  recommendedLanes : Nat

def syzygyPlanForMode : ConsciousnessMode → SyzygyPlan
  | .focused => { stageCount := 1, recommendedLanes := 2 }
  | .daydream => { stageCount := 2, recommendedLanes := 3 }
  | .realityCheck => { stageCount := 3, recommendedLanes := 4 }

theorem syzygy_plan_lane_invariants (m : ConsciousnessMode) :
    (syzygyPlanForMode m).recommendedLanes = (syzygyPlanForMode m).stageCount + 1 ∧
    2 ≤ (syzygyPlanForMode m).recommendedLanes := by
  cases m <;> constructor <;> decide

def diversityProfileForMode : ConsciousnessMode → NetworkProfile
  | .focused => {
      forkDiversity := 0
      raceDiversity := 0
      foldDiversity := 0
      voidRelays := 1
      throughputBase := 1
    }
  | .daydream => {
      forkDiversity := 2
      raceDiversity := 2
      foldDiversity := 1
      voidRelays := 2
      throughputBase := 5
    }
  | .realityCheck => {
      forkDiversity := 3
      raceDiversity := 3
      foldDiversity := 2
      voidRelays := 3
      throughputBase := 8
    }

theorem low_diversity_profile_iff_focused (m : ConsciousnessMode) :
    (diversityProfileForMode m).isLowDiversity ↔ m = .focused := by
  cases m <;> simp [diversityProfileForMode, NetworkProfile.isLowDiversity, NetworkProfile.diversityIndex]

end Gnosis
