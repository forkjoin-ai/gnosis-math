import Gnosis.TransformationFamily

/-!
# Cancer Reinforcement

Small Nat-valued outcome algebra for checkpoint-preserving targeted therapy,
over-capacity shattering, and featureless checkpoint collapse.
-/

namespace CancerReinforcement

inductive TherapyOutcome where
  | reinforce
  | shatter
  | fizzle
deriving DecidableEq, Repr

structure CellTarget where
  checkpointCrossings : Nat
  capacity : Nat
deriving Repr

structure TherapeuticDose where
  energy : Nat
deriving Repr

def isFeatureless (cell : CellTarget) : Prop :=
  cell.checkpointCrossings = 0

def therapyOutcome (cell : CellTarget) (dose : TherapeuticDose) : TherapyOutcome :=
  if cell.checkpointCrossings = 0 then
    .fizzle
  else if dose.energy ≤ cell.capacity then
    .reinforce
  else
    .shatter

theorem targeted_therapy_succeeds
    (cell : CellTarget)
    (dose : TherapeuticDose)
    (hCheckpoints : 0 < cell.checkpointCrossings)
    (hDose : dose.energy ≤ cell.capacity) :
    therapyOutcome cell dose = .reinforce := by
  have hNotFeatureless : ¬ cell.checkpointCrossings = 0 :=
    Nat.ne_of_gt hCheckpoints
  simp [therapyOutcome, hNotFeatureless, hDose]

theorem chemo_shatters_healthy
    (cell : CellTarget)
    (dose : TherapeuticDose)
    (hCheckpoints : 0 < cell.checkpointCrossings)
    (hOverCapacity : cell.capacity < dose.energy) :
    therapyOutcome cell dose = .shatter := by
  have hNotFeatureless : ¬ cell.checkpointCrossings = 0 :=
    Nat.ne_of_gt hCheckpoints
  have hNotSafe : ¬ dose.energy ≤ cell.capacity :=
    Nat.not_le_of_gt hOverCapacity
  simp [therapyOutcome, hNotFeatureless, hNotSafe]

theorem featureless_resists
    (cell : CellTarget)
    (dose : TherapeuticDose)
    (hFeatureless : isFeatureless cell) :
    therapyOutcome cell dose = .fizzle := by
  unfold isFeatureless at hFeatureless
  unfold therapyOutcome
  rw [hFeatureless]
  rfl

theorem cancer_reinforcement_master
    (cell : CellTarget)
    (dose : TherapeuticDose) :
    (isFeatureless cell ∧ therapyOutcome cell dose = .fizzle) ∨
    (0 < cell.checkpointCrossings ∧
      cell.capacity < dose.energy ∧
      therapyOutcome cell dose = .shatter) ∨
    (0 < cell.checkpointCrossings ∧
      dose.energy ≤ cell.capacity ∧
      therapyOutcome cell dose = .reinforce) := by
  by_cases hFeatureless : cell.checkpointCrossings = 0
  · left
    exact ⟨hFeatureless, featureless_resists cell dose hFeatureless⟩
  · have hPositive : 0 < cell.checkpointCrossings := Nat.pos_of_ne_zero hFeatureless
    by_cases hDose : dose.energy ≤ cell.capacity
    · right
      right
      exact ⟨hPositive, hDose, targeted_therapy_succeeds cell dose hPositive hDose⟩
    · right
      left
      have hOverCapacity : cell.capacity < dose.energy :=
        Nat.lt_of_not_ge hDose
      exact
        ⟨hPositive,
          hOverCapacity,
          chemo_shatters_healthy cell dose hPositive hOverCapacity⟩

theorem cancer_is_featureless
    (cell : CellTarget)
    (hDestroyed : cell.checkpointCrossings = 0) :
    isFeatureless cell :=
  hDestroyed

theorem one_checkpoint_breaks_fizzle :
    ¬ isFeatureless { checkpointCrossings := 1, capacity := 1 } := by
  intro hFeatureless
  exact Nat.succ_ne_zero 0 hFeatureless

theorem one_checkpoint_breaks_featurelessness
    (capacity : Nat) :
    ¬ isFeatureless { checkpointCrossings := 1, capacity := capacity } := by
  intro hFeatureless
  exact Nat.succ_ne_zero 0 hFeatureless

theorem featureless_transformation_cannot_reinforce
    (weightBefore weightAfter : Nat) :
    ¬ Gnosis.isSuccessfulReinforcementWitness
      { beforeCrossings := 0
        afterCrossings := 0
        beforeWeight := weightBefore
        afterWeight := weightAfter } :=
  Gnosis.featureless_states_cannot_reinforce _ rfl

end CancerReinforcement
