namespace ForkRaceFoldTheorems

/-!
Init-only transformation-family surface.

This restores the finite witness predicates used by the ledger rows for
projection, reinforcement, and decomposition. The old Lean file was already a
small Nat theorem family; this version keeps the theorem names and avoids
automation-heavy dependencies.
-/

inductive TransformationMode
  | projection
  | reinforcement
  | decomposition
deriving DecidableEq, Repr

structure TransformationWitness where
  beforeCrossings : Nat
  afterCrossings : Nat
  beforeWeight : Nat
  afterWeight : Nat
deriving Repr

def isProjectionWitness (w : TransformationWitness) : Prop :=
  w.beforeCrossings = 0 ∧ 0 < w.afterCrossings

def isReinforcementWitness (w : TransformationWitness) : Prop :=
  w.beforeCrossings = w.afterCrossings ∧ w.beforeWeight < w.afterWeight

def isSuccessfulReinforcementWitness (w : TransformationWitness) : Prop :=
  0 < w.beforeCrossings ∧ isReinforcementWitness w

def isWeakDecompositionWitness (w : TransformationWitness) : Prop :=
  w.afterCrossings ≤ w.beforeCrossings

def isDecompositionWitness (w : TransformationWitness) : Prop :=
  w.afterCrossings < w.beforeCrossings

theorem projection_adds_structure
    (w : TransformationWitness)
    (hProjection : isProjectionWitness w) :
    w.beforeCrossings = 0 ∧ 0 < w.afterCrossings := by
  exact hProjection

theorem reinforcement_preserves_structure
    (w : TransformationWitness)
    (hReinforcement : isReinforcementWitness w) :
    w.beforeCrossings = w.afterCrossings ∧ w.beforeWeight < w.afterWeight := by
  exact hReinforcement

theorem decomposition_removes_or_preserves_structure
    (w : TransformationWitness)
    (hDecomposition : isWeakDecompositionWitness w) :
    w.afterCrossings ≤ w.beforeCrossings := by
  exact hDecomposition

theorem projection_reinforcement_exclusive
    (w : TransformationWitness)
    (hProjection : isProjectionWitness w) :
    ¬ isReinforcementWitness w := by
  intro hReinforcement
  have hBeforeZero : w.beforeCrossings = 0 := hProjection.1
  have hAfterPositive : 0 < w.afterCrossings := hProjection.2
  have hBeforeAfter : w.beforeCrossings = w.afterCrossings := hReinforcement.1
  have hAfterZero : w.afterCrossings = 0 := by
    rw [← hBeforeAfter]
    exact hBeforeZero
  rw [hAfterZero] at hAfterPositive
  exact Nat.lt_irrefl 0 hAfterPositive

theorem reinforcement_decomposition_exclusive
    (w : TransformationWitness)
    (hReinforcement : isReinforcementWitness w) :
    ¬ isDecompositionWitness w := by
  intro hDecomposition
  have hBeforeAfter : w.beforeCrossings = w.afterCrossings := hReinforcement.1
  unfold isDecompositionWitness at hDecomposition
  rw [← hBeforeAfter] at hDecomposition
  exact Nat.lt_irrefl w.beforeCrossings hDecomposition

theorem featureless_states_cannot_reinforce
    (w : TransformationWitness)
    (hFeatureless : w.beforeCrossings = 0) :
    ¬ isSuccessfulReinforcementWitness w := by
  intro hSuccessful
  have hPositive : 0 < w.beforeCrossings := hSuccessful.1
  rw [hFeatureless] at hPositive
  exact Nat.lt_irrefl 0 hPositive

theorem decompose_then_reinforce_requires_restoration
    (decomp reinforce : TransformationWitness)
    (hFull : decomp.afterCrossings = 0)
    (hLink : reinforce.beforeCrossings = decomp.afterCrossings) :
    ¬ isSuccessfulReinforcementWitness reinforce := by
  intro hSuccessful
  have hFeatureless : reinforce.beforeCrossings = 0 := by
    rw [hLink]
    exact hFull
  have hPositive : 0 < reinforce.beforeCrossings := hSuccessful.1
  rw [hFeatureless] at hPositive
  exact Nat.lt_irrefl 0 hPositive

end ForkRaceFoldTheorems
