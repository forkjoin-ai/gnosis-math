import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Buddhist
namespace DhammacakkappavattanaWheelWitness

/-!
# Dhammacakkappavattana Sutta -- Wheel as Exhaustion Protocol

Source text: `docs/ebooks/source-texts/dhammacakkappavattana-sutta-thanissaro.txt`;
text anchor `docs/ebooks/source-texts/dhammacakkappavattana-sutta-thanissaro.txt:1-16`.

Sat/unseen reading:

The first turning of the Dhamma wheel is a verification protocol, not a sermon
outline. The two extremes are refused as unprofitable boundary states; the
middle way is an eightfold operator that produces vision and knowledge; the four
truths are not merely named, but exhausted through three rounds: know the truth,
know the task, know the task is complete. Awakening is not claimed until the
4 x 3 matrix is pure.

Invariant:

  * sensual indulgence and self-affliction are both rejected;
  * the middle way leads through the eightfold path;
  * stress, origination, cessation, and path each receive three completions;
  * the wheel is unstoppable only after the matrix closes;
  * Kondanna's eye sees the invariant: whatever originates ceases.

Gap / counterproof:

  * one truth label is not enough;
  * one insight event is not enough;
  * one ethical path without task-completion is not enough;
  * awakening is not Sat until the twelve-permutation knowledge-and-vision
    ledger is pure.

No `sorry`, no new `axiom`.
-/

structure ExtremesRejected where
  sensualIndulgenceRejected : Bool
  selfAfflictionRejected : Bool
  bothIgnoble : Bool
  bothUnprofitable : Bool
deriving DecidableEq, Repr

def dhammaExtremesRejected : ExtremesRejected where
  sensualIndulgenceRejected := true
  selfAfflictionRejected := true
  bothIgnoble := true
  bothUnprofitable := true

def extremesAreNotPath (e : ExtremesRejected) : Prop :=
  e.sensualIndulgenceRejected = true ∧
  e.selfAfflictionRejected = true ∧
  e.bothIgnoble = true ∧
  e.bothUnprofitable = true

structure EightfoldMiddleWay where
  rightView : Bool
  rightResolve : Bool
  rightSpeech : Bool
  rightAction : Bool
  rightLivelihood : Bool
  rightEffort : Bool
  rightMindfulness : Bool
  rightConcentration : Bool
  producesVisionKnowledge : Bool
  leadsToUnbinding : Bool
deriving DecidableEq, Repr

def dhammaEightfoldMiddleWay : EightfoldMiddleWay where
  rightView := true
  rightResolve := true
  rightSpeech := true
  rightAction := true
  rightLivelihood := true
  rightEffort := true
  rightMindfulness := true
  rightConcentration := true
  producesVisionKnowledge := true
  leadsToUnbinding := true

def middleWayIsEightfoldOperator (p : EightfoldMiddleWay) : Prop :=
  p.rightView = true ∧
  p.rightResolve = true ∧
  p.rightSpeech = true ∧
  p.rightAction = true ∧
  p.rightLivelihood = true ∧
  p.rightEffort = true ∧
  p.rightMindfulness = true ∧
  p.rightConcentration = true ∧
  p.producesVisionKnowledge = true ∧
  p.leadsToUnbinding = true

structure FourTruthWheel where
  truthCount : Nat
  roundsPerTruth : Nat
  permutationCount : Nat
  stressComprehended : Bool
  cravingAbandoned : Bool
  cessationExperienced : Bool
  pathDeveloped : Bool
  purityBeforeClaim : Bool
deriving DecidableEq, Repr

def dhammaFourTruthWheel : FourTruthWheel where
  truthCount := 4
  roundsPerTruth := 3
  permutationCount := 12
  stressComprehended := true
  cravingAbandoned := true
  cessationExperienced := true
  pathDeveloped := true
  purityBeforeClaim := true

def twelvePermutationClosure (w : FourTruthWheel) : Prop :=
  w.truthCount * w.roundsPerTruth = w.permutationCount ∧
  w.stressComprehended = true ∧
  w.cravingAbandoned = true ∧
  w.cessationExperienced = true ∧
  w.pathDeveloped = true ∧
  w.purityBeforeClaim = true

structure UnstoppableWitness where
  releaseUnprovoked : Bool
  lastBirth : Bool
  noFurtherBecoming : Bool
  whateverOriginatesCeases : Bool
  wheelCannotBeStopped : Bool
  cosmosRadiance : Bool
deriving DecidableEq, Repr

def dhammaUnstoppableWitness : UnstoppableWitness where
  releaseUnprovoked := true
  lastBirth := true
  noFurtherBecoming := true
  whateverOriginatesCeases := true
  wheelCannotBeStopped := true
  cosmosRadiance := true

def wheelTurnsAfterClosure (u : UnstoppableWitness) : Prop :=
  u.releaseUnprovoked = true ∧
  u.lastBirth = true ∧
  u.noFurtherBecoming = true ∧
  u.whateverOriginatesCeases = true ∧
  u.wheelCannotBeStopped = true ∧
  u.cosmosRadiance = true

theorem dhamma_extremes_rejected :
    extremesAreNotPath dhammaExtremesRejected := by
  unfold extremesAreNotPath dhammaExtremesRejected
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem dhamma_middle_way_operator :
    middleWayIsEightfoldOperator dhammaEightfoldMiddleWay := by
  unfold middleWayIsEightfoldOperator dhammaEightfoldMiddleWay
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dhamma_twelve_permutation_closure :
    twelvePermutationClosure dhammaFourTruthWheel := by
  unfold twelvePermutationClosure dhammaFourTruthWheel
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dhamma_wheel_turns_after_closure :
    wheelTurnsAfterClosure dhammaUnstoppableWitness := by
  unfold wheelTurnsAfterClosure dhammaUnstoppableWitness
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem middle_way_recovery_shape :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem dhammacakkappavattana_wheel_witness :
    extremesAreNotPath dhammaExtremesRejected ∧
    middleWayIsEightfoldOperator dhammaEightfoldMiddleWay ∧
    twelvePermutationClosure dhammaFourTruthWheel ∧
    wheelTurnsAfterClosure dhammaUnstoppableWitness ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨dhamma_extremes_rejected,
    dhamma_middle_way_operator,
    dhamma_twelve_permutation_closure,
    dhamma_wheel_turns_after_closure,
    middle_way_recovery_shape⟩

end DhammacakkappavattanaWheelWitness
end Gnosis.Witnesses.Buddhist
