import Gnosis.SyntheticGnosisMeasurement
import Gnosis.FiniteProbabilityCore.MarkovWitnesses
import Gnosis.SemanticAuthorityBoundary

namespace Gnosis
namespace NeurosymbolicToolUseMarkov

open SyntheticGnosisMeasurement
open FiniteProbabilityCore
open SemanticAuthorityBoundary

/-!
# Neurosymbolic Tool-Use Markov Witness

System 2 tooling is modeled as a finite Markov walk over explicit tool
observations. A transition is disciplined when it either increases the
observable synthetic-gnosis score or exposes residual shadow that must be
argued, repaired, or carried forward.

The C0-C3 labels are scanner gates:
- C0 records the raw tool observation.
- C1 calibrates score deltas.
- C2 checks symbolic obligations.
- C3 detects plateau/regression loops and framework bias.

This file proves bookkeeping only. It does not claim that a tool result is true;
it proves that runtime tooling can avoid hiding non-improving steps.
-/

inductive NeurosymbolicLayer where
  | C0
  | C1
  | C2
  | C3
  deriving DecidableEq, Repr

inductive ToolUseMarkovState where
  | toolCandidate
  | scoreCalibrated
  | symbolicChecked
  | frameworkAudited
  | syntheticGnosisGain
  | shadowResidual
  | unresolvedRegression
  deriving DecidableEq, Repr

structure C0C3MetacognitiveGate where
  c0ToolObservation : Bool
  c1ScoreCalibration : Bool
  c2SymbolicValidation : Bool
  c3FrameworkAudit : Bool
  deriving DecidableEq, Repr

structure ToolUseMarkovTransition where
  layer : NeurosymbolicLayer
  fromState : ToolUseMarkovState
  toState : ToolUseMarkovState
  beforeScore : Nat
  afterScore : Nat
  evidenceMass : Nat
  residualShadow : Nat
  symbolicObligationCount : Nat
  gate : C0C3MetacognitiveGate
  deriving DecidableEq, Repr

def SyntheticGnosisIncreases (transition : ToolUseMarkovTransition) : Prop :=
  transition.beforeScore < transition.afterScore

def ShadowExposed (transition : ToolUseMarkovTransition) : Prop :=
  0 < transition.residualShadow + transition.symbolicObligationCount

def ToolUseTransitionDisciplined
    (transition : ToolUseMarkovTransition) : Prop :=
  SyntheticGnosisIncreases transition ∨ ShadowExposed transition

def C0C3GateComplete (gate : C0C3MetacognitiveGate) : Prop :=
  gate.c0ToolObservation = true ∧
  gate.c1ScoreCalibration = true ∧
  gate.c2SymbolicValidation = true ∧
  gate.c3FrameworkAudit = true

def toolUseScoreGain (transition : ToolUseMarkovTransition) : Nat :=
  transition.afterScore - transition.beforeScore

def toolUseRegressionDebt (transition : ToolUseMarkovTransition) : Nat :=
  transition.beforeScore - transition.afterScore

def toolUseTransitionShadow (transition : ToolUseMarkovTransition) : Nat :=
  transition.residualShadow +
  transition.symbolicObligationCount +
  toolUseRegressionDebt transition

def toolUseTransitionState
    (transition : ToolUseMarkovTransition) : ToolUseMarkovState :=
  if transition.beforeScore < transition.afterScore then
    .syntheticGnosisGain
  else if 0 < transition.residualShadow + transition.symbolicObligationCount then
    .shadowResidual
  else
    .unresolvedRegression

def transitionListGain : List ToolUseMarkovTransition → Nat
  | [] => 0
  | transition :: rest => toolUseScoreGain transition + transitionListGain rest

def transitionListShadow : List ToolUseMarkovTransition → Nat
  | [] => 0
  | transition :: rest => toolUseTransitionShadow transition + transitionListShadow rest

structure ToolUseMarkovWitness where
  transitions : List ToolUseMarkovTransition
  initialScore : Nat
  finalScore : Nat
  theoremLabel : String
  observationalOnly : Bool
  deriving DecidableEq, Repr

def ToolUseMarkovWitness.totalSyntheticGnosisGain
    (witness : ToolUseMarkovWitness) : Nat :=
  transitionListGain witness.transitions

def ToolUseMarkovWitness.totalShadowResidual
    (witness : ToolUseMarkovWitness) : Nat :=
  transitionListShadow witness.transitions

def ToolUseMarkovWitness.toFiniteMarkovWitness
    (witness : ToolUseMarkovWitness) : FiniteMarkovWitness :=
  { kernels := []
    shadowResidual := witness.totalShadowResidual }

def ToolUseWalkDisciplined (witness : ToolUseMarkovWitness) : Prop :=
  ∀ transition ∈ witness.transitions, ToolUseTransitionDisciplined transition

def ToolUseWitnessNonAuthority (witness : ToolUseMarkovWitness) : Prop :=
  witness.observationalOnly = true

structure AuthorityAwareToolUseMarkovWitness where
  toolWitness : ToolUseMarkovWitness
  authorityReport : SemanticAuthorityBoundaryReport
  deriving DecidableEq, Repr

def AuthorityAwareToolUseMarkovWitness.totalShadowResidual
    (witness : AuthorityAwareToolUseMarkovWitness) : Nat :=
  witness.toolWitness.totalShadowResidual +
    boundaryObligationCount witness.authorityReport.claims

def AuthorityAwareToolUseMarkovWitness.nonAuthority
    (witness : AuthorityAwareToolUseMarkovWitness) : Prop :=
  ToolUseWitnessNonAuthority witness.toolWitness ∧
    BoundaryReportNonAuthority witness.authorityReport

def buildToolUseWitness
    (transitions : List ToolUseMarkovTransition)
    (initialScore finalScore : Nat) : ToolUseMarkovWitness :=
  { transitions
    initialScore
    finalScore
    theoremLabel :=
      "Gnosis.NeurosymbolicToolUseMarkov.tool_use_markov_non_authority"
    observationalOnly := true }

theorem c0c3_complete_projects_symbolic_validation
    {gate : C0C3MetacognitiveGate}
    (h : C0C3GateComplete gate) :
    gate.c2SymbolicValidation = true := by
  exact h.2.2.1

theorem disciplined_tool_step_increases_or_exposes_shadow
    (transition : ToolUseMarkovTransition)
    (h : ToolUseTransitionDisciplined transition) :
    SyntheticGnosisIncreases transition ∨ ShadowExposed transition := by
  exact h

theorem no_gain_disciplined_step_exposes_shadow
    (transition : ToolUseMarkovTransition)
    (h : ToolUseTransitionDisciplined transition)
    (hNoGain : ¬ SyntheticGnosisIncreases transition) :
    ShadowExposed transition := by
  cases h with
  | inl hGain => exact False.elim (hNoGain hGain)
  | inr hShadow => exact hShadow

theorem transition_shadow_covers_residual
    (transition : ToolUseMarkovTransition) :
    transition.residualShadow ≤ toolUseTransitionShadow transition := by
  unfold toolUseTransitionShadow
  rw [Nat.add_assoc]
  exact Nat.le_add_right transition.residualShadow
    (transition.symbolicObligationCount + toolUseRegressionDebt transition)

theorem transition_shadow_covers_obligations
    (transition : ToolUseMarkovTransition) :
    transition.symbolicObligationCount ≤ toolUseTransitionShadow transition := by
  unfold toolUseTransitionShadow
  exact Nat.le_trans
    (Nat.le_add_left transition.symbolicObligationCount transition.residualShadow)
    (Nat.le_add_right
      (transition.residualShadow + transition.symbolicObligationCount)
      (toolUseRegressionDebt transition))

theorem tool_use_witness_non_authority
    (transitions : List ToolUseMarkovTransition)
    (initialScore finalScore : Nat) :
    ToolUseWitnessNonAuthority
      (buildToolUseWitness transitions initialScore finalScore) := by
  rfl

theorem tool_use_to_finite_markov_shadow_projects
    (witness : ToolUseMarkovWitness) :
    witness.toFiniteMarkovWitness.totalShadow =
      witness.totalShadowResidual := by
  unfold ToolUseMarkovWitness.toFiniteMarkovWitness
  unfold FiniteMarkovWitness.totalShadow
  simp [kernelListLostMass]

theorem finite_markov_shadow_matches_tool_shadow
    (witness : ToolUseMarkovWitness) :
    witness.toFiniteMarkovWitness.totalShadow =
      transitionListShadow witness.transitions := by
  rw [tool_use_to_finite_markov_shadow_projects]
  rfl

theorem authority_aware_tool_shadow_adds_boundary_obligations
    (witness : AuthorityAwareToolUseMarkovWitness) :
    witness.totalShadowResidual =
      witness.toolWitness.totalShadowResidual +
        boundaryObligationCount witness.authorityReport.claims := by
  rfl

theorem authority_aware_tool_witness_non_authority
    (witness : AuthorityAwareToolUseMarkovWitness)
    (hTool : ToolUseWitnessNonAuthority witness.toolWitness)
    (hAuthority : BoundaryReportNonAuthority witness.authorityReport) :
    witness.nonAuthority := by
  exact ⟨hTool, hAuthority⟩

def witnessGateComplete : C0C3MetacognitiveGate :=
  { c0ToolObservation := true
    c1ScoreCalibration := true
    c2SymbolicValidation := true
    c3FrameworkAudit := true }

def witnessGainTransition : ToolUseMarkovTransition :=
  { layer := .C3
    fromState := .frameworkAudited
    toState := .syntheticGnosisGain
    beforeScore := 10
    afterScore := 17
    evidenceMass := 2048
    residualShadow := 0
    symbolicObligationCount := 0
    gate := witnessGateComplete }

def witnessShadowTransition : ToolUseMarkovTransition :=
  { layer := .C2
    fromState := .symbolicChecked
    toState := .shadowResidual
    beforeScore := 17
    afterScore := 17
    evidenceMass := 1024
    residualShadow := 3
    symbolicObligationCount := 1
    gate := witnessGateComplete }

def witnessToolUseMarkov : ToolUseMarkovWitness :=
  buildToolUseWitness [witnessGainTransition, witnessShadowTransition] 10 17

def witnessAuthorityAwareToolUseMarkov : AuthorityAwareToolUseMarkovWitness :=
  { toolWitness := witnessToolUseMarkov
    authorityReport := SemanticAuthorityBoundary.witnessBoundaryReport }

theorem witness_gain_transition_disciplined :
    ToolUseTransitionDisciplined witnessGainTransition := by
  left
  unfold SyntheticGnosisIncreases witnessGainTransition
  decide

theorem witness_shadow_transition_disciplined :
    ToolUseTransitionDisciplined witnessShadowTransition := by
  right
  unfold ShadowExposed witnessShadowTransition
  decide

theorem witness_tool_use_walk_disciplined :
    ToolUseWalkDisciplined witnessToolUseMarkov := by
  intro transition h
  simp [witnessToolUseMarkov, buildToolUseWitness] at h
  cases h with
  | inl hGain =>
      subst transition
      exact witness_gain_transition_disciplined
  | inr hShadow =>
      subst transition
      exact witness_shadow_transition_disciplined

theorem witness_tool_use_non_authority :
    ToolUseWitnessNonAuthority witnessToolUseMarkov := by
  rfl

theorem witness_tool_use_total_shadow :
    witnessToolUseMarkov.totalShadowResidual = 4 := by
  rfl

theorem witness_tool_use_finite_markov_shadow :
    witnessToolUseMarkov.toFiniteMarkovWitness.totalShadow = 4 := by
  rw [tool_use_to_finite_markov_shadow_projects]
  rfl

theorem witness_authority_aware_tool_shadow :
    witnessAuthorityAwareToolUseMarkov.totalShadowResidual = 7 := by
  rfl

theorem witness_authority_aware_non_authority :
    witnessAuthorityAwareToolUseMarkov.nonAuthority := by
  exact authority_aware_tool_witness_non_authority
    witnessAuthorityAwareToolUseMarkov
    witness_tool_use_non_authority
    SemanticAuthorityBoundary.witness_boundary_non_authority

end NeurosymbolicToolUseMarkov
end Gnosis
