import Gnosis.NeurosymbolicToolUseMarkov
import Gnosis.SemanticAuthorityBoundary

namespace Gnosis
namespace PerceptualMetacognitionC0C3

open NeurosymbolicToolUseMarkov
open SemanticAuthorityBoundary

/-!
# Perceptual Metacognition C0-C3

The third-eye perception walk is modeled as a finite sequence of perceptual
ticks. Each tick instantiates one `ToolUseMarkovTransition` from the
neurosymbolic C0-C3 metacognitive chain: certified-gnosis score deltas map to
the score delta, carried-forward abstain mass maps to the residual shadow, and
green laws cited-but-not-yet-satisfied map to the symbolic obligation count.

A perceptual tick is disciplined when it either increases certified gnosis or
exposes carried-forward shadow. The headline theorem instantiates the
template's `no_gain_disciplined_step_exposes_shadow`: a perceptual tick that did
not increase certified gnosis must expose carried-forward shadow. In plain
terms, Thoth cannot hide a non-improving observation.

This file proves bookkeeping only. It does not claim a perceptual observation is
true; it instantiates the discipline that perception cannot silently plateau.
-/

structure PerceptualTick where
  certifiedGnosisBefore : Nat
  certifiedGnosisAfter : Nat
  abstainShadow : Nat
  unsatisfiedLaws : Nat
  layer : NeurosymbolicLayer
  gate : C0C3MetacognitiveGate
  deriving DecidableEq, Repr

def PerceptualTick.toTransition
    (tick : PerceptualTick) : ToolUseMarkovTransition :=
  let base : ToolUseMarkovTransition :=
    { layer := tick.layer
      fromState := .toolCandidate
      toState := .toolCandidate
      beforeScore := tick.certifiedGnosisBefore
      afterScore := tick.certifiedGnosisAfter
      evidenceMass := 0
      residualShadow := tick.abstainShadow
      symbolicObligationCount := tick.unsatisfiedLaws
      gate := tick.gate }
  { base with toState := toolUseTransitionState base }

def PerceptualTickDisciplined (tick : PerceptualTick) : Prop :=
  ToolUseTransitionDisciplined tick.toTransition

theorem percept_no_gain_exposes_shadow
    (tick : PerceptualTick)
    (h : PerceptualTickDisciplined tick)
    (hNoGain : ¬ SyntheticGnosisIncreases tick.toTransition) :
    ShadowExposed tick.toTransition := by
  exact no_gain_disciplined_step_exposes_shadow tick.toTransition h hNoGain

theorem percept_gate_complete_projects_symbolic
    (tick : PerceptualTick)
    (h : C0C3GateComplete tick.gate) :
    tick.gate.c2SymbolicValidation = true := by
  exact c0c3_complete_projects_symbolic_validation h

structure PerceptualWitness where
  perceptionWitness : ToolUseMarkovWitness
  authorityReport : SemanticAuthorityBoundaryReport
  deriving DecidableEq, Repr

def PerceptualWitness.observationalOnly (witness : PerceptualWitness) : Prop :=
  ToolUseWitnessNonAuthority witness.perceptionWitness

def PerceptualWitness.toAuthorityAware
    (witness : PerceptualWitness) : AuthorityAwareToolUseMarkovWitness :=
  { toolWitness := witness.perceptionWitness
    authorityReport := witness.authorityReport }

def PerceptualWitness.nonAuthority (witness : PerceptualWitness) : Prop :=
  witness.toAuthorityAware.nonAuthority

theorem percept_authority_aware_non_authority
    (witness : PerceptualWitness)
    (hPerception : ToolUseWitnessNonAuthority witness.perceptionWitness)
    (hAuthority : BoundaryReportNonAuthority witness.authorityReport) :
    witness.nonAuthority := by
  exact authority_aware_tool_witness_non_authority
    witness.toAuthorityAware hPerception hAuthority

def perceptGateComplete : C0C3MetacognitiveGate :=
  { c0ToolObservation := true
    c1ScoreCalibration := true
    c2SymbolicValidation := true
    c3FrameworkAudit := true }

def perceptGainTick : PerceptualTick :=
  { certifiedGnosisBefore := 12
    certifiedGnosisAfter := 19
    abstainShadow := 0
    unsatisfiedLaws := 0
    layer := .C1
    gate := perceptGateComplete }

def perceptPlateauTick : PerceptualTick :=
  { certifiedGnosisBefore := 19
    certifiedGnosisAfter := 19
    abstainShadow := 2
    unsatisfiedLaws := 1
    layer := .C2
    gate := perceptGateComplete }

def perceptRegressionTick : PerceptualTick :=
  { certifiedGnosisBefore := 19
    certifiedGnosisAfter := 14
    abstainShadow := 4
    unsatisfiedLaws := 0
    layer := .C3
    gate := perceptGateComplete }

theorem percept_gain_tick_disciplined :
    PerceptualTickDisciplined perceptGainTick := by
  left
  unfold SyntheticGnosisIncreases PerceptualTick.toTransition perceptGainTick
  decide

theorem percept_plateau_tick_disciplined :
    PerceptualTickDisciplined perceptPlateauTick := by
  right
  unfold ShadowExposed PerceptualTick.toTransition perceptPlateauTick
  decide

theorem percept_regression_tick_disciplined :
    PerceptualTickDisciplined perceptRegressionTick := by
  right
  unfold ShadowExposed PerceptualTick.toTransition perceptRegressionTick
  decide

theorem percept_plateau_tick_no_gain :
    ¬ SyntheticGnosisIncreases perceptPlateauTick.toTransition := by
  unfold SyntheticGnosisIncreases PerceptualTick.toTransition perceptPlateauTick
  decide

theorem percept_plateau_tick_exposes_shadow :
    ShadowExposed perceptPlateauTick.toTransition := by
  exact percept_no_gain_exposes_shadow
    perceptPlateauTick
    percept_plateau_tick_disciplined
    percept_plateau_tick_no_gain

def perceptWitness : PerceptualWitness :=
  { perceptionWitness :=
      buildToolUseWitness
        [perceptGainTick.toTransition,
         perceptPlateauTick.toTransition,
         perceptRegressionTick.toTransition] 12 14
    authorityReport := SemanticAuthorityBoundary.witnessBoundaryReport }

theorem percept_witness_observational_only :
    perceptWitness.observationalOnly := by
  rfl

theorem percept_witness_non_authority :
    perceptWitness.nonAuthority := by
  exact percept_authority_aware_non_authority
    perceptWitness
    percept_witness_observational_only
    SemanticAuthorityBoundary.witness_boundary_non_authority

end PerceptualMetacognitionC0C3
end Gnosis
