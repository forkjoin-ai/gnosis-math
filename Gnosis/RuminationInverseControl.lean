import Gnosis.Contrarian.ContrarianStallIsInformationDensity
import Gnosis.DepressionAsDampedOscillation
import Gnosis.PhysarumRopelength
import Gnosis.PsychologyAsInterference

/-!
# Rumination as Inverse Control

This bridge separates rumination from suppression in the existing
interference psychology model. A stall is not automatically a failure:
under unresolved threat, rumination preserves observation. It becomes
pathological when recovery is available but the loop does not update.
-/

namespace Gnosis.RuminationInverseControl

inductive CopingStallMode where
  | ruminationObservation
  | suppressionControl
  | panicCascade
  | learnedHelplessness
  | compulsiveControl
  | dissociation
  | echoChamberLock
  | mediocritySaturation
deriving Repr, DecidableEq

def copingStallModes : List CopingStallMode :=
  [.ruminationObservation,
    .suppressionControl,
    .panicCascade,
    .learnedHelplessness,
    .compulsiveControl,
    .dissociation,
    .echoChamberLock,
    .mediocritySaturation]

def stallPreservesObservation : CopingStallMode → Bool
  | .ruminationObservation => true
  | .panicCascade => true
  | .echoChamberLock => true
  | _ => false

def stallDestroysRecovery : CopingStallMode → Bool
  | .suppressionControl => true
  | .learnedHelplessness => true
  | .dissociation => true
  | .mediocritySaturation => true
  | _ => false

def stallPreservesAction : CopingStallMode → Bool
  | .panicCascade => true
  | .compulsiveControl => true
  | _ => false

def stallDestroysAction : CopingStallMode → Bool
  | .learnedHelplessness => true
  | .dissociation => true
  | _ => false

def stallPreservesDiversity : CopingStallMode → Bool
  | .panicCascade => true
  | .ruminationObservation => true
  | _ => false

def stallDestroysDiversity : CopingStallMode → Bool
  | .echoChamberLock => true
  | .mediocritySaturation => true
  | .suppressionControl => true
  | _ => false

def stallPreservesControlCost : CopingStallMode → Bool
  | .dissociation => true
  | .ruminationObservation => true
  | _ => false

def stallDestroysControlCost : CopingStallMode → Bool
  | .compulsiveControl => true
  | .mediocritySaturation => true
  | .panicCascade => true
  | _ => false

def stallControlCost : CopingStallMode → Nat
  | .ruminationObservation => 6
  | .suppressionControl => 8
  | .panicCascade => 10
  | .learnedHelplessness => 7
  | .compulsiveControl => 11
  | .dissociation => 5
  | .echoChamberLock => 9
  | .mediocritySaturation => 12

def stallRecoveryValue : CopingStallMode → Nat
  | .ruminationObservation => 2
  | .suppressionControl => 0
  | .panicCascade => 1
  | .learnedHelplessness => 0
  | .compulsiveControl => 1
  | .dissociation => 0
  | .echoChamberLock => 1
  | .mediocritySaturation => 0

def stallInformationDensity (mode : CopingStallMode) : Nat :=
  if stallPreservesObservation mode then 12 else 3

def preservationScore (mode : CopingStallMode) : Nat :=
  (if stallPreservesObservation mode then 1 else 0) +
  (if stallPreservesAction mode then 1 else 0) +
  (if stallPreservesDiversity mode then 1 else 0) +
  (if stallPreservesControlCost mode then 1 else 0)

def destructionScore (mode : CopingStallMode) : Nat :=
  (if stallDestroysRecovery mode then 1 else 0) +
  (if stallDestroysAction mode then 1 else 0) +
  (if stallDestroysDiversity mode then 1 else 0) +
  (if stallDestroysControlCost mode then 1 else 0)

def entropyTax (mode : CopingStallMode) : Nat :=
  destructionScore mode + stallControlCost mode - preservationScore mode

def mixedSeam (mode : CopingStallMode) : Prop :=
  0 < preservationScore mode ∧ 0 < destructionScore mode

def purePreservationSide (mode : CopingStallMode) : Prop :=
  0 < preservationScore mode ∧ destructionScore mode = 0

def pureDestructionSide (mode : CopingStallMode) : Prop :=
  preservationScore mode = 0 ∧ 0 < destructionScore mode

def preservesInformation (mode : CopingStallMode) : Prop :=
  stallPreservesObservation mode = true ∨ stallPreservesDiversity mode = true

def destroysInformation (mode : CopingStallMode) : Prop :=
  stallDestroysDiversity mode = true

def preservesPhysics (mode : CopingStallMode) : Prop :=
  stallPreservesAction mode = true ∨
    stallPreservesControlCost mode = true ∨
    stallControlCost mode ≤ 8

def destroysPhysics (mode : CopingStallMode) : Prop :=
  stallDestroysRecovery mode = true ∨
    stallDestroysAction mode = true ∨
    stallDestroysControlCost mode = true

def informationConservedPhysicsLost (mode : CopingStallMode) : Prop :=
  preservesInformation mode ∧ destroysPhysics mode

def physicsConservedInformationLost (mode : CopingStallMode) : Prop :=
  preservesPhysics mode ∧ destroysInformation mode

def lossyTransition (mode : CopingStallMode) : Prop :=
  destroysInformation mode ∨ destroysPhysics mode

def perfectCloneTransition (mode : CopingStallMode) : Prop :=
  preservesInformation mode ∧ preservesPhysics mode ∧ ¬ lossyTransition mode

def conservationTransferBoundary (mode : CopingStallMode) : Prop :=
  lossyTransition mode → ¬ perfectCloneTransition mode

def ruminationStallDensity :
    ForkRaceFold.StallDensity :=
  { stall_duration := 12, compression_ratio := 12 }

theorem stall_taxonomy_has_eight_modes :
    copingStallModes.length = 8 := by
  native_decide

theorem rumination_preserves_observation_unlike_suppression :
    stallPreservesObservation .ruminationObservation = true ∧
    stallPreservesObservation .suppressionControl = false ∧
    stallRecoveryValue .suppressionControl <
      stallRecoveryValue .ruminationObservation := by
  native_decide

theorem rumination_is_information_dense_stall :
    10 < ruminationStallDensity.stall_duration := by
  exact ForkRaceFold.stall_is_density ruminationStallDensity rfl (by decide)

theorem rumination_bridges_existing_interference_models :
    PsychologyAsInterference.rumination_loop Gnosis.PhysarumRopelength.ruminationHope Gnosis.PhysarumRopelength.ruminationDespair ∧
    DepressionAsDampedOscillation.rumination_loop Gnosis.PhysarumRopelength.ruminationHope Gnosis.PhysarumRopelength.ruminationDespair := by
  unfold PsychologyAsInterference.rumination_loop
    DepressionAsDampedOscillation.rumination_loop
    Gnosis.PhysarumRopelength.ruminationHope
    Gnosis.PhysarumRopelength.ruminationDespair
  native_decide

theorem rumination_is_contextually_suitable_not_global_optimum :
    Gnosis.PhysarumRopelength.SuitableCopingStrategy Gnosis.PhysarumRopelength.fuckedUpSituation Gnosis.PhysarumRopelength.ruminationFrame ∧
    Gnosis.PhysarumRopelength.EvolutionarilyAdvantageousStall Gnosis.PhysarumRopelength.ruminationFrame
      Gnosis.PhysarumRopelength.negativeApproachFrame ∧
    Gnosis.PhysarumRopelength.inverseControlValue Gnosis.PhysarumRopelength.ruminationFrame <
      Gnosis.PhysarumRopelength.inverseControlValue Gnosis.PhysarumRopelength.inverseControlFrame := by
  exact Gnosis.PhysarumRopelength.rumination_coping_strategy_summary

theorem other_stalls_in_inverse_control_model :
    copingStallModes.length = 8 ∧
    stallDestroysRecovery .learnedHelplessness = true ∧
    stallControlCost .compulsiveControl >
      stallControlCost .panicCascade ∧
    stallRecoveryValue .dissociation = 0 ∧
    stallInformationDensity .ruminationObservation >
      stallInformationDensity .suppressionControl := by
  native_decide

theorem preserve_destroy_sets_line_up :
    purePreservationSide .ruminationObservation ∧
    mixedSeam .panicCascade ∧
    pureDestructionSide .learnedHelplessness ∧
    pureDestructionSide .suppressionControl ∧
    pureDestructionSide .mediocritySaturation := by
  unfold purePreservationSide mixedSeam pureDestructionSide
    preservationScore destructionScore
    stallPreservesObservation stallPreservesAction stallPreservesDiversity
    stallPreservesControlCost stallDestroysRecovery stallDestroysAction
    stallDestroysDiversity stallDestroysControlCost
  native_decide

theorem seam_is_mixed_preservation_and_destruction :
    mixedSeam .panicCascade ∧
    mixedSeam .echoChamberLock ∧
    mixedSeam .compulsiveControl ∧
    mixedSeam .dissociation := by
  unfold mixedSeam preservationScore destructionScore
    stallPreservesObservation stallPreservesAction stallPreservesDiversity
    stallPreservesControlCost stallDestroysRecovery stallDestroysAction
    stallDestroysDiversity stallDestroysControlCost
  native_decide

theorem preservation_destruction_table_summary :
    preservationScore .ruminationObservation >
      destructionScore .ruminationObservation ∧
    destructionScore .suppressionControl >
      preservationScore .suppressionControl ∧
    preservationScore .panicCascade >
      destructionScore .panicCascade ∧
    destructionScore .compulsiveControl =
      preservationScore .compulsiveControl ∧
    destructionScore .learnedHelplessness >
      preservationScore .learnedHelplessness := by
  native_decide

theorem information_physics_dual_seams_line_up :
    informationConservedPhysicsLost .panicCascade ∧
    physicsConservedInformationLost .suppressionControl ∧
    preservesInformation .echoChamberLock ∧
    destroysInformation .echoChamberLock ∧
    ¬ destroysPhysics .echoChamberLock ∧
    ¬ physicsConservedInformationLost .compulsiveControl := by
  unfold informationConservedPhysicsLost physicsConservedInformationLost
    preservesInformation destroysInformation preservesPhysics destroysPhysics
    stallPreservesObservation stallPreservesDiversity
    stallPreservesAction stallPreservesControlCost stallControlCost
    stallDestroysRecovery stallDestroysAction stallDestroysControlCost
    stallDestroysDiversity
  native_decide

theorem same_stall_can_conserve_information_and_physics :
    preservesInformation .panicCascade ∧
    preservesPhysics .panicCascade ∧
    destroysPhysics .panicCascade := by
  unfold preservesInformation preservesPhysics destroysPhysics
    stallPreservesObservation stallPreservesDiversity
    stallPreservesAction stallPreservesControlCost
    stallDestroysRecovery stallDestroysAction stallDestroysControlCost
  native_decide

theorem mediocrity_conserves_neither_axis :
    ¬ preservesInformation .mediocritySaturation ∧
    ¬ preservesPhysics .mediocritySaturation ∧
    destroysInformation .mediocritySaturation ∧
    destroysPhysics .mediocritySaturation := by
  unfold preservesInformation preservesPhysics destroysInformation destroysPhysics
    stallPreservesObservation stallPreservesDiversity
    stallPreservesAction stallPreservesControlCost
    stallDestroysDiversity stallDestroysRecovery stallDestroysAction
    stallDestroysControlCost
  native_decide

theorem lossy_stalls_cannot_clone_physics_and_information :
    conservationTransferBoundary .panicCascade ∧
    conservationTransferBoundary .suppressionControl ∧
    conservationTransferBoundary .echoChamberLock ∧
    conservationTransferBoundary .mediocritySaturation := by
  unfold conservationTransferBoundary perfectCloneTransition lossyTransition
    preservesInformation preservesPhysics destroysInformation destroysPhysics
    stallPreservesObservation stallPreservesDiversity
    stallPreservesAction stallPreservesControlCost stallControlCost
    stallDestroysDiversity stallDestroysRecovery stallDestroysAction
    stallDestroysControlCost
  simp

theorem rumination_is_nonlossy_local_conservation :
    ¬ lossyTransition .ruminationObservation ∧
    perfectCloneTransition .ruminationObservation := by
  constructor
  · unfold lossyTransition destroysInformation destroysPhysics
      stallDestroysDiversity stallDestroysRecovery stallDestroysAction
      stallDestroysControlCost
    native_decide
  · unfold perfectCloneTransition preservesInformation preservesPhysics
      lossyTransition destroysInformation destroysPhysics
      stallPreservesObservation stallPreservesDiversity
      stallPreservesAction stallPreservesControlCost stallControlCost
      stallDestroysDiversity stallDestroysRecovery stallDestroysAction
      stallDestroysControlCost
    native_decide

theorem conservation_law_summary :
    informationConservedPhysicsLost .panicCascade ∧
    physicsConservedInformationLost .suppressionControl ∧
    conservationTransferBoundary .panicCascade ∧
    conservationTransferBoundary .suppressionControl ∧
    ¬ perfectCloneTransition .mediocritySaturation := by
  unfold informationConservedPhysicsLost physicsConservedInformationLost
    conservationTransferBoundary perfectCloneTransition lossyTransition
    preservesInformation preservesPhysics destroysInformation destroysPhysics
    stallPreservesObservation stallPreservesDiversity
    stallPreservesAction stallPreservesControlCost stallControlCost
    stallDestroysDiversity stallDestroysRecovery stallDestroysAction
    stallDestroysControlCost
  simp

theorem entropy_tax_marks_lossy_conservation :
    entropyTax .ruminationObservation < entropyTax .suppressionControl ∧
    entropyTax .ruminationObservation < entropyTax .panicCascade ∧
    entropyTax .panicCascade < entropyTax .mediocritySaturation ∧
    entropyTax .suppressionControl < entropyTax .mediocritySaturation := by
  unfold entropyTax preservationScore destructionScore
    stallControlCost
    stallPreservesObservation stallPreservesAction stallPreservesDiversity
    stallPreservesControlCost
    stallDestroysRecovery stallDestroysAction stallDestroysDiversity
    stallDestroysControlCost
  native_decide

theorem mediocrity_pays_max_entropy_tax_among_named_stalls :
    entropyTax .ruminationObservation < entropyTax .mediocritySaturation ∧
    entropyTax .suppressionControl < entropyTax .mediocritySaturation ∧
    entropyTax .panicCascade < entropyTax .mediocritySaturation ∧
    entropyTax .echoChamberLock < entropyTax .mediocritySaturation ∧
    entropyTax .compulsiveControl < entropyTax .mediocritySaturation ∧
    entropyTax .dissociation < entropyTax .mediocritySaturation := by
  unfold entropyTax preservationScore destructionScore
    stallControlCost
    stallPreservesObservation stallPreservesAction stallPreservesDiversity
    stallPreservesControlCost
    stallDestroysRecovery stallDestroysAction stallDestroysDiversity
    stallDestroysControlCost
  native_decide

theorem rumination_stall_summary :
    PsychologyAsInterference.rumination_loop Gnosis.PhysarumRopelength.ruminationHope Gnosis.PhysarumRopelength.ruminationDespair ∧
    DepressionAsDampedOscillation.rumination_loop Gnosis.PhysarumRopelength.ruminationHope Gnosis.PhysarumRopelength.ruminationDespair ∧
    stallPreservesObservation .ruminationObservation = true ∧
    stallRecoveryValue .suppressionControl <
      stallRecoveryValue .ruminationObservation ∧
    Gnosis.PhysarumRopelength.inverseControlValue Gnosis.PhysarumRopelength.ruminationFrame <
      Gnosis.PhysarumRopelength.inverseControlValue Gnosis.PhysarumRopelength.inverseControlFrame := by
  exact ⟨rumination_bridges_existing_interference_models.left,
    rumination_bridges_existing_interference_models.right,
    rumination_preserves_observation_unlike_suppression.left,
    rumination_preserves_observation_unlike_suppression.right.right,
    rumination_is_contextually_suitable_not_global_optimum.right.right⟩

end Gnosis.RuminationInverseControl
