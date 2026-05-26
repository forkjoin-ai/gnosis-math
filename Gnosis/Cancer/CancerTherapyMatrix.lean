import Init
import Gnosis.Cancer.CancerHackSearch

namespace Gnosis
namespace CancerTherapyMatrix

/-!
# Cancer Therapy Matrix

All-topology / all-therapy matrix layer. The matrix is intentionally blunt:
each cell is a score. A positive score means the therapy can be considered for
that topology under the model; zero means mismatch unless a separate combination
proof lifts it. The nuclear option is admitted only through a benefit/risk gate.
-/

open Gnosis.CancerHackSearch
open Gnosis.CancerTreatmentHypotheses

def mechanismScore
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism) : Nat :=
  if matchedMechanism topology = mechanism then 3 else
  match topology, mechanism with
  | .metastaticPathOpen, .antiAngiogenic => 2
  | .metastaticPathOpen, .surgicalDebulking => 1
  | .proliferativeBulk, .surgicalDebulking => 2
  | .proliferativeBulk, .radiationVentActivation => 2
  | .proliferativeBulk, .thermalAblation => 2
  | .dnaDamageVent, .chemotherapyCytotoxicPressure => 2
  | .dnaDamageVent, .targetedInhibitor => 1
  | _, .nuclearCombination => 1
  | _, _ => 0

def matrixCellAdmissible
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism) : Prop :=
  0 < mechanismScore topology mechanism

def nuclearOptionAdmissible (ctx : TreatmentContext) : Prop :=
  nuclearCombinationAdmissible ctx

def radiationRuntimeGate (ctx : TreatmentContext) : Prop :=
  radiationVentActivated ctx

def chemotherapyRuntimeGate (ctx : TreatmentContext) : Prop :=
  chemotherapyCoversProliferation ctx

def thermalAblationRuntimeGate (ctx : TreatmentContext) : Prop :=
  thermalAblationReachesTumor ctx

def runtimeGateAdmissible
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext) : Prop :=
  treatmentPasses mechanism ctx

def apiAdmissible
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext) : Prop :=
  matrixCellAdmissible topology mechanism ∧ runtimeGateAdmissible mechanism ctx

def selectedMechanism
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism) : Prop :=
  matrixCellAdmissible topology mechanism

def gatedSelectedMember
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext) : Prop :=
  selectedMechanism topology mechanism ∧ apiAdmissible topology mechanism ctx

theorem matched_cell_positive
    (topology : CompromisedTopology) :
    matrixCellAdmissible topology (matchedMechanism topology) := by
  unfold matrixCellAdmissible mechanismScore
  rw [if_pos rfl]
  decide

theorem nuclear_option_requires_benefit_bound
    (ctx : TreatmentContext)
    (hRisk : ctx.nuclearBenefit < ctx.nuclearRisk) :
    ¬ nuclearOptionAdmissible ctx := by
  exact antitheorem_nuclear_combination_fails_when_risk_exceeds_benefit ctx hRisk

theorem runtime_gate_radiation_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.radiationVentActivation ctx ↔
      0 < ctx.radiationFractions ∧ 0 < ctx.radiationVentBeta1 := by
  rfl

theorem runtime_gate_sentinel_vaccine_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.sentinelVaccine ctx ↔
      0 < ctx.antigenSignal ∧ witnessReady ctx := by
  unfold runtimeGateAdmissible treatmentPasses
  rfl

theorem runtime_gate_sieve_checkpoint_reset_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.sieveCheckpointReset ctx ↔
      witnessReady ctx := by
  unfold runtimeGateAdmissible treatmentPasses
  rfl

theorem runtime_gate_apoptosis_restorer_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.apoptosisRestorer ctx ↔
      0 < ctx.apoptosisCapacity := by
  rfl

theorem runtime_gate_route_normalizer_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.routeNormalizer ctx ↔
      routeRestored ctx := by
  rfl

theorem runtime_gate_metabolic_vent_primer_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.metabolicVentPrimer ctx ↔
      metabolicPrimed ctx := by
  rfl

theorem runtime_gate_abscopal_patch_broadcast_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.abscopalPatchBroadcast ctx ↔
      abscopalBroadcastPositive ctx := by
  rfl

theorem runtime_gate_honeytoken_challenge_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.honeytokenChallenge ctx ↔
      baitPositive ctx := by
  rfl

theorem runtime_gate_synthetic_lethal_pair_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.syntheticLethalPair ctx ↔
      syntheticPairPasses ctx := by
  rfl

theorem runtime_gate_metastasis_cutset_seal_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.metastasisCutsetSeal ctx ↔
      ctx.tissueCutsetSealed = true := by
  rfl

theorem runtime_gate_exhaustion_relief_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.exhaustionRelief ctx ↔
      exhaustionRelieved ctx := by
  rfl

theorem runtime_gate_senescence_then_clearance_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.senescenceThenClearance ctx ↔
      senescenceCleared ctx := by
  rfl

theorem runtime_gate_exosome_interdiction_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.exosomeInterdiction ctx ↔
      exosomeBlocked ctx := by
  rfl

theorem runtime_gate_stem_root_purge_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.stemRootPurge ctx ↔
      stemRootCleared ctx := by
  rfl

theorem runtime_gate_chrono_ki_schedule_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.chronoKiSchedule ctx ↔
      chronoWindowHit ctx := by
  rfl

theorem runtime_gate_living_off_land_block_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.livingOffLandBlock ctx ↔
      lotlBlocked ctx := by
  rfl

theorem runtime_gate_chemotherapy_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.chemotherapyCytotoxicPressure ctx ↔
      ctx.proliferativeBurden ≤ ctx.cytotoxicPressure := by
  rfl

theorem runtime_gate_surgical_debulking_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.surgicalDebulking ctx ↔
      surgeryDebulksAccessibleMass ctx := by
  rfl

theorem runtime_gate_targeted_inhibitor_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.targetedInhibitor ctx ↔
      targetedInhibitorCoversDependency ctx := by
  rfl

theorem runtime_gate_hormone_axis_therapy_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.hormoneAxisTherapy ctx ↔
      hormoneAxisTherapyCoversDependence ctx := by
  rfl

theorem runtime_gate_adoptive_cell_therapy_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.adoptiveCellTherapy ctx ↔
      adoptiveCellTherapyReachesTumor ctx := by
  rfl

theorem runtime_gate_oncolytic_virus_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.oncolyticVirus ctx ↔
      oncolyticVirusCanReplicate ctx := by
  rfl

theorem runtime_gate_epigenetic_reprogrammer_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.epigeneticReprogrammer ctx ↔
      epigeneticReprogrammerCoversDrift ctx := by
  rfl

theorem runtime_gate_anti_angiogenic_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.antiAngiogenic ctx ↔
      antiAngiogenicCoversInfrastructure ctx := by
  rfl

theorem runtime_gate_microbiome_modulator_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.microbiomeModulator ctx ↔
      microbiomeModulatorCoversDysbiosis ctx := by
  rfl

theorem runtime_gate_thermal_ablation_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.thermalAblation ctx ↔
      ctx.bulkBurden ≤ ctx.ablationAccess ∧ 0 < ctx.heatDose := by
  rfl

theorem runtime_gate_nuclear_combination_equiv
    (ctx : TreatmentContext) :
    runtimeGateAdmissible TreatmentMechanism.nuclearCombination ctx ↔
      ctx.nuclearRisk ≤ ctx.nuclearBenefit := by
  rfl

theorem api_admissible_equiv
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext) :
    apiAdmissible topology mechanism ctx ↔
      matrixCellAdmissible topology mechanism ∧
        runtimeGateAdmissible mechanism ctx := by
  rfl

theorem api_admissible_requires_positive_matrix_score
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext)
    (h : apiAdmissible topology mechanism ctx) :
    matrixCellAdmissible topology mechanism :=
  h.left

theorem api_admissible_requires_runtime_gate
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext)
    (h : apiAdmissible topology mechanism ctx) :
    runtimeGateAdmissible mechanism ctx :=
  h.right

theorem api_admissible_blocks_zero_score
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext)
    (hZero : mechanismScore topology mechanism = 0) :
    ¬ apiAdmissible topology mechanism ctx := by
  intro h
  unfold apiAdmissible matrixCellAdmissible at h
  rw [hZero] at h
  exact Nat.lt_irrefl 0 h.left

theorem gated_selected_member_equiv
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext) :
    gatedSelectedMember topology mechanism ctx ↔
      selectedMechanism topology mechanism ∧
        apiAdmissible topology mechanism ctx := by
  rfl

theorem gated_selected_member_requires_selection
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext)
    (h : gatedSelectedMember topology mechanism ctx) :
    selectedMechanism topology mechanism :=
  h.left

theorem gated_selected_member_requires_api_admissible
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext)
    (h : gatedSelectedMember topology mechanism ctx) :
    apiAdmissible topology mechanism ctx :=
  h.right

theorem gated_selected_excludes_unselected
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext)
    (hNotSelected : ¬ selectedMechanism topology mechanism) :
    ¬ gatedSelectedMember topology mechanism ctx := by
  intro h
  exact hNotSelected h.left

theorem gated_selected_excludes_not_api_admissible
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism)
    (ctx : TreatmentContext)
    (hNotAdmissible : ¬ apiAdmissible topology mechanism ctx) :
    ¬ gatedSelectedMember topology mechanism ctx := by
  intro h
  exact hNotAdmissible h.right

end CancerTherapyMatrix
end Gnosis
