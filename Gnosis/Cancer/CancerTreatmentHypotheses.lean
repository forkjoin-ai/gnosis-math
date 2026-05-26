import Init
import Gnosis.Cancer.CancerMeshSecurity

namespace Gnosis
namespace CancerTreatmentHypotheses

/-!
# Cancer Treatment Hypotheses

Research hypotheses generated from `CancerMeshSecurity`. These are not clinical
recommendations. Each candidate is modeled as a bounded mechanism with explicit
pass conditions. Where a seductive treatment story lacks a required support, the
file proves an antitheorem: the story cannot be promoted under this model.
-/

open Gnosis.CancerMeshSecurity

inductive TreatmentMechanism where
  | sentinelVaccine
  | sieveCheckpointReset
  | apoptosisRestorer
  | routeNormalizer
  | metabolicVentPrimer
  | abscopalPatchBroadcast
  | honeytokenChallenge
  | syntheticLethalPair
  | metastasisCutsetSeal
  | exhaustionRelief
  | senescenceThenClearance
  | exosomeInterdiction
  | stemRootPurge
  | chronoKiSchedule
  | livingOffLandBlock
  | radiationVentActivation
  | chemotherapyCytotoxicPressure
  | surgicalDebulking
  | targetedInhibitor
  | hormoneAxisTherapy
  | adoptiveCellTherapy
  | oncolyticVirus
  | epigeneticReprogrammer
  | antiAngiogenic
  | microbiomeModulator
  | thermalAblation
  | nuclearCombination
  deriving DecidableEq, Repr

structure TreatmentContext where
  antigenSignal : Nat
  sieveWitnesses : Nat
  witnessThreshold : Nat
  apoptosisCapacity : Nat
  routePoison : Nat
  routeRepair : Nat
  metabolicWaste : Nat
  ventPrimer : Nat
  siteARejections : Nat
  transferEfficiency : Nat
  baitSignal : Nat
  firstDeficit : Nat
  secondDeficit : Nat
  killThreshold : Nat
  tissueCutsetSealed : Bool
  exhaustionLoad : Nat
  exhaustionRelief : Nat
  senescenceLeak : Nat
  senolyticClearance : Nat
  exosomeCargo : Nat
  exosomeBlockade : Nat
  stemRootPool : Nat
  rootPurge : Nat
  reactionTime : Nat
  vulnerabilityWindow : Nat
  repairHijack : Bool
  lotlBlock : Bool
  radiationFractions : Nat
  radiationVentBeta1 : Nat
  proliferativeBurden : Nat
  cytotoxicPressure : Nat
  surgicalAccess : Nat
  bulkBurden : Nat
  targetDependency : Nat
  inhibitorPressure : Nat
  hormoneDependence : Nat
  hormoneBlockade : Nat
  cellTherapyFitness : Nat
  immuneAccess : Nat
  viralPermissivity : Nat
  viralPayload : Nat
  epigeneticDrift : Nat
  reprogrammingPressure : Nat
  angiogenesisBurden : Nat
  angiogenicBlockade : Nat
  dysbiosisBurden : Nat
  microbiomeCorrection : Nat
  ablationAccess : Nat
  heatDose : Nat
  nuclearBenefit : Nat
  nuclearRisk : Nat
  deriving DecidableEq, Repr

def witnessReady (ctx : TreatmentContext) : Prop :=
  ctx.witnessThreshold ≤ ctx.sieveWitnesses

def routeRestored (ctx : TreatmentContext) : Prop :=
  ctx.routePoison ≤ ctx.routeRepair

def metabolicPrimed (ctx : TreatmentContext) : Prop :=
  ctx.metabolicWaste ≤ ctx.ventPrimer

def abscopalBroadcastPositive (ctx : TreatmentContext) : Prop :=
  0 < ctx.siteARejections * ctx.transferEfficiency

def baitPositive (ctx : TreatmentContext) : Prop :=
  0 < ctx.baitSignal

def syntheticPairPasses (ctx : TreatmentContext) : Prop :=
  ctx.killThreshold ≤ ctx.firstDeficit + ctx.secondDeficit

def exhaustionRelieved (ctx : TreatmentContext) : Prop :=
  ctx.exhaustionLoad ≤ ctx.exhaustionRelief

def senescenceCleared (ctx : TreatmentContext) : Prop :=
  ctx.senescenceLeak ≤ ctx.senolyticClearance

def exosomeBlocked (ctx : TreatmentContext) : Prop :=
  ctx.exosomeCargo ≤ ctx.exosomeBlockade

def stemRootCleared (ctx : TreatmentContext) : Prop :=
  ctx.stemRootPool ≤ ctx.rootPurge

def chronoWindowHit (ctx : TreatmentContext) : Prop :=
  ctx.reactionTime ≤ ctx.vulnerabilityWindow

def lotlBlocked (ctx : TreatmentContext) : Prop :=
  ctx.repairHijack = true ∧ ctx.lotlBlock = true

def radiationVentActivated (ctx : TreatmentContext) : Prop :=
  0 < ctx.radiationFractions ∧ 0 < ctx.radiationVentBeta1

def chemotherapyCoversProliferation (ctx : TreatmentContext) : Prop :=
  ctx.proliferativeBurden ≤ ctx.cytotoxicPressure

def surgeryDebulksAccessibleMass (ctx : TreatmentContext) : Prop :=
  ctx.bulkBurden ≤ ctx.surgicalAccess

def targetedInhibitorCoversDependency (ctx : TreatmentContext) : Prop :=
  ctx.targetDependency ≤ ctx.inhibitorPressure

def hormoneAxisTherapyCoversDependence (ctx : TreatmentContext) : Prop :=
  ctx.hormoneDependence ≤ ctx.hormoneBlockade

def adoptiveCellTherapyReachesTumor (ctx : TreatmentContext) : Prop :=
  ctx.cellTherapyFitness ≤ ctx.immuneAccess

def oncolyticVirusCanReplicate (ctx : TreatmentContext) : Prop :=
  0 < ctx.viralPermissivity ∧ 0 < ctx.viralPayload

def epigeneticReprogrammerCoversDrift (ctx : TreatmentContext) : Prop :=
  ctx.epigeneticDrift ≤ ctx.reprogrammingPressure

def antiAngiogenicCoversInfrastructure (ctx : TreatmentContext) : Prop :=
  ctx.angiogenesisBurden ≤ ctx.angiogenicBlockade

def microbiomeModulatorCoversDysbiosis (ctx : TreatmentContext) : Prop :=
  ctx.dysbiosisBurden ≤ ctx.microbiomeCorrection

def thermalAblationReachesTumor (ctx : TreatmentContext) : Prop :=
  ctx.bulkBurden ≤ ctx.ablationAccess ∧ 0 < ctx.heatDose

def nuclearCombinationAdmissible (ctx : TreatmentContext) : Prop :=
  ctx.nuclearRisk ≤ ctx.nuclearBenefit

def treatmentPasses (mechanism : TreatmentMechanism) (ctx : TreatmentContext) : Prop :=
  match mechanism with
  | .sentinelVaccine => 0 < ctx.antigenSignal ∧ witnessReady ctx
  | .sieveCheckpointReset => witnessReady ctx
  | .apoptosisRestorer => 0 < ctx.apoptosisCapacity
  | .routeNormalizer => routeRestored ctx
  | .metabolicVentPrimer => metabolicPrimed ctx
  | .abscopalPatchBroadcast => abscopalBroadcastPositive ctx
  | .honeytokenChallenge => baitPositive ctx
  | .syntheticLethalPair => syntheticPairPasses ctx
  | .metastasisCutsetSeal => ctx.tissueCutsetSealed = true
  | .exhaustionRelief => exhaustionRelieved ctx
  | .senescenceThenClearance => senescenceCleared ctx
  | .exosomeInterdiction => exosomeBlocked ctx
  | .stemRootPurge => stemRootCleared ctx
  | .chronoKiSchedule => chronoWindowHit ctx
  | .livingOffLandBlock => lotlBlocked ctx
  | .radiationVentActivation => radiationVentActivated ctx
  | .chemotherapyCytotoxicPressure => chemotherapyCoversProliferation ctx
  | .surgicalDebulking => surgeryDebulksAccessibleMass ctx
  | .targetedInhibitor => targetedInhibitorCoversDependency ctx
  | .hormoneAxisTherapy => hormoneAxisTherapyCoversDependence ctx
  | .adoptiveCellTherapy => adoptiveCellTherapyReachesTumor ctx
  | .oncolyticVirus => oncolyticVirusCanReplicate ctx
  | .epigeneticReprogrammer => epigeneticReprogrammerCoversDrift ctx
  | .antiAngiogenic => antiAngiogenicCoversInfrastructure ctx
  | .microbiomeModulator => microbiomeModulatorCoversDysbiosis ctx
  | .thermalAblation => thermalAblationReachesTumor ctx
  | .nuclearCombination => nuclearCombinationAdmissible ctx

/-! ## Passing hypotheses -/

theorem sentinel_vaccine_passes_with_antigen_and_witnesses
    (ctx : TreatmentContext)
    (hAntigen : 0 < ctx.antigenSignal)
    (hWitness : witnessReady ctx) :
    treatmentPasses TreatmentMechanism.sentinelVaccine ctx :=
  ⟨hAntigen, hWitness⟩

theorem sieve_checkpoint_reset_passes_with_witnesses
    (ctx : TreatmentContext)
    (hWitness : witnessReady ctx) :
    treatmentPasses TreatmentMechanism.sieveCheckpointReset ctx :=
  hWitness

theorem apoptosis_restorer_passes_with_capacity
    (ctx : TreatmentContext)
    (hCapacity : 0 < ctx.apoptosisCapacity) :
    treatmentPasses TreatmentMechanism.apoptosisRestorer ctx :=
  hCapacity

theorem route_normalizer_passes_when_repair_covers_poison
    (ctx : TreatmentContext)
    (hRoute : routeRestored ctx) :
    treatmentPasses TreatmentMechanism.routeNormalizer ctx :=
  hRoute

theorem metabolic_vent_primer_passes_when_primer_covers_waste
    (ctx : TreatmentContext)
    (hPrime : metabolicPrimed ctx) :
    treatmentPasses TreatmentMechanism.metabolicVentPrimer ctx :=
  hPrime

theorem abscopal_patch_broadcast_passes_with_positive_transfer
    (ctx : TreatmentContext)
    (hBroadcast : abscopalBroadcastPositive ctx) :
    treatmentPasses TreatmentMechanism.abscopalPatchBroadcast ctx :=
  hBroadcast

theorem honeytoken_challenge_passes_with_positive_bait
    (ctx : TreatmentContext)
    (hBait : baitPositive ctx) :
    treatmentPasses TreatmentMechanism.honeytokenChallenge ctx :=
  hBait

theorem synthetic_lethal_pair_passes_when_chain_crosses_threshold
    (ctx : TreatmentContext)
    (hPair : syntheticPairPasses ctx) :
    treatmentPasses TreatmentMechanism.syntheticLethalPair ctx :=
  hPair

theorem metastasis_cutset_seal_passes_when_tissue_cutset_sealed
    (ctx : TreatmentContext)
    (hSeal : ctx.tissueCutsetSealed = true) :
    treatmentPasses TreatmentMechanism.metastasisCutsetSeal ctx :=
  hSeal

theorem exhaustion_relief_passes_when_relief_covers_load
    (ctx : TreatmentContext)
    (hRelief : exhaustionRelieved ctx) :
    treatmentPasses TreatmentMechanism.exhaustionRelief ctx :=
  hRelief

theorem senescence_then_clearance_passes_when_clearance_covers_leak
    (ctx : TreatmentContext)
    (hClear : senescenceCleared ctx) :
    treatmentPasses TreatmentMechanism.senescenceThenClearance ctx :=
  hClear

theorem exosome_interdiction_passes_when_blockade_covers_cargo
    (ctx : TreatmentContext)
    (hBlock : exosomeBlocked ctx) :
    treatmentPasses TreatmentMechanism.exosomeInterdiction ctx :=
  hBlock

theorem stem_root_purge_passes_when_purge_covers_root
    (ctx : TreatmentContext)
    (hPurge : stemRootCleared ctx) :
    treatmentPasses TreatmentMechanism.stemRootPurge ctx :=
  hPurge

theorem chrono_ki_schedule_passes_inside_window
    (ctx : TreatmentContext)
    (hWindow : chronoWindowHit ctx) :
    treatmentPasses TreatmentMechanism.chronoKiSchedule ctx :=
  hWindow

theorem living_off_land_block_passes_when_hijack_and_block_present
    (ctx : TreatmentContext)
    (hLotl : lotlBlocked ctx) :
    treatmentPasses TreatmentMechanism.livingOffLandBlock ctx :=
  hLotl

theorem radiation_vent_activation_passes_with_fraction_and_vent
    (ctx : TreatmentContext)
    (hRadiation : radiationVentActivated ctx) :
    treatmentPasses TreatmentMechanism.radiationVentActivation ctx :=
  hRadiation

theorem chemotherapy_cytotoxic_pressure_passes_when_pressure_covers_burden
    (ctx : TreatmentContext)
    (hChemo : chemotherapyCoversProliferation ctx) :
    treatmentPasses TreatmentMechanism.chemotherapyCytotoxicPressure ctx :=
  hChemo

theorem surgical_debulking_passes_when_access_covers_bulk
    (ctx : TreatmentContext)
    (hSurgery : surgeryDebulksAccessibleMass ctx) :
    treatmentPasses TreatmentMechanism.surgicalDebulking ctx :=
  hSurgery

theorem targeted_inhibitor_passes_when_pressure_covers_dependency
    (ctx : TreatmentContext)
    (hTarget : targetedInhibitorCoversDependency ctx) :
    treatmentPasses TreatmentMechanism.targetedInhibitor ctx :=
  hTarget

theorem hormone_axis_therapy_passes_when_blockade_covers_dependence
    (ctx : TreatmentContext)
    (hHormone : hormoneAxisTherapyCoversDependence ctx) :
    treatmentPasses TreatmentMechanism.hormoneAxisTherapy ctx :=
  hHormone

theorem adoptive_cell_therapy_passes_when_access_covers_fitness
    (ctx : TreatmentContext)
    (hCell : adoptiveCellTherapyReachesTumor ctx) :
    treatmentPasses TreatmentMechanism.adoptiveCellTherapy ctx :=
  hCell

theorem oncolytic_virus_passes_when_permissive_and_loaded
    (ctx : TreatmentContext)
    (hVirus : oncolyticVirusCanReplicate ctx) :
    treatmentPasses TreatmentMechanism.oncolyticVirus ctx :=
  hVirus

theorem epigenetic_reprogrammer_passes_when_pressure_covers_drift
    (ctx : TreatmentContext)
    (hEpi : epigeneticReprogrammerCoversDrift ctx) :
    treatmentPasses TreatmentMechanism.epigeneticReprogrammer ctx :=
  hEpi

theorem anti_angiogenic_passes_when_blockade_covers_infra
    (ctx : TreatmentContext)
    (hAngio : antiAngiogenicCoversInfrastructure ctx) :
    treatmentPasses TreatmentMechanism.antiAngiogenic ctx :=
  hAngio

theorem microbiome_modulator_passes_when_correction_covers_dysbiosis
    (ctx : TreatmentContext)
    (hMicro : microbiomeModulatorCoversDysbiosis ctx) :
    treatmentPasses TreatmentMechanism.microbiomeModulator ctx :=
  hMicro

theorem thermal_ablation_passes_when_access_and_heat
    (ctx : TreatmentContext)
    (hThermal : thermalAblationReachesTumor ctx) :
    treatmentPasses TreatmentMechanism.thermalAblation ctx :=
  hThermal

theorem nuclear_combination_passes_only_when_benefit_bounds_risk
    (ctx : TreatmentContext)
    (hNuclear : nuclearCombinationAdmissible ctx) :
    treatmentPasses TreatmentMechanism.nuclearCombination ctx :=
  hNuclear

/-! ## Antitheorems: failure gates -/

theorem antitheorem_sentinel_vaccine_fails_without_antigen
    (ctx : TreatmentContext)
    (hNoAntigen : ctx.antigenSignal = 0) :
    ¬ treatmentPasses TreatmentMechanism.sentinelVaccine ctx := by
  intro hPass
  unfold treatmentPasses at hPass
  rw [hNoAntigen] at hPass
  exact Nat.lt_irrefl 0 hPass.left

theorem antitheorem_sieve_reset_fails_without_witnesses
    (ctx : TreatmentContext)
    (hWitnessGap : ctx.sieveWitnesses < ctx.witnessThreshold) :
    ¬ treatmentPasses TreatmentMechanism.sieveCheckpointReset ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hWitnessGap

theorem antitheorem_apoptosis_restorer_fails_without_capacity
    (ctx : TreatmentContext)
    (hNoCapacity : ctx.apoptosisCapacity = 0) :
    ¬ treatmentPasses TreatmentMechanism.apoptosisRestorer ctx := by
  intro hPass
  unfold treatmentPasses at hPass
  rw [hNoCapacity] at hPass
  exact Nat.lt_irrefl 0 hPass

theorem antitheorem_route_normalizer_fails_when_poison_exceeds_repair
    (ctx : TreatmentContext)
    (hPoison : ctx.routeRepair < ctx.routePoison) :
    ¬ treatmentPasses TreatmentMechanism.routeNormalizer ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hPoison

theorem antitheorem_metabolic_primer_fails_when_waste_exceeds_primer
    (ctx : TreatmentContext)
    (hWaste : ctx.ventPrimer < ctx.metabolicWaste) :
    ¬ treatmentPasses TreatmentMechanism.metabolicVentPrimer ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hWaste

theorem antitheorem_abscopal_broadcast_fails_without_transfer
    (ctx : TreatmentContext)
    (hNoTransfer : ctx.transferEfficiency = 0) :
    ¬ treatmentPasses TreatmentMechanism.abscopalPatchBroadcast ctx := by
  intro hPass
  unfold treatmentPasses abscopalBroadcastPositive at hPass
  rw [hNoTransfer, Nat.mul_zero] at hPass
  exact Nat.lt_irrefl 0 hPass

theorem antitheorem_honeytoken_fails_without_bait
    (ctx : TreatmentContext)
    (hNoBait : ctx.baitSignal = 0) :
    ¬ treatmentPasses TreatmentMechanism.honeytokenChallenge ctx := by
  intro hPass
  unfold treatmentPasses baitPositive at hPass
  rw [hNoBait] at hPass
  exact Nat.lt_irrefl 0 hPass

theorem antitheorem_synthetic_pair_fails_below_threshold
    (ctx : TreatmentContext)
    (hBelow : ctx.firstDeficit + ctx.secondDeficit < ctx.killThreshold) :
    ¬ treatmentPasses TreatmentMechanism.syntheticLethalPair ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hBelow

theorem antitheorem_metastasis_cutset_fails_when_unsealed
    (ctx : TreatmentContext)
    (hOpen : ctx.tissueCutsetSealed = false) :
    ¬ treatmentPasses TreatmentMechanism.metastasisCutsetSeal ctx := by
  intro hPass
  unfold treatmentPasses at hPass
  rw [hOpen] at hPass
  cases hPass

theorem antitheorem_exhaustion_relief_fails_when_load_exceeds_relief
    (ctx : TreatmentContext)
    (hLoad : ctx.exhaustionRelief < ctx.exhaustionLoad) :
    ¬ treatmentPasses TreatmentMechanism.exhaustionRelief ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hLoad

theorem antitheorem_senescence_clearance_fails_when_leak_exceeds_clearance
    (ctx : TreatmentContext)
    (hLeak : ctx.senolyticClearance < ctx.senescenceLeak) :
    ¬ treatmentPasses TreatmentMechanism.senescenceThenClearance ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hLeak

theorem antitheorem_exosome_interdiction_fails_when_cargo_exceeds_blockade
    (ctx : TreatmentContext)
    (hCargo : ctx.exosomeBlockade < ctx.exosomeCargo) :
    ¬ treatmentPasses TreatmentMechanism.exosomeInterdiction ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hCargo

theorem antitheorem_stem_root_purge_fails_when_root_exceeds_purge
    (ctx : TreatmentContext)
    (hRoot : ctx.rootPurge < ctx.stemRootPool) :
    ¬ treatmentPasses TreatmentMechanism.stemRootPurge ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hRoot

theorem antitheorem_chrono_schedule_fails_outside_window
    (ctx : TreatmentContext)
    (hLate : ctx.vulnerabilityWindow < ctx.reactionTime) :
    ¬ treatmentPasses TreatmentMechanism.chronoKiSchedule ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hLate

theorem antitheorem_lotl_block_fails_without_block
    (ctx : TreatmentContext)
    (hNoBlock : ctx.lotlBlock = false) :
    ¬ treatmentPasses TreatmentMechanism.livingOffLandBlock ctx := by
  intro hPass
  unfold treatmentPasses lotlBlocked at hPass
  rw [hNoBlock] at hPass
  cases hPass.right

theorem antitheorem_radiation_fails_without_fraction
    (ctx : TreatmentContext)
    (hNoFraction : ctx.radiationFractions = 0) :
    ¬ treatmentPasses TreatmentMechanism.radiationVentActivation ctx := by
  intro hPass
  unfold treatmentPasses radiationVentActivated at hPass
  rw [hNoFraction] at hPass
  exact Nat.lt_irrefl 0 hPass.left

theorem antitheorem_radiation_fails_without_vent
    (ctx : TreatmentContext)
    (hNoVent : ctx.radiationVentBeta1 = 0) :
    ¬ treatmentPasses TreatmentMechanism.radiationVentActivation ctx := by
  intro hPass
  unfold treatmentPasses radiationVentActivated at hPass
  rw [hNoVent] at hPass
  exact Nat.lt_irrefl 0 hPass.right

theorem antitheorem_chemo_fails_when_burden_exceeds_pressure
    (ctx : TreatmentContext)
    (hBurden : ctx.cytotoxicPressure < ctx.proliferativeBurden) :
    ¬ treatmentPasses TreatmentMechanism.chemotherapyCytotoxicPressure ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hBurden

theorem antitheorem_surgery_fails_when_bulk_exceeds_access
    (ctx : TreatmentContext)
    (hBulk : ctx.surgicalAccess < ctx.bulkBurden) :
    ¬ treatmentPasses TreatmentMechanism.surgicalDebulking ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hBulk

theorem antitheorem_targeted_inhibitor_fails_when_dependency_exceeds_pressure
    (ctx : TreatmentContext)
    (hDependency : ctx.inhibitorPressure < ctx.targetDependency) :
    ¬ treatmentPasses TreatmentMechanism.targetedInhibitor ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hDependency

theorem antitheorem_hormone_therapy_fails_when_dependence_exceeds_blockade
    (ctx : TreatmentContext)
    (hHormone : ctx.hormoneBlockade < ctx.hormoneDependence) :
    ¬ treatmentPasses TreatmentMechanism.hormoneAxisTherapy ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hHormone

theorem antitheorem_adoptive_cell_fails_when_access_below_fitness
    (ctx : TreatmentContext)
    (hCell : ctx.immuneAccess < ctx.cellTherapyFitness) :
    ¬ treatmentPasses TreatmentMechanism.adoptiveCellTherapy ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hCell

theorem antitheorem_oncolytic_virus_fails_without_permissivity
    (ctx : TreatmentContext)
    (hNoPermissivity : ctx.viralPermissivity = 0) :
    ¬ treatmentPasses TreatmentMechanism.oncolyticVirus ctx := by
  intro hPass
  unfold treatmentPasses oncolyticVirusCanReplicate at hPass
  rw [hNoPermissivity] at hPass
  exact Nat.lt_irrefl 0 hPass.left

theorem antitheorem_epigenetic_reprogrammer_fails_when_drift_exceeds_pressure
    (ctx : TreatmentContext)
    (hDrift : ctx.reprogrammingPressure < ctx.epigeneticDrift) :
    ¬ treatmentPasses TreatmentMechanism.epigeneticReprogrammer ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hDrift

theorem antitheorem_anti_angiogenic_fails_when_infra_exceeds_blockade
    (ctx : TreatmentContext)
    (hInfra : ctx.angiogenicBlockade < ctx.angiogenesisBurden) :
    ¬ treatmentPasses TreatmentMechanism.antiAngiogenic ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hInfra

theorem antitheorem_microbiome_modulator_fails_when_dysbiosis_exceeds_correction
    (ctx : TreatmentContext)
    (hDysbiosis : ctx.microbiomeCorrection < ctx.dysbiosisBurden) :
    ¬ treatmentPasses TreatmentMechanism.microbiomeModulator ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hDysbiosis

theorem antitheorem_thermal_ablation_fails_without_heat
    (ctx : TreatmentContext)
    (hNoHeat : ctx.heatDose = 0) :
    ¬ treatmentPasses TreatmentMechanism.thermalAblation ctx := by
  intro hPass
  unfold treatmentPasses thermalAblationReachesTumor at hPass
  rw [hNoHeat] at hPass
  exact Nat.lt_irrefl 0 hPass.right

theorem antitheorem_nuclear_combination_fails_when_risk_exceeds_benefit
    (ctx : TreatmentContext)
    (hRisk : ctx.nuclearBenefit < ctx.nuclearRisk) :
    ¬ treatmentPasses TreatmentMechanism.nuclearCombination ctx := by
  intro hPass
  exact Nat.not_lt_of_ge hPass hRisk

theorem treatment_hypotheses_master :
    (∀ ctx, 0 < ctx.antigenSignal → witnessReady ctx →
      treatmentPasses TreatmentMechanism.sentinelVaccine ctx) ∧
    (∀ ctx, syntheticPairPasses ctx →
      treatmentPasses TreatmentMechanism.syntheticLethalPair ctx) ∧
    (∀ ctx, ctx.antigenSignal = 0 →
      ¬ treatmentPasses TreatmentMechanism.sentinelVaccine ctx) ∧
    (∀ ctx, ctx.firstDeficit + ctx.secondDeficit < ctx.killThreshold →
      ¬ treatmentPasses TreatmentMechanism.syntheticLethalPair ctx) := by
  exact ⟨sentinel_vaccine_passes_with_antigen_and_witnesses,
    synthetic_lethal_pair_passes_when_chain_crosses_threshold,
    antitheorem_sentinel_vaccine_fails_without_antigen,
    antitheorem_synthetic_pair_fails_below_threshold⟩

end CancerTreatmentHypotheses
end Gnosis
