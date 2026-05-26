import Init
import Gnosis.Cancer.CancerTreatmentHypotheses

namespace Gnosis
namespace CancerHackSearch

/-!
# Cancer Hack Search

The Sandy search algorithm: classify the compromised topology, select matched
interventions, and reject mismatches by antitheorem. This is a formal hypothesis
router, not medical advice.
-/

open Gnosis.CancerTreatmentHypotheses

inductive CompromisedTopology where
  | invisibleAntigen
  | deadSieve
  | missingKillSwitch
  | poisonedRoute
  | metabolicWaste
  | localSignatureOnly
  | hiddenEvasion
  | pairedDeficit
  | metastaticPathOpen
  | exhaustedDefense
  | leakyQuarantine
  | exosomeCargo
  | rootPersistence
  | missedTimingWindow
  | repairHijack
  | dnaDamageVent
  | proliferativeBulk
  deriving DecidableEq, Repr

def matchedMechanism : CompromisedTopology → TreatmentMechanism
  | .invisibleAntigen => .sentinelVaccine
  | .deadSieve => .sieveCheckpointReset
  | .missingKillSwitch => .apoptosisRestorer
  | .poisonedRoute => .routeNormalizer
  | .metabolicWaste => .metabolicVentPrimer
  | .localSignatureOnly => .abscopalPatchBroadcast
  | .hiddenEvasion => .honeytokenChallenge
  | .pairedDeficit => .syntheticLethalPair
  | .metastaticPathOpen => .metastasisCutsetSeal
  | .exhaustedDefense => .exhaustionRelief
  | .leakyQuarantine => .senescenceThenClearance
  | .exosomeCargo => .exosomeInterdiction
  | .rootPersistence => .stemRootPurge
  | .missedTimingWindow => .chronoKiSchedule
  | .repairHijack => .livingOffLandBlock
  | .dnaDamageVent => .radiationVentActivation
  | .proliferativeBulk => .chemotherapyCytotoxicPressure

def topologyMatchesMechanism
    (topology : CompromisedTopology)
    (mechanism : TreatmentMechanism) : Prop :=
  matchedMechanism topology = mechanism

structure SearchResult where
  topology : CompromisedTopology
  mechanism : TreatmentMechanism
  matched : topologyMatchesMechanism topology mechanism

def selectIntervention (topology : CompromisedTopology) : SearchResult :=
  { topology := topology
    mechanism := matchedMechanism topology
    matched := rfl }

theorem selected_intervention_matches
    (topology : CompromisedTopology) :
    topologyMatchesMechanism topology (selectIntervention topology).mechanism :=
  (selectIntervention topology).matched

/-! ## Matched intervention examples -/

theorem invisible_antigen_selects_sentinel :
    topologyMatchesMechanism
      CompromisedTopology.invisibleAntigen
      TreatmentMechanism.sentinelVaccine := by
  unfold topologyMatchesMechanism matchedMechanism
  rfl

theorem poisoned_route_selects_route_normalizer :
    topologyMatchesMechanism
      CompromisedTopology.poisonedRoute
      TreatmentMechanism.routeNormalizer := by
  unfold topologyMatchesMechanism matchedMechanism
  rfl

theorem paired_deficit_selects_synthetic_lethal_pair :
    topologyMatchesMechanism
      CompromisedTopology.pairedDeficit
      TreatmentMechanism.syntheticLethalPair := by
  unfold topologyMatchesMechanism matchedMechanism
  rfl

theorem missed_timing_window_selects_chrono_ki_schedule :
    topologyMatchesMechanism
      CompromisedTopology.missedTimingWindow
      TreatmentMechanism.chronoKiSchedule := by
  unfold topologyMatchesMechanism matchedMechanism
  rfl

theorem dna_damage_vent_selects_radiation :
    topologyMatchesMechanism
      CompromisedTopology.dnaDamageVent
      TreatmentMechanism.radiationVentActivation := by
  unfold topologyMatchesMechanism matchedMechanism
  rfl

theorem proliferative_bulk_selects_chemotherapy :
    topologyMatchesMechanism
      CompromisedTopology.proliferativeBulk
      TreatmentMechanism.chemotherapyCytotoxicPressure := by
  unfold topologyMatchesMechanism matchedMechanism
  rfl

/-! ## Mismatch antitheorems -/

theorem antitheorem_route_poison_not_fixed_by_sentinel_vaccine :
    ¬ topologyMatchesMechanism
      CompromisedTopology.poisonedRoute
      TreatmentMechanism.sentinelVaccine := by
  unfold topologyMatchesMechanism matchedMechanism
  intro h
  cases h

theorem antitheorem_metabolic_waste_not_fixed_by_cutset_seal :
    ¬ topologyMatchesMechanism
      CompromisedTopology.metabolicWaste
      TreatmentMechanism.metastasisCutsetSeal := by
  unfold topologyMatchesMechanism matchedMechanism
  intro h
  cases h

theorem antitheorem_root_persistence_not_fixed_by_abscopal_only :
    ¬ topologyMatchesMechanism
      CompromisedTopology.rootPersistence
      TreatmentMechanism.abscopalPatchBroadcast := by
  unfold topologyMatchesMechanism matchedMechanism
  intro h
  cases h

theorem antitheorem_repair_hijack_not_fixed_by_metabolic_primer :
    ¬ topologyMatchesMechanism
      CompromisedTopology.repairHijack
      TreatmentMechanism.metabolicVentPrimer := by
  unfold topologyMatchesMechanism matchedMechanism
  intro h
  cases h

theorem antitheorem_exhaustion_not_fixed_by_honeytoken_only :
    ¬ topologyMatchesMechanism
      CompromisedTopology.exhaustedDefense
      TreatmentMechanism.honeytokenChallenge := by
  unfold topologyMatchesMechanism matchedMechanism
  intro h
  cases h

theorem antitheorem_radiation_not_matched_to_dead_vent :
    ¬ topologyMatchesMechanism
      CompromisedTopology.missingKillSwitch
      TreatmentMechanism.radiationVentActivation := by
  unfold topologyMatchesMechanism matchedMechanism
  intro h
  cases h

theorem antitheorem_chemo_not_matched_to_dormant_root :
    ¬ topologyMatchesMechanism
      CompromisedTopology.rootPersistence
      TreatmentMechanism.chemotherapyCytotoxicPressure := by
  unfold topologyMatchesMechanism matchedMechanism
  intro h
  cases h

/-! ## Search plus pass gate -/

def selectedPasses (topology : CompromisedTopology) (ctx : TreatmentContext) : Prop :=
  treatmentPasses (matchedMechanism topology) ctx

theorem selected_synthetic_pair_passes_when_chain_crosses_threshold
    (ctx : TreatmentContext)
    (hPair : syntheticPairPasses ctx) :
    selectedPasses CompromisedTopology.pairedDeficit ctx := by
  unfold selectedPasses matchedMechanism
  exact synthetic_lethal_pair_passes_when_chain_crosses_threshold ctx hPair

theorem selected_route_normalizer_fails_when_poison_exceeds_repair
    (ctx : TreatmentContext)
    (hPoison : ctx.routeRepair < ctx.routePoison) :
    ¬ selectedPasses CompromisedTopology.poisonedRoute ctx := by
  unfold selectedPasses matchedMechanism
  exact antitheorem_route_normalizer_fails_when_poison_exceeds_repair ctx hPoison

theorem cancer_hack_search_master :
    topologyMatchesMechanism
      CompromisedTopology.pairedDeficit
      TreatmentMechanism.syntheticLethalPair ∧
    ¬ topologyMatchesMechanism
      CompromisedTopology.poisonedRoute
      TreatmentMechanism.sentinelVaccine := by
  exact ⟨paired_deficit_selects_synthetic_lethal_pair,
    antitheorem_route_poison_not_fixed_by_sentinel_vaccine⟩

end CancerHackSearch
end Gnosis
