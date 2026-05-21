import Gnosis.Witnesses.Chaldean.ComparativeFloodMethodReserveWitness
import Gnosis.Witnesses.Chaldean.CuthaCompositeCreatureWitness
import Gnosis.Witnesses.Chaldean.IzdubarErechReturnCityBoundaryWitness

namespace Gnosis.Witnesses.Chaldean
namespace SyrianMediatorTraditionNetworkWitness

/-!
# Syrian Mediator Tradition Network Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter XII
conclusion, after the Genesis/Deluge comparison.

Smith gives a crucial bridge topology. Three ancient lists have ten names
Egyptian gods, Jewish patriarchs, and Chaldean kings. He says the shared count
cannot be accidental, but the names do not resemble each other and appear
independent. The missing connection may lie in the old Syrian peoples'
literature, if it is ever recovered. A ninth-century Syrian chief's seal
already shows sacred tree and composite-being motifs similar to Babylonia.

That is the mediator network: not a direct-copy edge, but a lost carrier layer
between Babylonia and Palestine, with Syria/Harran/Euphrates routes preserving
the topology while changing names.

No `sorry`, no new `axiom`.
-/

structure TenNameNonAccidentalRecurrence where
  egyptianGodListHasTen : Bool := true
  jewishPatriarchListHasTen : Bool := true
  chaldeanKingListHasTen : Bool := true
  sharedTenNotAccidental : Bool := true
  namesIndependentInOrigin : Bool := true
  connectionCurrentlyUnknown : Bool := true
deriving DecidableEq, Repr

def tenNameNonAccidentalRecurrence : TenNameNonAccidentalRecurrence := {}

def tenNameRecurrenceUnderReserve (t : TenNameNonAccidentalRecurrence) : Prop :=
  t.egyptianGodListHasTen = true ∧
  t.jewishPatriarchListHasTen = true ∧
  t.chaldeanKingListHasTen = true ∧
  t.sharedTenNotAccidental = true ∧
  t.namesIndependentInOrigin = true ∧
  t.connectionCurrentlyUnknown = true

structure SyrianBridgeCarrier where
  oldSyrianLiteratureMayRecoverConnection : Bool := true
  syrianChiefSealWitness : Bool := true
  sacredTreeMotifPresent : Bool := true
  compositeBeingsMotifPresent : Bool := true
  similarStoriesAndIdeasPresent : Bool := true
  mediatorCarrierNotDirectCopy : Bool := true
deriving DecidableEq, Repr

def syrianBridgeCarrier : SyrianBridgeCarrier := {}

def syrianMediatorCarrierWitness (s : SyrianBridgeCarrier) : Prop :=
  s.oldSyrianLiteratureMayRecoverConnection = true ∧
  s.syrianChiefSealWitness = true ∧
  s.sacredTreeMotifPresent = true ∧
  s.compositeBeingsMotifPresent = true ∧
  s.similarStoriesAndIdeasPresent = true ∧
  s.mediatorCarrierNotDirectCopy = true

structure EuphratesTraditionRoute where
  traditionsNotFixedNearPalestine : Bool := true
  euphratesValleyLocalization : Bool := true
  edenByEuphratesAndTigris : Bool := true
  preFloodCitiesNamed : Bool := true
  surippakArkCityNamed : Bool := true
  babylonTowerSiteNamed : Bool := true
  urToHarranToPalestineMigration : Bool := true
deriving DecidableEq, Repr

def euphratesTraditionRoute : EuphratesTraditionRoute := {}

def euphratesCarrierRoute (e : EuphratesTraditionRoute) : Prop :=
  e.traditionsNotFixedNearPalestine = true ∧
  e.euphratesValleyLocalization = true ∧
  e.edenByEuphratesAndTigris = true ∧
  e.preFloodCitiesNamed = true ∧
  e.surippakArkCityNamed = true ∧
  e.babylonTowerSiteNamed = true ∧
  e.urToHarranToPalestineMigration = true

structure DecisionReserve where
  chaldeanOriginalHomeHypothesisSupported : Bool := true
  strikingDifferencesRemain : Bool := true
  patriarchNamesDiffer : Bool := true
  furtherInformationRequired : Bool := true
  borrowingQuestionAskedInVainForNow : Bool := true
deriving DecidableEq, Repr

def decisionReserve : DecisionReserve := {}

def borrowingDecisionHeldOpen (d : DecisionReserve) : Prop :=
  d.chaldeanOriginalHomeHypothesisSupported = true ∧
  d.strikingDifferencesRemain = true ∧
  d.patriarchNamesDiffer = true ∧
  d.furtherInformationRequired = true ∧
  d.borrowingQuestionAskedInVainForNow = true

theorem syrian_ten_name_recurrence_under_reserve :
    tenNameRecurrenceUnderReserve tenNameNonAccidentalRecurrence := by
  unfold tenNameRecurrenceUnderReserve tenNameNonAccidentalRecurrence
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem syrian_mediator_carrier_witness :
    syrianMediatorCarrierWitness syrianBridgeCarrier := by
  unfold syrianMediatorCarrierWitness syrianBridgeCarrier
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem syrian_euphrates_carrier_route :
    euphratesCarrierRoute euphratesTraditionRoute := by
  unfold euphratesCarrierRoute euphratesTraditionRoute
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem syrian_borrowing_decision_held_open :
    borrowingDecisionHeldOpen decisionReserve := by
  unfold borrowingDecisionHeldOpen decisionReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem syrian_inherits_mediator_archive_hole :
    ComparativeFloodMethodReserveWitness.mediatorArchiveHole
      ComparativeFloodMethodReserveWitness.lostMediatorTraditions ∧
    syrianMediatorCarrierWitness syrianBridgeCarrier ∧
    borrowingDecisionHeldOpen decisionReserve := by
  exact ⟨ComparativeFloodMethodReserveWitness.comparative_mediator_archive_hole,
    syrian_mediator_carrier_witness,
    syrian_borrowing_decision_held_open⟩

theorem syrian_inherits_composite_creature_bridge :
    CuthaCompositeCreatureWitness.turbidCompositeCreatureLayer
      CuthaCompositeCreatureWitness.cuthaWaterCreatureLayer ∧
    syrianMediatorCarrierWitness syrianBridgeCarrier := by
  exact ⟨CuthaCompositeCreatureWitness.cutha_turbid_composite_creature_layer,
    syrian_mediator_carrier_witness⟩

theorem syrian_inherits_city_boundary_route :
    IzdubarErechReturnCityBoundaryWitness.erechBoundaryMeasured
      IzdubarErechReturnCityBoundaryWitness.cityBoundarySurvey ∧
    euphratesCarrierRoute euphratesTraditionRoute := by
  exact ⟨IzdubarErechReturnCityBoundaryWitness.izdubar_erech_boundary_measured,
    syrian_euphrates_carrier_route⟩

theorem syrian_mediator_tradition_network_witness :
    tenNameRecurrenceUnderReserve tenNameNonAccidentalRecurrence ∧
    syrianMediatorCarrierWitness syrianBridgeCarrier ∧
    euphratesCarrierRoute euphratesTraditionRoute ∧
    borrowingDecisionHeldOpen decisionReserve := by
  exact ⟨syrian_ten_name_recurrence_under_reserve,
    syrian_mediator_carrier_witness,
    syrian_euphrates_carrier_route,
    syrian_borrowing_decision_held_open⟩

end SyrianMediatorTraditionNetworkWitness
end Gnosis.Witnesses.Chaldean
