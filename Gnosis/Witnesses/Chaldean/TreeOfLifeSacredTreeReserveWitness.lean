import Gnosis.Witnesses.Chaldean.ChaldeanCreationSeriesWitness
import Gnosis.Witnesses.Chaldean.ErrorToTruthFragmentMethodWitness
import Gnosis.Witnesses.Chaldean.KarkartiamatDragonSeaMonsterWitness
import Gnosis.Witnesses.Chaldean.SyrianMediatorTraditionNetworkWitness

namespace Gnosis.Witnesses.Chaldean
namespace TreeOfLifeSacredTreeReserveWitness

/-!
# Tree Of Life Sacred Tree Reserve Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter V
discussion of the Fall and the conclusion.

Smith records strong sacred-tree recurrence without pretending the broken
cuneiform text proves every Genesis connection. The tree of life is one of the
common emblems on seals and larger sculptures, appears even as dress ornament,
and sacred tree/grove language occurs in the legends. He also notes the sacred
grove of Anu, guarded by a sword turning to the four compass points, and scenes
where a complete tree emblem is attended by two cherubim.

The reserve is the point: the present fragments do not directly show Eden or the
Tree of Knowledge, and Smith says no direct connection is known between the tree
and the Fall. Gem engravings make a similar legend probable, including an early
seal with two figures reaching toward fruit while a serpent stands behind one,
but probability is not closure.

No `sorry`, no new `axiom`.
-/

structure SacredTreeEmblemRecurrence where
  treeOfLifeBeliefEvidenced : Bool := true
  commonOnSeals : Bool := true
  commonOnLargerSculptures : Bool := true
  usedOnDresses : Bool := true
  sacredTreeMentionedInLegends : Bool := true
  sacredGroveOfAnuNamed : Bool := true
deriving DecidableEq, Repr

def sacredTreeEmblemRecurrence : SacredTreeEmblemRecurrence := {}

def sacredTreeRecursAcrossMedia (s : SacredTreeEmblemRecurrence) : Prop :=
  s.treeOfLifeBeliefEvidenced = true ∧
  s.commonOnSeals = true ∧
  s.commonOnLargerSculptures = true ∧
  s.usedOnDresses = true ∧
  s.sacredTreeMentionedInLegends = true ∧
  s.sacredGroveOfAnuNamed = true

structure CherubimGuardedTreeBoundary where
  fourPointSwordGuard : Bool := true
  completeTreeAttendedByTwoFigures : Bool := true
  cherubimOneOnEachSide : Bool := true
  sacredEmblemCentered : Bool := true
  wallAndGemImageCarriers : Bool := true
deriving DecidableEq, Repr

def cherubimGuardedTreeBoundary : CherubimGuardedTreeBoundary := {}

def guardedTreeBoundary (g : CherubimGuardedTreeBoundary) : Prop :=
  g.fourPointSwordGuard = true ∧
  g.completeTreeAttendedByTwoFigures = true ∧
  g.cherubimOneOnEachSide = true ∧
  g.sacredEmblemCentered = true ∧
  g.wallAndGemImageCarriers = true

structure FallConnectionReserve where
  edenFragmentsMissing : Bool := true
  treeOfKnowledgeNotInPresentFragments : Bool := true
  directTreeFallConnectionNotKnown : Bool := true
  gemEngravingsMakeSimilarLegendProbable : Bool := true
  probableLegendNotDirectProof : Bool := true
  noClosureWithoutRecoveredText : Bool := true
deriving DecidableEq, Repr

def fallConnectionReserve : FallConnectionReserve := {}

def treeFallConnectionHeldUnderReserve (r : FallConnectionReserve) : Prop :=
  r.edenFragmentsMissing = true ∧
  r.treeOfKnowledgeNotInPresentFragments = true ∧
  r.directTreeFallConnectionNotKnown = true ∧
  r.gemEngravingsMakeSimilarLegendProbable = true ∧
  r.probableLegendNotDirectProof = true ∧
  r.noClosureWithoutRecoveredText = true

structure SerpentFruitSealScene where
  twoFiguresBesideTree : Bool := true
  handsTowardFruit : Bool := true
  serpentBehindOneFigure : Bool := true
  notChanceDevices : Bool := true
  eventsOrLegendFiguresRepresented : Bool := true
  genesisLikeFallFormKnownInBabylonia : Bool := true
deriving DecidableEq, Repr

def serpentFruitSealScene : SerpentFruitSealScene := {}

def serpentFruitImageWitness (i : SerpentFruitSealScene) : Prop :=
  i.twoFiguresBesideTree = true ∧
  i.handsTowardFruit = true ∧
  i.serpentBehindOneFigure = true ∧
  i.notChanceDevices = true ∧
  i.eventsOrLegendFiguresRepresented = true ∧
  i.genesisLikeFallFormKnownInBabylonia = true

theorem sacred_tree_recurs_across_media :
    sacredTreeRecursAcrossMedia sacredTreeEmblemRecurrence := by
  unfold sacredTreeRecursAcrossMedia sacredTreeEmblemRecurrence
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sacred_tree_guarded_boundary :
    guardedTreeBoundary cherubimGuardedTreeBoundary := by
  unfold guardedTreeBoundary cherubimGuardedTreeBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem sacred_tree_fall_connection_held_under_reserve :
    treeFallConnectionHeldUnderReserve fallConnectionReserve := by
  unfold treeFallConnectionHeldUnderReserve fallConnectionReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sacred_tree_serpent_fruit_image_witness :
    serpentFruitImageWitness serpentFruitSealScene := by
  unfold serpentFruitImageWitness serpentFruitSealScene
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sacred_tree_inherits_creation_fall_boundary :
    ChaldeanCreationSeriesWitness.dutyFallBoundary
      ChaldeanCreationSeriesWitness.humanDutyFallBoundary ∧
    KarkartiamatDragonSeaMonsterWitness.seaDragonCarriesFallVector
      KarkartiamatDragonSeaMonsterWitness.dragonFallVector ∧
    treeFallConnectionHeldUnderReserve fallConnectionReserve := by
  exact ⟨ChaldeanCreationSeriesWitness.chaldean_duty_fall_boundary,
    KarkartiamatDragonSeaMonsterWitness.karkartiamat_carries_fall_vector,
    sacred_tree_fall_connection_held_under_reserve⟩

theorem sacred_tree_inherits_syrian_bridge_motif :
    SyrianMediatorTraditionNetworkWitness.syrianMediatorCarrierWitness
      SyrianMediatorTraditionNetworkWitness.syrianBridgeCarrier ∧
    sacredTreeRecursAcrossMedia sacredTreeEmblemRecurrence := by
  exact ⟨SyrianMediatorTraditionNetworkWitness.syrian_mediator_carrier_witness,
    sacred_tree_recurs_across_media⟩

theorem sacred_tree_inherits_error_to_truth_reserve :
    ErrorToTruthFragmentMethodWitness.revisableFragmentMethod
      ErrorToTruthFragmentMethodWitness.fragmentCorrectionDiscipline ∧
    treeFallConnectionHeldUnderReserve fallConnectionReserve := by
  exact ⟨ErrorToTruthFragmentMethodWitness.error_to_truth_revisable_fragment_method,
    sacred_tree_fall_connection_held_under_reserve⟩

theorem tree_of_life_sacred_tree_reserve_witness :
    sacredTreeRecursAcrossMedia sacredTreeEmblemRecurrence ∧
    guardedTreeBoundary cherubimGuardedTreeBoundary ∧
    treeFallConnectionHeldUnderReserve fallConnectionReserve ∧
    serpentFruitImageWitness serpentFruitSealScene := by
  exact ⟨sacred_tree_recurs_across_media,
    sacred_tree_guarded_boundary,
    sacred_tree_fall_connection_held_under_reserve,
    sacred_tree_serpent_fruit_image_witness⟩

end TreeOfLifeSacredTreeReserveWitness
end Gnosis.Witnesses.Chaldean
