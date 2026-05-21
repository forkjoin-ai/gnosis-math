import Gnosis.Witnesses.Chaldean.SyrianMediatorTraditionNetworkWitness

namespace Gnosis.Witnesses.Chaldean
namespace GenesisNameMigrationWitness

/-!
# Genesis Name Migration Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter XVII
conclusion, "Notices of Genesis" and detached patriarchal-name evidence.

Smith's point is not that Genesis names appear as a clean patriarch list in the
mythical-period inscriptions. They do not. The witness is dispersed: Adam
appears as a general word for man; Cain, Enoch, and Noah correspond to
Babylonian roots; Cainan appears as a Babylonian town-name and Canaanite label;
Lamech appears through Phoenician and cuneiform moon-name forms; Tubal-Cain
maps by name and craft to fire/metalworker Bil-kan; post-flood names such as
Reu/Ragu, Serug, and Harran appear as Syrian town names; Abram and Ishmael
surface later in Assyrian/Babylonian documentary contexts.

This is name migration, not name identity. Names move through roots, towns,
trades, divine titles, documents, and routes.

No `sorry`, no new `axiom`.
-/

structure RootNameCorrespondence where
  adamGeneralManNotProperName : Bool := true
  cainRootUprightRight : Bool := true
  enochRootWise : Bool := true
  noahRootRestSatisfaction : Bool := true
  cleanMythicPatriarchListAbsent : Bool := true
deriving DecidableEq, Repr

def rootNameCorrespondence : RootNameCorrespondence := {}

def rootsPreserveNameTraces (r : RootNameCorrespondence) : Prop :=
  r.adamGeneralManNotProperName = true ∧
  r.cainRootUprightRight = true ∧
  r.enochRootWise = true ∧
  r.noahRootRestSatisfaction = true ∧
  r.cleanMythicPatriarchListAbsent = true

structure TownAndMigrationNames where
  cainanKanNanTown : Bool := true
  fishCanalMeaningGiven : Bool := true
  kanunaiCanaanitesNamed : Bool := true
  tribesCarryGeographicalNames : Bool := true
  postFloodNamesAsSyrianTowns : Bool := true
  reuRaguSerugHarranNamed : Bool := true
deriving DecidableEq, Repr

def townAndMigrationNames : TownAndMigrationNames := {}

def townsCarryPatriarchNames (t : TownAndMigrationNames) : Prop :=
  t.cainanKanNanTown = true ∧
  t.fishCanalMeaningGiven = true ∧
  t.kanunaiCanaanitesNamed = true ∧
  t.tribesCarryGeographicalNames = true ∧
  t.postFloodNamesAsSyrianTowns = true ∧
  t.reuRaguSerugHarranNamed = true

structure CraftAndDivineNameBridge where
  lamechPhoenicianDiamich : Bool := true
  lamechDumuguLamgaMoonForms : Bool := true
  tubalCainMetalworkerRole : Bool := true
  vulcanComparisonNamed : Bool := true
  bilKanFireMetalDeity : Bool := true
  nameAndCharacterCorrespond : Bool := true
deriving DecidableEq, Repr

def craftAndDivineNameBridge : CraftAndDivineNameBridge := {}

def craftNamesBridgeTraditions (c : CraftAndDivineNameBridge) : Prop :=
  c.lamechPhoenicianDiamich = true ∧
  c.lamechDumuguLamgaMoonForms = true ∧
  c.tubalCainMetalworkerRole = true ∧
  c.vulcanComparisonNamed = true ∧
  c.bilKanFireMetalDeity = true ∧
  c.nameAndCharacterCorrespond = true

structure DocumentaryNameEvidence where
  abramInEsarhaddonAssyria : Bool := true
  hebrewNamesInAssyria : Bool := true
  elohimJehovahCompoundNames : Bool := true
  urOfChaldeesAsBabylonianUr : Bool := true
  noNorthernUrEvidence : Bool := true
  ishmaelInHammurabiEraLarsaDocument : Bool := true
  hittiteAndArabianNamesInSamePeriod : Bool := true
deriving DecidableEq, Repr

def documentaryNameEvidence : DocumentaryNameEvidence := {}

def documentsPreserveGenesisNames (d : DocumentaryNameEvidence) : Prop :=
  d.abramInEsarhaddonAssyria = true ∧
  d.hebrewNamesInAssyria = true ∧
  d.elohimJehovahCompoundNames = true ∧
  d.urOfChaldeesAsBabylonianUr = true ∧
  d.noNorthernUrEvidence = true ∧
  d.ishmaelInHammurabiEraLarsaDocument = true ∧
  d.hittiteAndArabianNamesInSamePeriod = true

theorem genesis_roots_preserve_name_traces :
    rootsPreserveNameTraces rootNameCorrespondence := by
  unfold rootsPreserveNameTraces rootNameCorrespondence
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem genesis_towns_carry_patriarch_names :
    townsCarryPatriarchNames townAndMigrationNames := by
  unfold townsCarryPatriarchNames townAndMigrationNames
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem genesis_craft_names_bridge_traditions :
    craftNamesBridgeTraditions craftAndDivineNameBridge := by
  unfold craftNamesBridgeTraditions craftAndDivineNameBridge
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem genesis_documents_preserve_names :
    documentsPreserveGenesisNames documentaryNameEvidence := by
  unfold documentsPreserveGenesisNames documentaryNameEvidence
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem genesis_inherits_syrian_mediator_route :
    SyrianMediatorTraditionNetworkWitness.euphratesCarrierRoute
      SyrianMediatorTraditionNetworkWitness.euphratesTraditionRoute ∧
    townsCarryPatriarchNames townAndMigrationNames := by
  exact ⟨SyrianMediatorTraditionNetworkWitness.syrian_euphrates_carrier_route,
    genesis_towns_carry_patriarch_names⟩

theorem genesis_name_migration_witness :
    rootsPreserveNameTraces rootNameCorrespondence ∧
    townsCarryPatriarchNames townAndMigrationNames ∧
    craftNamesBridgeTraditions craftAndDivineNameBridge ∧
    documentsPreserveGenesisNames documentaryNameEvidence := by
  exact ⟨genesis_roots_preserve_name_traces,
    genesis_towns_carry_patriarch_names,
    genesis_craft_names_bridge_traditions,
    genesis_documents_preserve_names⟩

end GenesisNameMigrationWitness
end Gnosis.Witnesses.Chaldean
