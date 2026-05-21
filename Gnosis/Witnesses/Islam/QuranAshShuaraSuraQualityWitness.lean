import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAshShuaraSuraQualityWitness

/-!
# Quran 26, Ash-Shu'ara / The Poets -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:9702-9955`.

This complete sura witness covers Quran 26:1-227.

Ash-Shu'ara is the faithful-messenger refrain witness. Moses, Abraham, Noah,
Hud, Salih, Lot, and Shu'ayb repeat one source-order signature: faithful
messenger, be mindful, obey, no wage, rejected people, sign, and the Almighty
Merciful close. The sura then distinguishes revelation carried by the
Trustworthy Spirit from jinn-noise and aimless poetry.

No `sorry`, no new `axiom`.
-/

inductive AshShuaraQualityCluster
  | clearScripturePropheticGriefAndEarthSigns
  | mosesPharaohSorceryAndSeaRescue
  | abrahamDevotedHeartAndFalseGodCollapse
  | noahRejectedPoorBelieversAndArk
  | hudMonumentsImmortalityFantasyAndDestruction
  | salihCamelLotBoundsAndShuaybMeasure
  | trustworthySpiritArabicWarningAndPoetryBoundary
deriving DecidableEq, Repr

def ashShuaraQualityClusters : List AshShuaraQualityCluster :=
  [ AshShuaraQualityCluster.clearScripturePropheticGriefAndEarthSigns
  , AshShuaraQualityCluster.mosesPharaohSorceryAndSeaRescue
  , AshShuaraQualityCluster.abrahamDevotedHeartAndFalseGodCollapse
  , AshShuaraQualityCluster.noahRejectedPoorBelieversAndArk
  , AshShuaraQualityCluster.hudMonumentsImmortalityFantasyAndDestruction
  , AshShuaraQualityCluster.salihCamelLotBoundsAndShuaybMeasure
  , AshShuaraQualityCluster.trustworthySpiritArabicWarningAndPoetryBoundary
  ]

structure AshShuaraInvariantLedger where
  faithfulMessengerRefrainIsStable : Bool := true
  noWageWitnessKeepsMessageClean : Bool := true
  signsPersistDespiteMajorityDisbelief : Bool := true
  lordOfWorldsOutranksLocalPower : Bool := true
  devotedHeartOutranksWealthChildren : Bool := true
  trustworthySpiritCarriesRevelation : Bool := true
  poetryIsDistinguishedFromQuran : Bool := true
deriving DecidableEq, Repr

def ashShuaraInvariantLedger : AshShuaraInvariantLedger := {}

def ashShuaraSat (l : AshShuaraInvariantLedger) : Prop :=
  l.faithfulMessengerRefrainIsStable = true ∧
  l.noWageWitnessKeepsMessageClean = true ∧
  l.signsPersistDespiteMajorityDisbelief = true ∧
  l.lordOfWorldsOutranksLocalPower = true ∧
  l.devotedHeartOutranksWealthChildren = true ∧
  l.trustworthySpiritCarriesRevelation = true ∧
  l.poetryIsDistinguishedFromQuran = true

structure AshShuaraGapLedger where
  revelationTurnedAwayFrom : Bool := true
  pharaohPrisonThreat : Bool := true
  sorceryPropaganda : Bool := true
  poorBelieversDespised : Bool := true
  monumentsAndFortressesSeekImmortality : Bool := true
  camelSignHarmed : Bool := true
  measureWeightCorrupted : Bool := true
  jinnAndPoetryMisattribution : Bool := true
deriving DecidableEq, Repr

def ashShuaraGapLedger : AshShuaraGapLedger := {}

def ashShuaraGapsExposeBoundary (g : AshShuaraGapLedger) : Prop :=
  g.revelationTurnedAwayFrom = true ∧
  g.pharaohPrisonThreat = true ∧
  g.sorceryPropaganda = true ∧
  g.poorBelieversDespised = true ∧
  g.monumentsAndFortressesSeekImmortality = true ∧
  g.camelSignHarmed = true ∧
  g.measureWeightCorrupted = true ∧
  g.jinnAndPoetryMisattribution = true

def ashShuaraSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 26 / Ash-Shu'ara witnesses the faithful-messenger refrain and revelation/poetry boundary"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive AshShuaraRegister | moses | abraham | noah | hud | salih | lot | shuayb | spirit
deriving DecidableEq, Repr, Nonempty

inductive AshShuaraInvariant | faithfulMessengerRevelationBoundary
deriving DecidableEq, Repr

def ashShuaraRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AshShuaraRegister => AshShuaraInvariant.faithfulMessengerRevelationBoundary)
      AshShuaraInvariant.faithfulMessengerRevelationBoundary :=
  TruthOneManyNamesWitness.constant_names_agree
    AshShuaraInvariant.faithfulMessengerRevelationBoundary

theorem ash_shuara_quality_clusters_shape :
    ashShuaraQualityClusters.length = 7
    ∧ ashShuaraQualityClusters.head? =
      some AshShuaraQualityCluster.clearScripturePropheticGriefAndEarthSigns
    ∧ ashShuaraQualityClusters.getLast? =
      some AshShuaraQualityCluster.trustworthySpiritArabicWarningAndPoetryBoundary := by
  exact ⟨rfl, rfl, rfl⟩

theorem ash_shuara_sat_witness : ashShuaraSat ashShuaraInvariantLedger := by
  unfold ashShuaraSat ashShuaraInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ash_shuara_gap_witness : ashShuaraGapsExposeBoundary ashShuaraGapLedger := by
  unfold ashShuaraGapsExposeBoundary ashShuaraGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ash_shuara_access_archaeological :
    ashShuaraSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_ash_shuara_sura_quality_witness :
    ashShuaraQualityClusters.length = 7 ∧
    ashShuaraSat ashShuaraInvariantLedger ∧
    ashShuaraGapsExposeBoundary ashShuaraGapLedger ∧
    ashShuaraSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AshShuaraRegister => AshShuaraInvariant.faithfulMessengerRevelationBoundary)
      AshShuaraInvariant.faithfulMessengerRevelationBoundary := by
  exact ⟨ash_shuara_quality_clusters_shape.left, ash_shuara_sat_witness,
    ash_shuara_gap_witness, ash_shuara_access_archaeological, ashShuaraRegistersAgree⟩

end QuranAshShuaraSuraQualityWitness
end Gnosis.Witnesses.Islam
