import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlHashrSuraQualityWitness

/-!
# Quran 59, Al-Hashr / The Gathering [of Forces] -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14345-14421`.

This complete sura witness covers Quran 59:1-24.

Al-Hashr is the exile-distribution-and-name-litany witness. God drives out the
People of the Book from their strongholds, their own hands help demolish homes,
spoils are distributed so wealth does not circulate only among the rich,
Emigrants and Helpers are praised for need-sharing, hypocrite promises collapse,
Satan's abandonment models false alliance, and the final Names concentrate the
source of sovereignty, peace, might, and creation.

No `sorry`, no new `axiom`.
-/

inductive HashrQualityCluster
  | glorificationExileStrongholdsAndHomeDemolition
  | spoilDistributionAndWealthCirculationBoundary
  | emigrantsHelpersAndNeedSharing
  | hypocritePromiseSatanAbandonmentAndFear
  | quranMountainParableAndDivineNames
deriving DecidableEq, Repr

def hashrQualityClusters : List HashrQualityCluster :=
  [ .glorificationExileStrongholdsAndHomeDemolition
  , .spoilDistributionAndWealthCirculationBoundary
  , .emigrantsHelpersAndNeedSharing
  , .hypocritePromiseSatanAbandonmentAndFear
  , .quranMountainParableAndDivineNames
  ]

structure HashrInvariantLedger where
  apparentFortressesDoNotBlockDivineJudgment : Bool := true
  wealthDistributionMustAvoidRichOnlyCirculation : Bool := true
  faithfulCommunityPrefersOthersDespiteNeed : Bool := true
  falseAllianceAbandonsAtCost : Bool := true
  divineNamesGatherSovereignSource : Bool := true
deriving DecidableEq, Repr

def hashrInvariantLedger : HashrInvariantLedger := {}

def hashrSat (l : HashrInvariantLedger) : Prop :=
  l.apparentFortressesDoNotBlockDivineJudgment = true ∧
  l.wealthDistributionMustAvoidRichOnlyCirculation = true ∧
  l.faithfulCommunityPrefersOthersDespiteNeed = true ∧
  l.falseAllianceAbandonsAtCost = true ∧
  l.divineNamesGatherSovereignSource = true

structure HashrGapLedger where
  strongholdsCreateFalseSecurity : Bool := true
  wealthCanPoolAmongTheRich : Bool := true
  hypocritesPromiseSupportTheyWillNotGive : Bool := true
  satanSaysDisbelieveThenDisowns : Bool := true
  forgettingGodProducesSelfForgetfulness : Bool := true
deriving DecidableEq, Repr

def hashrGapLedger : HashrGapLedger := {}

def hashrGapsExposeBoundary (g : HashrGapLedger) : Prop :=
  g.strongholdsCreateFalseSecurity = true ∧
  g.wealthCanPoolAmongTheRich = true ∧
  g.hypocritesPromiseSupportTheyWillNotGive = true ∧
  g.satanSaysDisbelieveThenDisowns = true ∧
  g.forgettingGodProducesSelfForgetfulness = true

def hashrSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 59 / Al-Hashr witnesses exile, just distribution, false alliance collapse, and Names"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive HashrRegister | exile | spoils | emigrants | helpers | alliance | names
deriving DecidableEq, Repr, Nonempty

inductive HashrInvariant | gatheredNamesJustDistribution
deriving DecidableEq, Repr

def hashrRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : HashrRegister => HashrInvariant.gatheredNamesJustDistribution)
      HashrInvariant.gatheredNamesJustDistribution :=
  TruthOneManyNamesWitness.constant_names_agree HashrInvariant.gatheredNamesJustDistribution

theorem hashr_quality_clusters_shape :
    hashrQualityClusters.length = 5 ∧
    hashrQualityClusters.head? = some .glorificationExileStrongholdsAndHomeDemolition ∧
    hashrQualityClusters.getLast? = some .quranMountainParableAndDivineNames := by
  exact ⟨rfl, rfl, rfl⟩

theorem hashr_sat_witness : hashrSat hashrInvariantLedger := by
  unfold hashrSat hashrInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hashr_gap_witness : hashrGapsExposeBoundary hashrGapLedger := by
  unfold hashrGapsExposeBoundary hashrGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hashr_access_archaeological :
    hashrSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_hashr_sura_quality_witness :
    hashrQualityClusters.length = 5 ∧
    hashrSat hashrInvariantLedger ∧
    hashrGapsExposeBoundary hashrGapLedger ∧
    hashrSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : HashrRegister => HashrInvariant.gatheredNamesJustDistribution)
      HashrInvariant.gatheredNamesJustDistribution := by
  exact ⟨hashr_quality_clusters_shape.left, hashr_sat_witness, hashr_gap_witness,
    hashr_access_archaeological, hashrRegistersAgree⟩

end QuranAlHashrSuraQualityWitness
end Gnosis.Witnesses.Islam
