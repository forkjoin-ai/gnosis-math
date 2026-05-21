import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlAhqafSuraQualityWitness

/-!
# Quran 46, Al-Ahqaf / The Sand Dunes -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:13089-13208`.

This complete sura witness covers Quran 46:1-35.

Al-Ahqaf is the filial-warning-and-jinn-hearing witness: creation in truth,
powerless invoked partners, confirming Scripture, kindness to parents, the
thirty-month burden and mature repentance, the opposite child who dismisses
resurrection, Hud warning his people at the sand dunes, the destructive wind,
jinn listening to the Quran, and steadfastness like messengers of firm resolve.

No `sorry`, no new `axiom`.
-/

inductive AhqafQualityCluster
  | trueCreationAndPowerlessPartners
  | parentalBurdenMaturityAndRepentance
  | dismissiveChildAndDeedRecompense
  | hudSandDunesWarningAndDestroyingWind
  | jinnHearingAndFirmMessengerSteadfastness
deriving DecidableEq, Repr

def ahqafQualityClusters : List AhqafQualityCluster :=
  [ .trueCreationAndPowerlessPartners
  , .parentalBurdenMaturityAndRepentance
  , .dismissiveChildAndDeedRecompense
  , .hudSandDunesWarningAndDestroyingWind
  , .jinnHearingAndFirmMessengerSteadfastness
  ]

structure AhqafInvariantLedger where
  creationHasTruthAndTerm : Bool := true
  parentalGratitudeBelongsToRepentantMaturity : Bool := true
  deedsReceiveJustRank : Bool := true
  warningPersistsBeforeDestruction : Bool := true
  jinnHearingConfirmsQuranicGuidance : Bool := true
deriving DecidableEq, Repr

def ahqafInvariantLedger : AhqafInvariantLedger := {}

def ahqafSat (l : AhqafInvariantLedger) : Prop :=
  l.creationHasTruthAndTerm = true ∧
  l.parentalGratitudeBelongsToRepentantMaturity = true ∧
  l.deedsReceiveJustRank = true ∧
  l.warningPersistsBeforeDestruction = true ∧
  l.jinnHearingConfirmsQuranicGuidance = true

structure AhqafGapLedger where
  partnersCannotAnswerInvocation : Bool := true
  resurrectionIsDismissedAsAncientTales : Bool := true
  worldlyGoodCanBeUsedUpBeforeFire : Bool := true
  sandDuneWarningIsMockedAsHastenedPunishment : Bool := true
  noProtectorRemainsAgainstGod : Bool := true
deriving DecidableEq, Repr

def ahqafGapLedger : AhqafGapLedger := {}

def ahqafGapsExposeBoundary (g : AhqafGapLedger) : Prop :=
  g.partnersCannotAnswerInvocation = true ∧
  g.resurrectionIsDismissedAsAncientTales = true ∧
  g.worldlyGoodCanBeUsedUpBeforeFire = true ∧
  g.sandDuneWarningIsMockedAsHastenedPunishment = true ∧
  g.noProtectorRemainsAgainstGod = true

def ahqafSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 46 / Al-Ahqaf witnesses mature gratitude, sand-dune warning, and jinn hearing"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive AhqafRegister | creation | parents | child | hud | wind | jinn
deriving DecidableEq, Repr, Nonempty

inductive AhqafInvariant | matureWarningAndHearing
deriving DecidableEq, Repr

def ahqafRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AhqafRegister => AhqafInvariant.matureWarningAndHearing)
      AhqafInvariant.matureWarningAndHearing :=
  TruthOneManyNamesWitness.constant_names_agree AhqafInvariant.matureWarningAndHearing

theorem ahqaf_quality_clusters_shape :
    ahqafQualityClusters.length = 5 ∧
    ahqafQualityClusters.head? = some .trueCreationAndPowerlessPartners ∧
    ahqafQualityClusters.getLast? = some .jinnHearingAndFirmMessengerSteadfastness := by
  exact ⟨rfl, rfl, rfl⟩

theorem ahqaf_sat_witness : ahqafSat ahqafInvariantLedger := by
  unfold ahqafSat ahqafInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ahqaf_gap_witness : ahqafGapsExposeBoundary ahqafGapLedger := by
  unfold ahqafGapsExposeBoundary ahqafGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ahqaf_access_archaeological :
    ahqafSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_ahqaf_sura_quality_witness :
    ahqafQualityClusters.length = 5 ∧
    ahqafSat ahqafInvariantLedger ∧
    ahqafGapsExposeBoundary ahqafGapLedger ∧
    ahqafSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AhqafRegister => AhqafInvariant.matureWarningAndHearing)
      AhqafInvariant.matureWarningAndHearing := by
  exact ⟨ahqaf_quality_clusters_shape.left, ahqaf_sat_witness, ahqaf_gap_witness,
    ahqaf_access_archaeological, ahqafRegistersAgree⟩

end QuranAlAhqafSuraQualityWitness
end Gnosis.Witnesses.Islam
