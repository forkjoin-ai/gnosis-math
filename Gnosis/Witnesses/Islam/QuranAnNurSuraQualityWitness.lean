import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAnNurSuraQualityWitness

/-!
# Quran 24, An-Nur / Light -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:9276-9526`.

This complete sura witness covers Quran 24:1-64.

An-Nur is the communal-light witness. Clear obligations regulate accusation,
witnessing, repentance, privacy, modesty, marriage, emancipation, the Verse of
Light, houses of remembrance, obedience to judgment, succession after fear, and
household permission. The counterproof is slander without four witnesses,
indecency-spreading, Satanic footsteps, forced prostitution, mirage deeds,
deep-sea darkness, false obedience, and stealthy departure from the Messenger.

No `sorry`, no new `axiom`.
-/

inductive AnNurQualityCluster
  | obligatorySuraAccusationAndRepentance
  | slanderTonguesForgivenessAndPurity
  | privacyModestyMarriageAndEmancipation
  | verseOfLightHousesAndDarknessCounterproofs
  | creationSignsJudgmentObedienceAndSuccession
  | householdPermissionCommunalDisciplineAndReturn
deriving DecidableEq, Repr

def anNurQualityClusters : List AnNurQualityCluster :=
  [ AnNurQualityCluster.obligatorySuraAccusationAndRepentance
  , AnNurQualityCluster.slanderTonguesForgivenessAndPurity
  , AnNurQualityCluster.privacyModestyMarriageAndEmancipation
  , AnNurQualityCluster.verseOfLightHousesAndDarknessCounterproofs
  , AnNurQualityCluster.creationSignsJudgmentObedienceAndSuccession
  , AnNurQualityCluster.householdPermissionCommunalDisciplineAndReturn
  ]

structure AnNurInvariantLedger where
  clearRevelationOrdersCommunity : Bool := true
  witnessRulesProtectHonor : Bool := true
  forgivenessAndPurityInterruptSlander : Bool := true
  privacyAndModestyAreLightDiscipline : Bool := true
  godGuidesToLightUponLight : Bool := true
  trueObedienceAnswersJudgmentSummons : Bool := true
  allReturnUnderFullKnowledge : Bool := true
deriving DecidableEq, Repr

def anNurInvariantLedger : AnNurInvariantLedger := {}

def anNurSat (l : AnNurInvariantLedger) : Prop :=
  l.clearRevelationOrdersCommunity = true ∧
  l.witnessRulesProtectHonor = true ∧
  l.forgivenessAndPurityInterruptSlander = true ∧
  l.privacyAndModestyAreLightDiscipline = true ∧
  l.godGuidesToLightUponLight = true ∧
  l.trueObedienceAnswersJudgmentSummons = true ∧
  l.allReturnUnderFullKnowledge = true

structure AnNurGapLedger where
  accusationWithoutWitnesses : Bool := true
  tonguesRepeatUnknownSlander : Bool := true
  indecencySpreadDesired : Bool := true
  satanFootstepsFollowed : Bool := true
  forcedProstitutionForWorldGain : Bool := true
  disbelieverDeedsAsMirage : Bool := true
  layeredDarknessWithoutLight : Bool := true
  stealthDepartureFromSummons : Bool := true
deriving DecidableEq, Repr

def anNurGapLedger : AnNurGapLedger := {}

def anNurGapsExposeBoundary (g : AnNurGapLedger) : Prop :=
  g.accusationWithoutWitnesses = true ∧
  g.tonguesRepeatUnknownSlander = true ∧
  g.indecencySpreadDesired = true ∧
  g.satanFootstepsFollowed = true ∧
  g.forcedProstitutionForWorldGain = true ∧
  g.disbelieverDeedsAsMirage = true ∧
  g.layeredDarknessWithoutLight = true ∧
  g.stealthDepartureFromSummons = true

def anNurSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 24 / An-Nur witnesses communal light through witness, privacy, purity, and obedience"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive AnNurRegister | witness | slander | privacy | light | obedience | permission | return
deriving DecidableEq, Repr, Nonempty

inductive AnNurInvariant | communalLightDiscipline
deriving DecidableEq, Repr

def anNurRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AnNurRegister => AnNurInvariant.communalLightDiscipline)
      AnNurInvariant.communalLightDiscipline :=
  TruthOneManyNamesWitness.constant_names_agree AnNurInvariant.communalLightDiscipline

theorem an_nur_quality_clusters_shape :
    anNurQualityClusters.length = 6
    ∧ anNurQualityClusters.head? = some AnNurQualityCluster.obligatorySuraAccusationAndRepentance
    ∧ anNurQualityClusters.getLast? =
      some AnNurQualityCluster.householdPermissionCommunalDisciplineAndReturn := by
  exact ⟨rfl, rfl, rfl⟩

theorem an_nur_sat_witness : anNurSat anNurInvariantLedger := by
  unfold anNurSat anNurInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem an_nur_gap_witness : anNurGapsExposeBoundary anNurGapLedger := by
  unfold anNurGapsExposeBoundary anNurGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem an_nur_access_archaeological :
    anNurSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_an_nur_sura_quality_witness :
    anNurQualityClusters.length = 6 ∧
    anNurSat anNurInvariantLedger ∧
    anNurGapsExposeBoundary anNurGapLedger ∧
    anNurSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AnNurRegister => AnNurInvariant.communalLightDiscipline)
      AnNurInvariant.communalLightDiscipline := by
  exact ⟨an_nur_quality_clusters_shape.left, an_nur_sat_witness, an_nur_gap_witness,
    an_nur_access_archaeological, anNurRegistersAgree⟩

end QuranAnNurSuraQualityWitness
end Gnosis.Witnesses.Islam
