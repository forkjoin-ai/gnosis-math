import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlQasasSuraQualityWitness

/-!
# Quran 28, Al-Qasas / The Story -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:10168-10428`.

This complete sura witness covers Quran 28:1-88.

Al-Qasas is the oppressed-remnant and anti-arrogance witness. Moses' mother,
river return, Midian, Tuwa signs, Pharaoh's tower, unseen revelation to
Muhammad, double reward for earlier Scripture people, sanctuary provision,
partner interrogation, night/day mercy, Qarun's swallowed wealth, and the final
"everything perishes except His Face" close all witness that God chooses,
guides, and returns judgment beyond worldly control.

No `sorry`, no new `axiom`.
-/

inductive AlQasasQualityCluster
  | oppressedFavoredMosesReturnedAndRaised
  | cityKillingRepentanceMidianAndCovenant
  | tuwaSignsAaronAndPharaohTower
  | unseenStoryGraceAndDesireVsGuidance
  | doubleRewardSanctuaryAndPartnerJudgment
  | nightDayMercyQarunAndPerishingExceptFace
deriving DecidableEq, Repr

def alQasasQualityClusters : List AlQasasQualityCluster :=
  [ AlQasasQualityCluster.oppressedFavoredMosesReturnedAndRaised
  , AlQasasQualityCluster.cityKillingRepentanceMidianAndCovenant
  , AlQasasQualityCluster.tuwaSignsAaronAndPharaohTower
  , AlQasasQualityCluster.unseenStoryGraceAndDesireVsGuidance
  , AlQasasQualityCluster.doubleRewardSanctuaryAndPartnerJudgment
  , AlQasasQualityCluster.nightDayMercyQarunAndPerishingExceptFace
  ]

structure AlQasasInvariantLedger where
  oppressedCanBecomeLeadersByDivineFavor : Bool := true
  promiseReturnsMosesToMother : Bool := true
  repentanceBreaksSupportForEvildoers : Bool := true
  prophetReceivesUnseenStoryByMercy : Bool := true
  godGuidesWhomHeWills : Bool := true
  worldlyPompFailsBeforeHereafter : Bool := true
  everythingPerishesExceptGodsFace : Bool := true
deriving DecidableEq, Repr

def alQasasInvariantLedger : AlQasasInvariantLedger := {}

def alQasasSat (l : AlQasasInvariantLedger) : Prop :=
  l.oppressedCanBecomeLeadersByDivineFavor = true ∧
  l.promiseReturnsMosesToMother = true ∧
  l.repentanceBreaksSupportForEvildoers = true ∧
  l.prophetReceivesUnseenStoryByMercy = true ∧
  l.godGuidesWhomHeWills = true ∧
  l.worldlyPompFailsBeforeHereafter = true ∧
  l.everythingPerishesExceptGodsFace = true

structure AlQasasGapLedger where
  pharaohDividesAndOppresses : Bool := true
  tyrannyMistakenForRepair : Bool := true
  conjuringChargeAgainstSigns : Bool := true
  pharaohTowerToMosesGod : Bool := true
  desireWithoutGuidance : Bool := true
  securityFearExcusesRejection : Bool := true
  partnerClaimsCannotAnswer : Bool := true
  qarunKnowledgeBoast : Bool := true
deriving DecidableEq, Repr

def alQasasGapLedger : AlQasasGapLedger := {}

def alQasasGapsExposeBoundary (g : AlQasasGapLedger) : Prop :=
  g.pharaohDividesAndOppresses = true ∧
  g.tyrannyMistakenForRepair = true ∧
  g.conjuringChargeAgainstSigns = true ∧
  g.pharaohTowerToMosesGod = true ∧
  g.desireWithoutGuidance = true ∧
  g.securityFearExcusesRejection = true ∧
  g.partnerClaimsCannotAnswer = true ∧
  g.qarunKnowledgeBoast = true

def alQasasSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 28 / Al-Qasas witnesses oppressed reversal, unseen story, and anti-arrogance return"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive AlQasasRegister | oppressed | mother | repentance | tuwa | unseen | sanctuary | qarun
deriving DecidableEq, Repr, Nonempty

inductive AlQasasInvariant | chosenGuidanceAgainstArrogance
deriving DecidableEq, Repr

def alQasasRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlQasasRegister => AlQasasInvariant.chosenGuidanceAgainstArrogance)
      AlQasasInvariant.chosenGuidanceAgainstArrogance :=
  TruthOneManyNamesWitness.constant_names_agree AlQasasInvariant.chosenGuidanceAgainstArrogance

theorem al_qasas_quality_clusters_shape :
    alQasasQualityClusters.length = 6
    ∧ alQasasQualityClusters.head? =
      some AlQasasQualityCluster.oppressedFavoredMosesReturnedAndRaised
    ∧ alQasasQualityClusters.getLast? =
      some AlQasasQualityCluster.nightDayMercyQarunAndPerishingExceptFace := by
  exact ⟨rfl, rfl, rfl⟩

theorem al_qasas_sat_witness : alQasasSat alQasasInvariantLedger := by
  unfold alQasasSat alQasasInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_qasas_gap_witness : alQasasGapsExposeBoundary alQasasGapLedger := by
  unfold alQasasGapsExposeBoundary alQasasGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_qasas_access_archaeological :
    alQasasSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_qasas_sura_quality_witness :
    alQasasQualityClusters.length = 6 ∧
    alQasasSat alQasasInvariantLedger ∧
    alQasasGapsExposeBoundary alQasasGapLedger ∧
    alQasasSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlQasasRegister => AlQasasInvariant.chosenGuidanceAgainstArrogance)
      AlQasasInvariant.chosenGuidanceAgainstArrogance := by
  exact ⟨al_qasas_quality_clusters_shape.left, al_qasas_sat_witness, al_qasas_gap_witness,
    al_qasas_access_archaeological, alQasasRegistersAgree⟩

end QuranAlQasasSuraQualityWitness
end Gnosis.Witnesses.Islam
