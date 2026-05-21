import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlFathSuraQualityWitness

/-!
# Quran 48, Al-Fath / Triumph -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:13332-13448`.

This complete sura witness covers Quran 48:1-29.

Al-Fath is the pledge-and-tranquility witness: clear triumph, forgiven burden,
tranquility sent into believers' hearts, hypocrite suspicion exposed, allegiance
under the tree, excuses of those left behind, restraint at Mecca, protected
unknown believers, the true dream, and Muhammad's companions as firm against
denial and merciful among themselves.

No `sorry`, no new `axiom`.
-/

inductive FathQualityCluster
  | clearTriumphForgivenessAndTranquility
  | hypocriteSuspicionAndDivineOwnership
  | treePledgeAndLeftBehindExcuses
  | meccaRestraintUnknownBelieversAndTrueDream
  | messengerCompanionsAndGrowingSeedImage
deriving DecidableEq, Repr

def fathQualityClusters : List FathQualityCluster :=
  [ .clearTriumphForgivenessAndTranquility
  , .hypocriteSuspicionAndDivineOwnership
  , .treePledgeAndLeftBehindExcuses
  , .meccaRestraintUnknownBelieversAndTrueDream
  , .messengerCompanionsAndGrowingSeedImage
  ]

structure FathInvariantLedger where
  triumphCanArriveAsCovenantTranquility : Bool := true
  allegianceToMessengerBindsToGod : Bool := true
  restraintCanProtectHiddenBelievers : Bool := true
  trueVisionBecomesOpenedAccess : Bool := true
  communityStrengthIncludesInternalMercy : Bool := true
deriving DecidableEq, Repr

def fathInvariantLedger : FathInvariantLedger := {}

def fathSat (l : FathInvariantLedger) : Prop :=
  l.triumphCanArriveAsCovenantTranquility = true ∧
  l.allegianceToMessengerBindsToGod = true ∧
  l.restraintCanProtectHiddenBelievers = true ∧
  l.trueVisionBecomesOpenedAccess = true ∧
  l.communityStrengthIncludesInternalMercy = true

structure FathGapLedger where
  hypocriteSuspicionProjectsBadOutcome : Bool := true
  leftBehindExcusesMaskAttachment : Bool := true
  pledgeBreakingHarmsOnlyTheBreaker : Bool := true
  fightingZealCanMissHiddenBelievers : Bool := true
  arrogantIgnoranceBlocksSacredAccess : Bool := true
deriving DecidableEq, Repr

def fathGapLedger : FathGapLedger := {}

def fathGapsExposeBoundary (g : FathGapLedger) : Prop :=
  g.hypocriteSuspicionProjectsBadOutcome = true ∧
  g.leftBehindExcusesMaskAttachment = true ∧
  g.pledgeBreakingHarmsOnlyTheBreaker = true ∧
  g.fightingZealCanMissHiddenBelievers = true ∧
  g.arrogantIgnoranceBlocksSacredAccess = true

def fathSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 48 / Al-Fath witnesses triumph as tranquil pledge, restraint, and opened access"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive FathRegister | triumph | tranquility | pledge | restraint | vision | community
deriving DecidableEq, Repr, Nonempty

inductive FathInvariant | tranquilPledgeTriumph
deriving DecidableEq, Repr

def fathRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : FathRegister => FathInvariant.tranquilPledgeTriumph)
      FathInvariant.tranquilPledgeTriumph :=
  TruthOneManyNamesWitness.constant_names_agree FathInvariant.tranquilPledgeTriumph

theorem fath_quality_clusters_shape :
    fathQualityClusters.length = 5 ∧
    fathQualityClusters.head? = some .clearTriumphForgivenessAndTranquility ∧
    fathQualityClusters.getLast? = some .messengerCompanionsAndGrowingSeedImage := by
  exact ⟨rfl, rfl, rfl⟩

theorem fath_sat_witness : fathSat fathInvariantLedger := by
  unfold fathSat fathInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem fath_gap_witness : fathGapsExposeBoundary fathGapLedger := by
  unfold fathGapsExposeBoundary fathGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem fath_access_archaeological :
    fathSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_fath_sura_quality_witness :
    fathQualityClusters.length = 5 ∧
    fathSat fathInvariantLedger ∧
    fathGapsExposeBoundary fathGapLedger ∧
    fathSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : FathRegister => FathInvariant.tranquilPledgeTriumph)
      FathInvariant.tranquilPledgeTriumph := by
  exact ⟨fath_quality_clusters_shape.left, fath_sat_witness, fath_gap_witness,
    fath_access_archaeological, fathRegistersAgree⟩

end QuranAlFathSuraQualityWitness
end Gnosis.Witnesses.Islam
