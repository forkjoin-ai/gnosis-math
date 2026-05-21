import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlMulkSuraQualityWitness

/-!
# Quran 67, Al-Mulk / Control -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14843-14880`.

This complete sura witness covers Quran 67:1-30.

Al-Mulk is the sovereign-control-and-observation witness. Control belongs to the
One who created death and life as a test, seven heavens show no flaw, stars repel
devils, Hell interrogates rejecters, birds held in flight expose sustaining
mercy, and water withdrawal makes dependence impossible to deny.

No `sorry`, no new `axiom`.
-/

inductive MulkQualityCluster
  | sovereignControlDeathLifeAndTest
  | sevenHeavensNoFlawAndStarGuard
  | hellQuestionAndConfessedRejection
  | birdsProvisionAndSustainingMercy
  | faceDownWalkingWaterWithdrawalAndDependence
deriving DecidableEq, Repr

def mulkQualityClusters : List MulkQualityCluster :=
  [ .sovereignControlDeathLifeAndTest, .sevenHeavensNoFlawAndStarGuard,
    .hellQuestionAndConfessedRejection, .birdsProvisionAndSustainingMercy,
    .faceDownWalkingWaterWithdrawalAndDependence ]

structure MulkInvariantLedger where
  deathAndLifeAreTestingOrder : Bool := true
  creationWithstandsRepeatedInspection : Bool := true
  warningRejectedIsConfessedAtFire : Bool := true
  mercySustainsFlightAndProvision : Bool := true
  waterDependenceRevealsSovereignControl : Bool := true
deriving DecidableEq, Repr

def mulkInvariantLedger : MulkInvariantLedger := {}

def mulkSat (l : MulkInvariantLedger) : Prop :=
  l.deathAndLifeAreTestingOrder = true ∧ l.creationWithstandsRepeatedInspection = true ∧
  l.warningRejectedIsConfessedAtFire = true ∧ l.mercySustainsFlightAndProvision = true ∧
  l.waterDependenceRevealsSovereignControl = true

structure MulkGapLedger where
  warningCanBeDeniedAsDelusion : Bool := true
  hearingAndReasonCanBeUnused : Bool := true
  armiesCannotProtectAgainstMercyWithdrawal : Bool := true
  provisionCanBeMisreadAsOwned : Bool := true
  faceDownWalkingMisreadsStraightPath : Bool := true
deriving DecidableEq, Repr

def mulkGapLedger : MulkGapLedger := {}

def mulkGapsExposeBoundary (g : MulkGapLedger) : Prop :=
  g.warningCanBeDeniedAsDelusion = true ∧ g.hearingAndReasonCanBeUnused = true ∧
  g.armiesCannotProtectAgainstMercyWithdrawal = true ∧ g.provisionCanBeMisreadAsOwned = true ∧
  g.faceDownWalkingMisreadsStraightPath = true

def mulkSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 67 / Al-Mulk witnesses sovereign control, tested life, inspection, and dependence"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive MulkRegister | control | test | heavens | warning | birds | water
deriving DecidableEq, Repr, Nonempty

inductive MulkInvariant | sovereignTestedDependence
deriving DecidableEq, Repr

def mulkRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MulkRegister => MulkInvariant.sovereignTestedDependence)
      MulkInvariant.sovereignTestedDependence :=
  TruthOneManyNamesWitness.constant_names_agree MulkInvariant.sovereignTestedDependence

theorem mulk_quality_clusters_shape :
    mulkQualityClusters.length = 5 ∧ mulkQualityClusters.head? = some .sovereignControlDeathLifeAndTest ∧
    mulkQualityClusters.getLast? = some .faceDownWalkingWaterWithdrawalAndDependence := by
  exact ⟨rfl, rfl, rfl⟩

theorem mulk_sat_witness : mulkSat mulkInvariantLedger := by
  unfold mulkSat mulkInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mulk_gap_witness : mulkGapsExposeBoundary mulkGapLedger := by
  unfold mulkGapsExposeBoundary mulkGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mulk_access_archaeological :
    mulkSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_mulk_sura_quality_witness :
    mulkQualityClusters.length = 5 ∧ mulkSat mulkInvariantLedger ∧
    mulkGapsExposeBoundary mulkGapLedger ∧
    mulkSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MulkRegister => MulkInvariant.sovereignTestedDependence)
      MulkInvariant.sovereignTestedDependence := by
  exact ⟨mulk_quality_clusters_shape.left, mulk_sat_witness, mulk_gap_witness,
    mulk_access_archaeological, mulkRegistersAgree⟩

end QuranAlMulkSuraQualityWitness
end Gnosis.Witnesses.Islam
