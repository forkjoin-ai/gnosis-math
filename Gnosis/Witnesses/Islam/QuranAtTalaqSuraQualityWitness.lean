import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAtTalaqSuraQualityWitness

/-!
# Quran 65, At-Talaq / Divorce -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14725-14760`.

This complete sura witness covers Quran 65:1-12.

At-Talaq is the boundary-and-provision witness. Divorce is placed inside waiting
periods, housing duties, witnesses, fair release, pregnancy and nursing care,
capacity-bounded spending, God-consciousness as the way out, and the repeated
town-cycle warning that commands can be refused only at ruinous cost.

No `sorry`, no new `axiom`.
-/

inductive TalaqQualityCluster
  | waitingPeriodsHousingAndWitnesses
  | fairReleaseAndPregnancyNursingCare
  | capacityBoundSpendingAndEaseAfterHardship
  | townCycleWarningAndSevereAccount
  | sevenHeavensCommandAndKnowledge
deriving DecidableEq, Repr

def talaqQualityClusters : List TalaqQualityCluster :=
  [ .waitingPeriodsHousingAndWitnesses, .fairReleaseAndPregnancyNursingCare,
    .capacityBoundSpendingAndEaseAfterHardship, .townCycleWarningAndSevereAccount,
    .sevenHeavensCommandAndKnowledge ]

structure TalaqInvariantLedger where
  householdSeparationHasBoundedProcedure : Bool := true
  careContinuesThroughVulnerability : Bool := true
  spendingIsBoundedByCapacity : Bool := true
  godAwarenessOpensProvisionAndEase : Bool := true
  commandRunsThroughCreatedOrder : Bool := true
deriving DecidableEq, Repr

def talaqInvariantLedger : TalaqInvariantLedger := {}

def talaqSat (l : TalaqInvariantLedger) : Prop :=
  l.householdSeparationHasBoundedProcedure = true ∧ l.careContinuesThroughVulnerability = true ∧
  l.spendingIsBoundedByCapacity = true ∧ l.godAwarenessOpensProvisionAndEase = true ∧
  l.commandRunsThroughCreatedOrder = true

structure TalaqGapLedger where
  expulsionDuringWaitingPeriodBreaksBounds : Bool := true
  harmCanBeUsedToConstrainWomen : Bool := true
  refusalOfCommandRuinsTowns : Bool := true
  provisionAnxietyCanOverruleTrust : Bool := true
  legalProcedureWithoutGodAwarenessFails : Bool := true
deriving DecidableEq, Repr

def talaqGapLedger : TalaqGapLedger := {}

def talaqGapsExposeBoundary (g : TalaqGapLedger) : Prop :=
  g.expulsionDuringWaitingPeriodBreaksBounds = true ∧ g.harmCanBeUsedToConstrainWomen = true ∧
  g.refusalOfCommandRuinsTowns = true ∧ g.provisionAnxietyCanOverruleTrust = true ∧
  g.legalProcedureWithoutGodAwarenessFails = true

def talaqSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 65 / At-Talaq witnesses bounded household separation, care, and provision trust"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive TalaqRegister | waiting | housing | care | spending | warning | command
deriving DecidableEq, Repr, Nonempty

inductive TalaqInvariant | boundedCareProvision
deriving DecidableEq, Repr

def talaqRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TalaqRegister => TalaqInvariant.boundedCareProvision)
      TalaqInvariant.boundedCareProvision :=
  TruthOneManyNamesWitness.constant_names_agree TalaqInvariant.boundedCareProvision

theorem talaq_quality_clusters_shape :
    talaqQualityClusters.length = 5 ∧ talaqQualityClusters.head? = some .waitingPeriodsHousingAndWitnesses ∧
    talaqQualityClusters.getLast? = some .sevenHeavensCommandAndKnowledge := by
  exact ⟨rfl, rfl, rfl⟩

theorem talaq_sat_witness : talaqSat talaqInvariantLedger := by
  unfold talaqSat talaqInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem talaq_gap_witness : talaqGapsExposeBoundary talaqGapLedger := by
  unfold talaqGapsExposeBoundary talaqGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem talaq_access_archaeological :
    talaqSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_at_talaq_sura_quality_witness :
    talaqQualityClusters.length = 5 ∧ talaqSat talaqInvariantLedger ∧
    talaqGapsExposeBoundary talaqGapLedger ∧
    talaqSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TalaqRegister => TalaqInvariant.boundedCareProvision)
      TalaqInvariant.boundedCareProvision := by
  exact ⟨talaq_quality_clusters_shape.left, talaq_sat_witness, talaq_gap_witness,
    talaq_access_archaeological, talaqRegistersAgree⟩

end QuranAtTalaqSuraQualityWitness
end Gnosis.Witnesses.Islam
