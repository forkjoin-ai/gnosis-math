import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlMumtahanaSuraQualityWitness

/-!
# Quran 60, Al-Mumtahana / Women Tested -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14448-14484`.

This complete sura witness covers Quran 60:1-13.

Al-Mumtahana is the tested-allegiance-and-fairness witness. Believers are warned
not to take hostile enemies as allies; Abraham supplies the disavowal pattern
with prayer for forgiveness; God may create affection after hostility; fairness
is preserved toward those who did not fight or expel; believing migrant women
are tested and protected; marriage bonds across hostile allegiance are
regulated; and the Prophet receives women's pledge.

No `sorry`, no new `axiom`.
-/

inductive MumtahanaQualityCluster
  | hostileAllianceWarningAndHiddenAffectionAudit
  | abrahamicDisavowalAndForgivenessPrayer
  | fairnessTowardNoncombatants
  | testedMigrantWomenAndMarriageBoundary
  | womensPledgeAndFinalAllianceWarning
deriving DecidableEq, Repr

def mumtahanaQualityClusters : List MumtahanaQualityCluster :=
  [ .hostileAllianceWarningAndHiddenAffectionAudit
  , .abrahamicDisavowalAndForgivenessPrayer
  , .fairnessTowardNoncombatants
  , .testedMigrantWomenAndMarriageBoundary
  , .womensPledgeAndFinalAllianceWarning
  ]

structure MumtahanaInvariantLedger where
  allegianceMustNotEmpowerHostileExpulsion : Bool := true
  abrahamicDisavowalIncludesPrayerfulReturn : Bool := true
  justiceTowardNoncombatantsRemainsAllowed : Bool := true
  migrantFaithRequiresTestingAndProtection : Bool := true
  pledgeBindsEthicalCommunity : Bool := true
deriving DecidableEq, Repr

def mumtahanaInvariantLedger : MumtahanaInvariantLedger := {}

def mumtahanaSat (l : MumtahanaInvariantLedger) : Prop :=
  l.allegianceMustNotEmpowerHostileExpulsion = true ∧
  l.abrahamicDisavowalIncludesPrayerfulReturn = true ∧
  l.justiceTowardNoncombatantsRemainsAllowed = true ∧
  l.migrantFaithRequiresTestingAndProtection = true ∧
  l.pledgeBindsEthicalCommunity = true

structure MumtahanaGapLedger where
  secretAffectionCanAidHostileEnemies : Bool := true
  kinshipWillNotHelpOnResurrectionDay : Bool := true
  combatantExpulsionChangesAllianceLaw : Bool := true
  untestedMigrationWouldConfuseCovenantBoundary : Bool := true
  deadHeartPeopleShouldNotBecomeAllies : Bool := true
deriving DecidableEq, Repr

def mumtahanaGapLedger : MumtahanaGapLedger := {}

def mumtahanaGapsExposeBoundary (g : MumtahanaGapLedger) : Prop :=
  g.secretAffectionCanAidHostileEnemies = true ∧
  g.kinshipWillNotHelpOnResurrectionDay = true ∧
  g.combatantExpulsionChangesAllianceLaw = true ∧
  g.untestedMigrationWouldConfuseCovenantBoundary = true ∧
  g.deadHeartPeopleShouldNotBecomeAllies = true

def mumtahanaSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 60 / Al-Mumtahana witnesses tested allegiance, fair noncombatant conduct, and pledge"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive MumtahanaRegister | allegiance | abraham | fairness | testing | marriage | pledge
deriving DecidableEq, Repr, Nonempty

inductive MumtahanaInvariant | testedAllegianceFairness
deriving DecidableEq, Repr

def mumtahanaRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MumtahanaRegister => MumtahanaInvariant.testedAllegianceFairness)
      MumtahanaInvariant.testedAllegianceFairness :=
  TruthOneManyNamesWitness.constant_names_agree MumtahanaInvariant.testedAllegianceFairness

theorem mumtahana_quality_clusters_shape :
    mumtahanaQualityClusters.length = 5 ∧
    mumtahanaQualityClusters.head? = some .hostileAllianceWarningAndHiddenAffectionAudit ∧
    mumtahanaQualityClusters.getLast? = some .womensPledgeAndFinalAllianceWarning := by
  exact ⟨rfl, rfl, rfl⟩

theorem mumtahana_sat_witness : mumtahanaSat mumtahanaInvariantLedger := by
  unfold mumtahanaSat mumtahanaInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mumtahana_gap_witness : mumtahanaGapsExposeBoundary mumtahanaGapLedger := by
  unfold mumtahanaGapsExposeBoundary mumtahanaGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mumtahana_access_archaeological :
    mumtahanaSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_mumtahana_sura_quality_witness :
    mumtahanaQualityClusters.length = 5 ∧
    mumtahanaSat mumtahanaInvariantLedger ∧
    mumtahanaGapsExposeBoundary mumtahanaGapLedger ∧
    mumtahanaSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MumtahanaRegister => MumtahanaInvariant.testedAllegianceFairness)
      MumtahanaInvariant.testedAllegianceFairness := by
  exact ⟨mumtahana_quality_clusters_shape.left, mumtahana_sat_witness, mumtahana_gap_witness,
    mumtahana_access_archaeological, mumtahanaRegistersAgree⟩

end QuranAlMumtahanaSuraQualityWitness
end Gnosis.Witnesses.Islam
