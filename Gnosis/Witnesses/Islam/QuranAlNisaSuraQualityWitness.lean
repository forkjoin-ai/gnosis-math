import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness
import Gnosis.Witnesses.Islam.QuranAlNisaBetrayalSatanAbrahamWitness
import Gnosis.Witnesses.Islam.QuranAlNisaHouseholdTrustsAuthorityWitness
import Gnosis.Witnesses.Islam.QuranAlNisaHypocritesKillingMigrationPrayerWitness
import Gnosis.Witnesses.Islam.QuranAlNisaJudgmentBattleWitness
import Gnosis.Witnesses.Islam.QuranAlNisaKinshipInheritanceWitness
import Gnosis.Witnesses.Islam.QuranAlNisaMessengersJesusInheritanceWitness
import Gnosis.Witnesses.Islam.QuranAlNisaRepentanceMarriageWealthWitness
import Gnosis.Witnesses.Islam.QuranAlNisaWomenJusticeHypocritesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlNisaSuraQualityWitness

/-!
# Quran 4, An-Nisa -- Sura Quality Spine

This module finishes the An-Nisa repair pass at the sura level. The eight
existing `QuranAlNisa*Witness` modules remain the source-order ledger; this
spine adds the quality framework across the whole sura.

Sat/unseen reading:

An-Nisa is social order under audit. It starts from single-soul kinship, then
tests whether a community can preserve vulnerable persons, property, household
trust, truthful judgment, peace exceptions, migration, prayer, women, justice,
and messenger testimony without collapsing into appetite, betrayal, or faction.

The invariant is accountable relational order: kinship, wealth, authority,
judgment, and belief must remain witnessable. The negative ledger is equally
load-bearing: orphan-property consumption, forced inheritance, unlawful wealth,
household fracture, scripture distortion, tyrannical judgment, hypocrite
division, deliberate killing, betrayal advocacy, Satanic delusion, wavering
alliances, messenger distinction, and Jesus-claim distortion all expose where
social order fails to compile.

No `sorry`, no new `axiom`.
-/

inductive AlNisaQualityCluster
  | kinshipInheritanceBounds
  | repentanceMarriageWealth
  | householdTrustsAuthority
  | judgmentBattleAndReferral
  | hypocritesKillingMigrationPrayer
  | betrayalSatanAbraham
  | womenJusticeHypocrites
  | messengersJesusInheritanceClosure
deriving DecidableEq, Repr

def alNisaQualityClusters : List AlNisaQualityCluster :=
  [ AlNisaQualityCluster.kinshipInheritanceBounds
  , AlNisaQualityCluster.repentanceMarriageWealth
  , AlNisaQualityCluster.householdTrustsAuthority
  , AlNisaQualityCluster.judgmentBattleAndReferral
  , AlNisaQualityCluster.hypocritesKillingMigrationPrayer
  , AlNisaQualityCluster.betrayalSatanAbraham
  , AlNisaQualityCluster.womenJusticeHypocrites
  , AlNisaQualityCluster.messengersJesusInheritanceClosure
  ]

def alNisaImportedWitnessCount : Nat := 8

structure AlNisaInvariantLedger where
  singleSoulKinshipGroundsObligation : Bool := true
  vulnerablePropertyMustRemainWitnessable : Bool := true
  marriageAndWealthAreBoundedByConsent : Bool := true
  trustsReturnToJustJudgment : Bool := true
  authorityRequiresDisputeReferral : Bool := true
  migrationAndPrayerPreserveLifeUnderThreat : Bool := true
  justiceWitnessOverridesAlliance : Bool := true
  messengersCloseExcuseBoundary : Bool := true
deriving DecidableEq, Repr

def alNisaInvariantLedger : AlNisaInvariantLedger := {}

def alNisaSat (l : AlNisaInvariantLedger) : Prop :=
  l.singleSoulKinshipGroundsObligation = true ∧
  l.vulnerablePropertyMustRemainWitnessable = true ∧
  l.marriageAndWealthAreBoundedByConsent = true ∧
  l.trustsReturnToJustJudgment = true ∧
  l.authorityRequiresDisputeReferral = true ∧
  l.migrationAndPrayerPreserveLifeUnderThreat = true ∧
  l.justiceWitnessOverridesAlliance = true ∧
  l.messengersCloseExcuseBoundary = true

structure AlNisaGapLedger where
  orphanPropertyConsumption : Bool := true
  forcedInheritanceOfWomen : Bool := true
  unlawfulWealthAndSelfKilling : Bool := true
  householdFracture : Bool := true
  scriptureDistortion : Bool := true
  tyrannicalJudgment : Bool := true
  hypocriteDivision : Bool := true
  deliberateKilling : Bool := true
  betrayalAdvocacy : Bool := true
  satanicDelusion : Bool := true
  waveringAlliances : Bool := true
  messengerDistinction : Bool := true
  jesusClaimDistortion : Bool := true
deriving DecidableEq, Repr

def alNisaGapLedger : AlNisaGapLedger := {}

def alNisaGapsExposeBoundary (g : AlNisaGapLedger) : Prop :=
  g.orphanPropertyConsumption = true ∧
  g.forcedInheritanceOfWomen = true ∧
  g.unlawfulWealthAndSelfKilling = true ∧
  g.householdFracture = true ∧
  g.scriptureDistortion = true ∧
  g.tyrannicalJudgment = true ∧
  g.hypocriteDivision = true ∧
  g.deliberateKilling = true ∧
  g.betrayalAdvocacy = true ∧
  g.satanicDelusion = true ∧
  g.waveringAlliances = true ∧
  g.messengerDistinction = true ∧
  g.jesusClaimDistortion = true

def alNisaSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 4 / An-Nisa witnesses social order by audited relation and failure"
    positiveSamples := [1, 2, 3, 4, 5, 6, 7, 8]
    negativeSamples := [9, 10, 11, 12, 13, 14, 15, 16] }

inductive AlNisaRegister
  | kinship
  | wealth
  | household
  | judgment
  | migration
  | justice
  | messenger
deriving DecidableEq, Repr, Nonempty

inductive AlNisaInvariant
  | accountableRelation
deriving DecidableEq, Repr

def alNisaRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlNisaRegister => AlNisaInvariant.accountableRelation)
      AlNisaInvariant.accountableRelation :=
  TruthOneManyNamesWitness.constant_names_agree AlNisaInvariant.accountableRelation

theorem al_nisa_quality_clusters_shape :
    alNisaQualityClusters.length = 8
    ∧ alNisaQualityClusters.head? =
      some AlNisaQualityCluster.kinshipInheritanceBounds
    ∧ alNisaQualityClusters.getLast? =
      some AlNisaQualityCluster.messengersJesusInheritanceClosure := by
  exact ⟨rfl, rfl, rfl⟩

theorem al_nisa_imported_witness_count :
    alNisaImportedWitnessCount = 8 := by
  rfl

theorem al_nisa_sat_witness :
    alNisaSat alNisaInvariantLedger := by
  unfold alNisaSat alNisaInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_nisa_gap_witness :
    alNisaGapsExposeBoundary alNisaGapLedger := by
  unfold alNisaGapsExposeBoundary alNisaGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_nisa_access_archaeological :
    alNisaSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem al_nisa_reuses_opening_kinship_bounds :
    QuranAlNisaKinshipInheritanceWitness.kinshipInheritancePattern.singleSoulCreationNamed = true ∧
    QuranAlNisaKinshipInheritanceWitness.kinshipInheritancePattern.orphanPropertyProtected = true ∧
    QuranAlNisaKinshipInheritanceWitness.kinshipInheritancePattern.transferWitnessed = true ∧
    QuranAlNisaKinshipInheritanceWitness.kinshipInheritancePattern.godsBoundsNamed = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem quran_al_nisa_sura_quality_witness :
    alNisaQualityClusters.length = 8 ∧
    alNisaImportedWitnessCount = 8 ∧
    alNisaSat alNisaInvariantLedger ∧
    alNisaGapsExposeBoundary alNisaGapLedger ∧
    alNisaSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlNisaRegister => AlNisaInvariant.accountableRelation)
      AlNisaInvariant.accountableRelation := by
  exact ⟨al_nisa_quality_clusters_shape.left,
    al_nisa_imported_witness_count,
    al_nisa_sat_witness,
    al_nisa_gap_witness,
    al_nisa_access_archaeological,
    alNisaRegistersAgree⟩

end QuranAlNisaSuraQualityWitness
end Gnosis.Witnesses.Islam
