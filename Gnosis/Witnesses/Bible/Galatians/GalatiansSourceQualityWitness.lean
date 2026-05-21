import Gnosis.Witnesses.Bible.Galatians.GalatiansAnotherGospelBoundaryWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansAntiochConfrontationWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansCrucifiedWithChristWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansSpiritFaithFleshWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansLawCurseRedeemedWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansPromiseBeforeLawWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansSchoolmasterUnityWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansHeirAdoptionWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansElementsRelapseWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansBondwomanFreewomanWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansLibertyCircumcisionDebtWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansLoveServiceConsumptionWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansFleshSpiritFruitWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansRestorationBurdenWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansCrossNewCreationWitness
import Gnosis.Witnesses.Bible.Torah.TorahGalatiansPromiseLawTandemWitness
import Gnosis.Witnesses.Bible.Torah.TorahGalatiansHagarSarahTandemWitness

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansSourceQualityWitness

/-!
# Galatians -- Source Quality Spine

Book-level invariant: Galatians is the anti-capture epistle. Its target is not
"Judaism" as a cultural object; the target is any badge-system that tries to
turn a received promise into a payable debt, a Spirit-begun runtime into flesh
completion, or liberty into another yoke.

Primary gap/counterproof: another gospel is a source attack. It changes the
emitter, then changes the payload, then taxes the receiver with circumcision,
calendar relapse, exclusion zeal, and flesh-boasting. Paul answers by dragging
the dispute back through Abraham, curse, promise-before-law, schoolmaster
boundary, Hagar/Sarah topology, and the cross as world-severance.

Unseen sat: Galatians does not end at "freedom." It ends with burden-bearing,
sowing/reaping, and new creation. Liberty that consumes the neighbor falsifies
itself; liberty that serves through love becomes load-bearing topology.

No `sorry`, no new `axiom`.
-/

structure GalatiansBookInvariant where
  anotherGospelIsSourceAttack : Bool := true
  publicConfrontationProtectsGospelTruth : Bool := true
  crucifixionSeversOldJustificationRoute : Bool := true
  spiritBeginningCannotBeFleshCompleted : Bool := true
  curseTreeRedeemsLawDebt : Bool := true
  promisePrecedesLaterLaw : Bool := true
  schoolmasterEndsAtFaith : Bool := true
  heirAdoptionReplacesTutorBondage : Bool := true
  elementRelapseIsRuntimeRegression : Bool := true
  bondwomanFreewomanMapsPromiseBoundary : Bool := true
  circumcisionDebtThreatensWholeLaw : Bool := true
  loveServicePreventsLibertyConsumption : Bool := true
  spiritFruitContradictsFleshWorks : Bool := true
  burdensRestoreWithoutSelfDeception : Bool := true
  crossNewCreationClosesBoasting : Bool := true
deriving DecidableEq, Repr

def galatiansBookInvariant : GalatiansBookInvariant := {}

def galatiansQualitySpine (g : GalatiansBookInvariant) : Prop :=
  g.anotherGospelIsSourceAttack = true ∧
  g.publicConfrontationProtectsGospelTruth = true ∧
  g.crucifixionSeversOldJustificationRoute = true ∧
  g.spiritBeginningCannotBeFleshCompleted = true ∧
  g.curseTreeRedeemsLawDebt = true ∧
  g.promisePrecedesLaterLaw = true ∧
  g.schoolmasterEndsAtFaith = true ∧
  g.heirAdoptionReplacesTutorBondage = true ∧
  g.elementRelapseIsRuntimeRegression = true ∧
  g.bondwomanFreewomanMapsPromiseBoundary = true ∧
  g.circumcisionDebtThreatensWholeLaw = true ∧
  g.loveServicePreventsLibertyConsumption = true ∧
  g.spiritFruitContradictsFleshWorks = true ∧
  g.burdensRestoreWithoutSelfDeception = true ∧
  g.crossNewCreationClosesBoasting = true

theorem galatians_source_quality_spine :
    galatiansQualitySpine galatiansBookInvariant := by
  unfold galatiansQualitySpine galatiansBookInvariant
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_source_quality_witness :
    galatiansQualitySpine galatiansBookInvariant := by
  have _ := GalatiansAnotherGospelBoundaryWitness.galatians_another_gospel_boundary_witness
  have _ := GalatiansAntiochConfrontationWitness.galatians_antioch_confrontation_witness
  have _ := GalatiansCrucifiedWithChristWitness.galatians_crucified_with_christ_witness
  have _ := GalatiansSpiritFaithFleshWitness.galatians_spirit_faith_flesh_witness
  have _ := GalatiansLawCurseRedeemedWitness.galatians_law_curse_redeemed_witness
  have _ := GalatiansPromiseBeforeLawWitness.galatians_promise_before_law_witness
  have _ := GalatiansSchoolmasterUnityWitness.galatians_schoolmaster_unity_witness
  have _ := GalatiansHeirAdoptionWitness.galatians_heir_adoption_witness
  have _ := GalatiansElementsRelapseWitness.galatians_elements_relapse_witness
  have _ := GalatiansBondwomanFreewomanWitness.galatians_bondwoman_freewoman_witness
  have _ := GalatiansLibertyCircumcisionDebtWitness.galatians_liberty_circumcision_debt_witness
  have _ := GalatiansLoveServiceConsumptionWitness.galatians_love_service_consumption_witness
  have _ := GalatiansFleshSpiritFruitWitness.galatians_flesh_spirit_fruit_witness
  have _ := GalatiansRestorationBurdenWitness.galatians_restoration_burden_witness
  have _ := GalatiansCrossNewCreationWitness.galatians_cross_new_creation_witness
  have _ := Gnosis.Witnesses.Bible.Torah.TorahGalatiansPromiseLawTandemWitness.torah_galatians_promise_law_tandem_witness
  have _ := Gnosis.Witnesses.Bible.Torah.TorahGalatiansHagarSarahTandemWitness.torah_galatians_hagar_sarah_tandem_witness
  exact galatians_source_quality_spine

end GalatiansSourceQualityWitness
end Gnosis.Witnesses.Bible.Galatians
