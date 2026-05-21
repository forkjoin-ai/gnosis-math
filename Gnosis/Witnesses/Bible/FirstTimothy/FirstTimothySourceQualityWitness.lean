import Gnosis.Witnesses.Bible.FirstTimothy.FirstTimothyContentmentTrustWitness
import Gnosis.Witnesses.Bible.FirstTimothy.FirstTimothyDoctrineMercyChargeWitness
import Gnosis.Witnesses.Bible.FirstTimothy.FirstTimothyGodlinessDisciplineWitness
import Gnosis.Witnesses.Bible.FirstTimothy.FirstTimothyHouseholdTruthWitness
import Gnosis.Witnesses.Bible.FirstTimothy.FirstTimothyPrayerOrderMediatorWitness
import Gnosis.Witnesses.Bible.FirstTimothy.FirstTimothyWidowsEldersPurityWitness

namespace Gnosis.Witnesses.Bible.FirstTimothy
namespace FirstTimothySourceQualityWitness

/-!
# 1 Timothy -- Source Quality Spine

Book invariant: entrusted doctrine must produce a truth-bearing household. The
source is not merely church-order inventory; it is a custody protocol for sound
words, pure conscience, godliness, tested office, disciplined care, and guarded
trust.

Primary gap/counterproof: false teaching converts doctrine into noise or profit:
fables, endless genealogies, law-jangling, seared asceticism, partiality,
gain-as-godliness, and false science. Each counterfeit is named by its failure to
produce charity, good conscience, faith unfeigned, and godliness with contentment.

Unseen sat: orthodoxy is not bare proposition storage. It is doctrine embodied as
household behavior, mercy pattern, public prayer, tested service, care for real
need, and refusal to monetize godliness.

No `sorry`, no new `axiom`.
-/

structure FirstTimothyInvariant where
  doctrineEndsInCharity : Bool := true
  householdStandsAsTruthPillar : Bool := true
  godlinessDisciplinesEmbodiedConduct : Bool := true
  entrustedTrustMustBeGuarded : Bool := true
deriving DecidableEq, Repr

def firstTimothyInvariant : FirstTimothyInvariant := {}

def entrustedDoctrineInvariant (i : FirstTimothyInvariant) : Prop :=
  i.doctrineEndsInCharity = true ∧
  i.householdStandsAsTruthPillar = true ∧
  i.godlinessDisciplinesEmbodiedConduct = true ∧
  i.entrustedTrustMustBeGuarded = true

structure FirstTimothyCounterproof where
  fablesCannotEdifyInFaith : Bool := true
  lawJanglingCannotTeachSoundDoctrine : Bool := true
  asceticForbiddingCannotNameThankfulCreation : Bool := true
  partialityCannotGuardHouseholdTruth : Bool := true
  gainCannotBeGodliness : Bool := true
  falseScienceCannotKeepTrust : Bool := true
deriving DecidableEq, Repr

def firstTimothyCounterproof : FirstTimothyCounterproof := {}

def counterfeitDoctrineRejected (c : FirstTimothyCounterproof) : Prop :=
  c.fablesCannotEdifyInFaith = true ∧
  c.lawJanglingCannotTeachSoundDoctrine = true ∧
  c.asceticForbiddingCannotNameThankfulCreation = true ∧
  c.partialityCannotGuardHouseholdTruth = true ∧
  c.gainCannotBeGodliness = true ∧
  c.falseScienceCannotKeepTrust = true

theorem first_timothy_quality_invariant :
    entrustedDoctrineInvariant firstTimothyInvariant := by
  unfold entrustedDoctrineInvariant firstTimothyInvariant
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem first_timothy_quality_counterproof :
    counterfeitDoctrineRejected firstTimothyCounterproof := by
  unfold counterfeitDoctrineRejected firstTimothyCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_source_quality_witness :
    entrustedDoctrineInvariant firstTimothyInvariant ∧
    counterfeitDoctrineRejected firstTimothyCounterproof ∧
    FirstTimothyDoctrineMercyChargeWitness.doctrineChargeWitness
      FirstTimothyDoctrineMercyChargeWitness.doctrineCharge ∧
    FirstTimothyHouseholdTruthWitness.householdTruthWitness
      FirstTimothyHouseholdTruthWitness.householdTruthMystery ∧
    FirstTimothyGodlinessDisciplineWitness.asceticCounterfeitWitness
      FirstTimothyGodlinessDisciplineWitness.asceticCounterfeit ∧
    FirstTimothyWidowsEldersPurityWitness.elderPurityWitness
      FirstTimothyWidowsEldersPurityWitness.elderPurityDiscernment ∧
    FirstTimothyContentmentTrustWitness.gainGodlinessRejected
      FirstTimothyContentmentTrustWitness.gainGodlinessCounterproof := by
  exact ⟨first_timothy_quality_invariant,
    first_timothy_quality_counterproof,
    FirstTimothyDoctrineMercyChargeWitness.first_timothy_doctrine_charge,
    FirstTimothyHouseholdTruthWitness.first_timothy_household_truth,
    FirstTimothyGodlinessDisciplineWitness.first_timothy_ascetic_counterfeit,
    FirstTimothyWidowsEldersPurityWitness.first_timothy_elder_purity,
    FirstTimothyContentmentTrustWitness.first_timothy_gain_godliness_rejected⟩

end FirstTimothySourceQualityWitness
end Gnosis.Witnesses.Bible.FirstTimothy
