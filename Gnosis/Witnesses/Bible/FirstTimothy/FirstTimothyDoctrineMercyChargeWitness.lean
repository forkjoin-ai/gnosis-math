import Init

namespace Gnosis.Witnesses.Bible.FirstTimothy
namespace FirstTimothyDoctrineMercyChargeWitness

/-!
# 1 Timothy 1 -- Sound Doctrine, Mercy Pattern, and Good Warfare

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95258-95325`.

The opening charge rejects speculative doctrine: fables and genealogies generate
questions rather than faithful edification. The counter-signal is charity from a
pure heart, lawful law-use, mercy shown to the chief sinner, and warfare held by
faith and good conscience.

No `sorry`, no new `axiom`.
-/

structure DoctrineCharge where
  noOtherDoctrineCharged : Bool := true
  fablesGenealogiesRejected : Bool := true
  questionsNotEdifyingNamed : Bool := true
  commandmentEndsInCharity : Bool := true
  vainJanglingFromSwerving : Bool := true
  lawUsedLawfully : Bool := true
  soundDoctrineGospelTrust : Bool := true
deriving DecidableEq, Repr

def doctrineCharge : DoctrineCharge := {}

def doctrineChargeWitness (d : DoctrineCharge) : Prop :=
  d.noOtherDoctrineCharged = true ∧ d.fablesGenealogiesRejected = true ∧
  d.questionsNotEdifyingNamed = true ∧ d.commandmentEndsInCharity = true ∧
  d.vainJanglingFromSwerving = true ∧ d.lawUsedLawfully = true ∧
  d.soundDoctrineGospelTrust = true

structure MercyWarfare where
  persecutorObtainedMercy : Bool := true
  graceAbundantFaithLove : Bool := true
  sinnersSavedFaithfulSaying : Bool := true
  chiefSinnerPatternLongsuffering : Bool := true
  kingEternalDoxology : Bool := true
  propheciesEnableGoodWarfare : Bool := true
  faithGoodConscienceHeld : Bool := true
  shipwreckCounterexampleNamed : Bool := true
deriving DecidableEq, Repr

def mercyWarfare : MercyWarfare := {}

def mercyWarfareWitness (m : MercyWarfare) : Prop :=
  m.persecutorObtainedMercy = true ∧ m.graceAbundantFaithLove = true ∧
  m.sinnersSavedFaithfulSaying = true ∧ m.chiefSinnerPatternLongsuffering = true ∧
  m.kingEternalDoxology = true ∧ m.propheciesEnableGoodWarfare = true ∧
  m.faithGoodConscienceHeld = true ∧ m.shipwreckCounterexampleNamed = true

theorem first_timothy_doctrine_charge :
    doctrineChargeWitness doctrineCharge := by
  unfold doctrineChargeWitness doctrineCharge
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_mercy_warfare :
    mercyWarfareWitness mercyWarfare := by
  unfold mercyWarfareWitness mercyWarfare
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_doctrine_mercy_charge_witness :
    doctrineChargeWitness doctrineCharge ∧ mercyWarfareWitness mercyWarfare := by
  exact ⟨first_timothy_doctrine_charge, first_timothy_mercy_warfare⟩

end FirstTimothyDoctrineMercyChargeWitness
end Gnosis.Witnesses.Bible.FirstTimothy
