import Init

namespace Gnosis.Witnesses.Bible.Titus
namespace TitusEldersVainTalkersWitness

/-!
# Titus 1 -- Ordered Elders, Sound Doctrine, and Vain Talkers Stopped

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95804-95850`.

The Crete assignment is order under doctrinal noise: elders must hold faithful
word so they can exhort by sound doctrine and convict gainsayers. The gap is vain
talk that subverts households for gain while professing God and denying him in
works.

No `sorry`, no new `axiom`.
-/

structure OrderedElders where
  truthAfterGodliness : Bool := true
  eternalLifePromisedByGodCannotLie : Bool := true
  orderWantingThingsInCrete : Bool := true
  eldersOrdainedEveryCity : Bool := true
  elderHouseholdBlameless : Bool := true
  bishopStewardNotSelfwilled : Bool := true
  hospitalitySobrietyJusticeHoliness : Bool := true
  faithfulWordHeldForDoctrine : Bool := true
deriving DecidableEq, Repr

def orderedElders : OrderedElders := {}

def orderedEldersWitness (e : OrderedElders) : Prop :=
  e.truthAfterGodliness = true ∧ e.eternalLifePromisedByGodCannotLie = true ∧
  e.orderWantingThingsInCrete = true ∧ e.eldersOrdainedEveryCity = true ∧
  e.elderHouseholdBlameless = true ∧ e.bishopStewardNotSelfwilled = true ∧
  e.hospitalitySobrietyJusticeHoliness = true ∧ e.faithfulWordHeldForDoctrine = true

structure VainTalkerCounterproof where
  unrulyVainTalkersDeceivers : Bool := true
  mouthsStopped : Bool := true
  householdsSubvertedForGain : Bool := true
  sharpRebukeTowardSoundFaith : Bool := true
  fablesCommandsTurnFromTruth : Bool := true
  defiledMindConscience : Bool := true
  professGodDenyInWorks : Bool := true
  reprobateUntoGoodWork : Bool := true
deriving DecidableEq, Repr

def vainTalkerCounterproof : VainTalkerCounterproof := {}

def vainTalkerRejected (v : VainTalkerCounterproof) : Prop :=
  v.unrulyVainTalkersDeceivers = true ∧ v.mouthsStopped = true ∧
  v.householdsSubvertedForGain = true ∧ v.sharpRebukeTowardSoundFaith = true ∧
  v.fablesCommandsTurnFromTruth = true ∧ v.defiledMindConscience = true ∧
  v.professGodDenyInWorks = true ∧ v.reprobateUntoGoodWork = true

theorem titus_ordered_elders :
    orderedEldersWitness orderedElders := by
  unfold orderedEldersWitness orderedElders
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem titus_vain_talker_rejected :
    vainTalkerRejected vainTalkerCounterproof := by
  unfold vainTalkerRejected vainTalkerCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem titus_elders_vain_talkers_witness :
    orderedEldersWitness orderedElders ∧
    vainTalkerRejected vainTalkerCounterproof := by
  exact ⟨titus_ordered_elders, titus_vain_talker_rejected⟩

end TitusEldersVainTalkersWitness
end Gnosis.Witnesses.Bible.Titus
