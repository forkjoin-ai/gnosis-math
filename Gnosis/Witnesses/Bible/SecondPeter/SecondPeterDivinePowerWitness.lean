namespace Gnosis.Witnesses.Bible.SecondPeter
namespace SecondPeterDivinePowerWitness

/-!
# 2 Peter 1 -- Divine Power, Remembered Virtue, and Prophetic Light

Source slice: 2 Peter 1:1-21.

Chapter invariant: life and godliness begin from gift, not self-manufacture.
Divine power has given what pertains to life and godliness; promises make
participation possible and corruption through lust escapable.

Primary gap/counterproof: virtue is not ornamental morality. Without the faith-
to-charity chain, a person becomes blind, cannot see afar off, and forgets old-
sin purgation. Fruitlessness is memory failure.

Unseen sat: apostolic witness is not fable, and prophecy is not private
possession. Eyewitness majesty and the more sure prophetic word form a lamp in a
dark place until the day star rises in the heart.

No `sorry`, no new `axiom`.
-/

structure DivinePowerGift where
  likePreciousFaithReceived : Bool := true
  gracePeaceMultipliedByKnowledge : Bool := true
  powerGivesLifeAndGodliness : Bool := true
  promisesMakeDivineParticipation : Bool := true
  lustCorruptionEscaped : Bool := true
deriving DecidableEq, Repr

def divinePowerGift : DivinePowerGift := {}

def divinePowerWitness (g : DivinePowerGift) : Prop :=
  g.likePreciousFaithReceived = true ∧
  g.gracePeaceMultipliedByKnowledge = true ∧
  g.powerGivesLifeAndGodliness = true ∧
  g.promisesMakeDivineParticipation = true ∧
  g.lustCorruptionEscaped = true

structure VirtueMemoryChain where
  faithAddsVirtueKnowledgeTemperance : Bool := true
  patienceGodlinessKindnessCharityAdded : Bool := true
  aboundingChainPreventsUnfruitfulness : Bool := true
  lackMakesBlindAndShortSighted : Bool := true
  lackForgetsOldSinPurgation : Bool := true
  diligenceMakesCallingElectionSure : Bool := true
deriving DecidableEq, Repr

def virtueMemoryChain : VirtueMemoryChain := {}

def virtueMemoryWitness (v : VirtueMemoryChain) : Prop :=
  v.faithAddsVirtueKnowledgeTemperance = true ∧
  v.patienceGodlinessKindnessCharityAdded = true ∧
  v.aboundingChainPreventsUnfruitfulness = true ∧
  v.lackMakesBlindAndShortSighted = true ∧
  v.lackForgetsOldSinPurgation = true ∧
  v.diligenceMakesCallingElectionSure = true

structure PropheticLightCounterproof where
  remembranceOutlivesTabernacle : Bool := true
  cunningFablesRejected : Bool := true
  eyewitnessMajestyHeardVoice : Bool := true
  surePropheticWordLightsDarkPlace : Bool := true
  prophecyNotPrivateInterpretation : Bool := true
  holyMenMovedByHolyGhost : Bool := true
deriving DecidableEq, Repr

def propheticLightCounterproof : PropheticLightCounterproof := {}

def fablePrivateWillRejected (c : PropheticLightCounterproof) : Prop :=
  c.remembranceOutlivesTabernacle = true ∧
  c.cunningFablesRejected = true ∧
  c.eyewitnessMajestyHeardVoice = true ∧
  c.surePropheticWordLightsDarkPlace = true ∧
  c.prophecyNotPrivateInterpretation = true ∧
  c.holyMenMovedByHolyGhost = true

theorem second_peter_divine_power :
    divinePowerWitness divinePowerGift := by
  unfold divinePowerWitness divinePowerGift
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem second_peter_virtue_memory :
    virtueMemoryWitness virtueMemoryChain := by
  unfold virtueMemoryWitness virtueMemoryChain
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_peter_fable_private_will_rejected :
    fablePrivateWillRejected propheticLightCounterproof := by
  unfold fablePrivateWillRejected propheticLightCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_peter_divine_power_witness :
    divinePowerWitness divinePowerGift ∧
    virtueMemoryWitness virtueMemoryChain ∧
    fablePrivateWillRejected propheticLightCounterproof := by
  exact ⟨second_peter_divine_power,
    second_peter_virtue_memory,
    second_peter_fable_private_will_rejected⟩

end SecondPeterDivinePowerWitness
end Gnosis.Witnesses.Bible.SecondPeter
