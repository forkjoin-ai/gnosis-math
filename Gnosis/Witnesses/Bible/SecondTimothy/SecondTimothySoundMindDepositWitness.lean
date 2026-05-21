import Init

namespace Gnosis.Witnesses.Bible.SecondTimothy
namespace SecondTimothySoundMindDepositWitness

/-!
# 2 Timothy 1 -- Unfeigned Faith, Sound Mind, and Guarded Deposit

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95578-95629`.

The opening rejects fear as the governing spirit. Timothy is called to stir the
gift, share affliction, hold sound words, and guard the good deposit by the Holy
Ghost while abandonment and loyal refreshment are both named.

No `sorry`, no new `axiom`.
-/

structure SoundMindCalling where
  unfeignedFaithRemembered : Bool := true
  giftStirredByHands : Bool := true
  notFearButPowerLoveSoundMind : Bool := true
  notAshamedOfTestimonyOrPrisoner : Bool := true
  afflictionSharedByPower : Bool := true
  purposeGraceBeforeWorld : Bool := true
  deathAbolishedLifeImmortalityLight : Bool := true
deriving DecidableEq, Repr

def soundMindCalling : SoundMindCalling := {}

def soundMindCallingWitness (s : SoundMindCalling) : Prop :=
  s.unfeignedFaithRemembered = true ∧
  s.giftStirredByHands = true ∧
  s.notFearButPowerLoveSoundMind = true ∧
  s.notAshamedOfTestimonyOrPrisoner = true ∧
  s.afflictionSharedByPower = true ∧
  s.purposeGraceBeforeWorld = true ∧
  s.deathAbolishedLifeImmortalityLight = true

structure GuardedDeposit where
  sufferYetNotAshamed : Bool := true
  persuadedHeKeepsCommitted : Bool := true
  soundWordsHeldInFaithLove : Bool := true
  goodThingKeptByHolyGhost : Bool := true
  asiaTurnedAwayNamed : Bool := true
  onesiphorusNotAshamedOfChain : Bool := true
  mercyInThatDayRequested : Bool := true
deriving DecidableEq, Repr

def guardedDeposit : GuardedDeposit := {}

def guardedDepositWitness (g : GuardedDeposit) : Prop :=
  g.sufferYetNotAshamed = true ∧
  g.persuadedHeKeepsCommitted = true ∧
  g.soundWordsHeldInFaithLove = true ∧
  g.goodThingKeptByHolyGhost = true ∧
  g.asiaTurnedAwayNamed = true ∧
  g.onesiphorusNotAshamedOfChain = true ∧
  g.mercyInThatDayRequested = true

theorem second_timothy_sound_mind_calling :
    soundMindCallingWitness soundMindCalling := by
  unfold soundMindCallingWitness soundMindCalling
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_timothy_guarded_deposit :
    guardedDepositWitness guardedDeposit := by
  unfold guardedDepositWitness guardedDeposit
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_timothy_sound_mind_deposit_witness :
    soundMindCallingWitness soundMindCalling ∧
    guardedDepositWitness guardedDeposit := by
  exact ⟨second_timothy_sound_mind_calling, second_timothy_guarded_deposit⟩

end SecondTimothySoundMindDepositWitness
end Gnosis.Witnesses.Bible.SecondTimothy
