namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsSonAngelsWitness

/-!
# Hebrews 1 -- Son, Angels, and Final Speech

Source slice: Hebrews 1:1-14.

Chapter invariant: revelation reaches its fixed point in the Son. The former
prophetic many-times/many-ways speech is not despised; it is gathered into the
last-days Son who is heir, maker, brightness, image, upholder, purifier, and
enthroned at the right hand.

Primary gap/counterproof: angelic mediation is real ministry, but it cannot
occupy the Son's namespace. Angels are spirits, ministers, and sent servants;
the Son receives throne, sceptre, permanence, unchanged years, and the right-hand
footstool promise.

Unseen sat: Hebrews opens by separating transmission from identity. A messenger
can carry fire, but the Son carries the source-signature that remains when
created heavens are folded like a garment.

No `sorry`, no new `axiom`.
-/

structure FinalSpeechField where
  sundryPropheticSpeechGathered : Bool := true
  sonIsHeirAndWorldMaker : Bool := true
  sonUpholdsByPowerWord : Bool := true
  purificationCompletesBeforeSession : Bool := true
deriving DecidableEq, Repr

def finalSpeechField : FinalSpeechField := {}

def finalSpeechWitness (f : FinalSpeechField) : Prop :=
  f.sundryPropheticSpeechGathered = true ∧
  f.sonIsHeirAndWorldMaker = true ∧
  f.sonUpholdsByPowerWord = true ∧
  f.purificationCompletesBeforeSession = true

structure AngelBoundary where
  angelsAreMinisteringSpirits : Bool := true
  sonReceivesBetterName : Bool := true
  sonReceivesThroneAndSceptre : Bool := true
  sonRemainsWhenCreationChanges : Bool := true
  sonReceivesRightHandFootstool : Bool := true
deriving DecidableEq, Repr

def angelBoundary : AngelBoundary := {}

def angelMediationCounterproof (b : AngelBoundary) : Prop :=
  b.angelsAreMinisteringSpirits = true ∧
  b.sonReceivesBetterName = true ∧
  b.sonReceivesThroneAndSceptre = true ∧
  b.sonRemainsWhenCreationChanges = true ∧
  b.sonReceivesRightHandFootstool = true

theorem hebrews_final_speech :
    finalSpeechWitness finalSpeechField := by
  unfold finalSpeechWitness finalSpeechField
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem hebrews_angel_boundary :
    angelMediationCounterproof angelBoundary := by
  unfold angelMediationCounterproof angelBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_son_angels_witness :
    finalSpeechWitness finalSpeechField ∧
    angelMediationCounterproof angelBoundary := by
  exact ⟨hebrews_final_speech, hebrews_angel_boundary⟩

end HebrewsSonAngelsWitness
end Gnosis.Witnesses.Bible.Hebrews
