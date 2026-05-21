import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansOldNewWalkWitness

/-!
# Ephesians 4:17-32 -- Old Man, Renewed Mind, and Edifying Speech

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94192-94231`.

Ephesians turns ontology into habits: old-man corruption is put off, renewed mind
puts on new-man holiness, then speech, anger, labor, Spirit-seal, and forgiveness
become the proof surface.

No `sorry`, no new `axiom`.
-/

structure OldNewWalk where
  gentileVanityWalkRejected : Bool := true
  understandingDarkened : Bool := true
  alienatedThroughBlindness : Bool := true
  oldManPutOff : Bool := true
  renewedInSpiritOfMind : Bool := true
  newManPutOn : Bool := true
  righteousnessTrueHoliness : Bool := true
deriving DecidableEq, Repr

def oldNewWalk : OldNewWalk := {}

def oldNewWalkWitness (w : OldNewWalk) : Prop :=
  w.gentileVanityWalkRejected = true ∧ w.understandingDarkened = true ∧
  w.alienatedThroughBlindness = true ∧ w.oldManPutOff = true ∧
  w.renewedInSpiritOfMind = true ∧ w.newManPutOn = true ∧
  w.righteousnessTrueHoliness = true

structure EdifyingConduct where
  lyingPutAwayTruthSpoken : Bool := true
  angryAndSinNot : Bool := true
  noPlaceToDevil : Bool := true
  thiefLaborsToGive : Bool := true
  corruptSpeechRejected : Bool := true
  edifyingGraceSpeech : Bool := true
  spiritSealNotGrieved : Bool := true
  bitternessMalicePutAway : Bool := true
  kindnessTenderForgiveness : Bool := true
deriving DecidableEq, Repr

def edifyingConduct : EdifyingConduct := {}

def edifyingConductWitness (e : EdifyingConduct) : Prop :=
  e.lyingPutAwayTruthSpoken = true ∧ e.angryAndSinNot = true ∧
  e.noPlaceToDevil = true ∧ e.thiefLaborsToGive = true ∧
  e.corruptSpeechRejected = true ∧ e.edifyingGraceSpeech = true ∧
  e.spiritSealNotGrieved = true ∧ e.bitternessMalicePutAway = true ∧
  e.kindnessTenderForgiveness = true

theorem ephesians_old_new_walk :
    oldNewWalkWitness oldNewWalk := by
  unfold oldNewWalkWitness oldNewWalk
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_edifying_conduct :
    edifyingConductWitness edifyingConduct := by
  unfold edifyingConductWitness edifyingConduct
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_old_new_walk_witness :
    oldNewWalkWitness oldNewWalk ∧ edifyingConductWitness edifyingConduct := by
  exact ⟨ephesians_old_new_walk, ephesians_edifying_conduct⟩

end EphesiansOldNewWalkWitness
end Gnosis.Witnesses.Bible.Ephesians
