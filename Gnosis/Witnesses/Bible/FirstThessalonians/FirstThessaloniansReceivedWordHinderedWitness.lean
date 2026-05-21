import Init

namespace Gnosis.Witnesses.Bible.FirstThessalonians
namespace FirstThessaloniansReceivedWordHinderedWitness

/-!
# 1 Thessalonians 2:13-20 -- Word Received as God, Suffering Pattern, Hindered Visit

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94958-94987`.

The word is received not as human speech but as God's effective word. The witness
then records opposition to Gentile speech, Satanic hindrance, and the community
itself as hope, joy, crown, glory.

No `sorry`, no new `axiom`.
-/

structure ReceivedWordSuffering where
  wordReceivedNotMenButGod : Bool := true
  wordWorksInBelievers : Bool := true
  followersOfJudeanChurches : Bool := true
  sufferedOfCountrymen : Bool := true
  forbiddingGentileSpeechNamed : Bool := true
  wrathUttermostNamed : Bool := true
deriving DecidableEq, Repr

def receivedWordSuffering : ReceivedWordSuffering := {}

def receivedWordWitness (r : ReceivedWordSuffering) : Prop :=
  r.wordReceivedNotMenButGod = true ∧ r.wordWorksInBelievers = true ∧
  r.followersOfJudeanChurches = true ∧ r.sufferedOfCountrymen = true ∧
  r.forbiddingGentileSpeechNamed = true ∧ r.wrathUttermostNamed = true

structure HinderedJoyCrown where
  absentPresenceNotHeart : Bool := true
  faceDesireAbundant : Bool := true
  satanHinderedVisit : Bool := true
  communityHopeJoyCrown : Bool := true
  presenceAtComingNamed : Bool := true
  gloryAndJoy : Bool := true
deriving DecidableEq, Repr

def hinderedJoyCrown : HinderedJoyCrown := {}

def hinderedJoyCrownWitness (h : HinderedJoyCrown) : Prop :=
  h.absentPresenceNotHeart = true ∧ h.faceDesireAbundant = true ∧
  h.satanHinderedVisit = true ∧ h.communityHopeJoyCrown = true ∧
  h.presenceAtComingNamed = true ∧ h.gloryAndJoy = true

theorem first_thessalonians_received_word :
    receivedWordWitness receivedWordSuffering := by
  unfold receivedWordWitness receivedWordSuffering
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_thessalonians_hindered_joy_crown :
    hinderedJoyCrownWitness hinderedJoyCrown := by
  unfold hinderedJoyCrownWitness hinderedJoyCrown
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_thessalonians_received_word_hindered_witness :
    receivedWordWitness receivedWordSuffering ∧
    hinderedJoyCrownWitness hinderedJoyCrown := by
  exact ⟨first_thessalonians_received_word, first_thessalonians_hindered_joy_crown⟩

end FirstThessaloniansReceivedWordHinderedWitness
end Gnosis.Witnesses.Bible.FirstThessalonians
