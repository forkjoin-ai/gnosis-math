import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansLightWisdomWitness

/-!
# Ephesians 5:1-21 -- Walk in Love, Light, and Wisdom

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94232-94272`.

The walk shifts through love, light, and wisdom. The antitheorem is vain words,
darkness, and excess; the positive witness is manifested light, redeemed time,
Spirit filling, song, thanks, and mutual submission.

No `sorry`, no new `axiom`.
-/

structure LoveLightWalk where
  followersOfGodDearChildren : Bool := true
  walkInLoveAsChristOffering : Bool := true
  impurityCovetousnessNotNamed : Bool := true
  thanksgivingInsteadOfFoolishSpeech : Bool := true
  noInheritanceForIdolatrousCovetousness : Bool := true
  vainWordsDeceptionRejected : Bool := true
  childrenOfLightWalk : Bool := true
  darknessReprovedByLight : Bool := true
deriving DecidableEq, Repr

def loveLightWalk : LoveLightWalk := {}

def loveLightWitness (l : LoveLightWalk) : Prop :=
  l.followersOfGodDearChildren = true ∧ l.walkInLoveAsChristOffering = true ∧
  l.impurityCovetousnessNotNamed = true ∧ l.thanksgivingInsteadOfFoolishSpeech = true ∧
  l.noInheritanceForIdolatrousCovetousness = true ∧ l.vainWordsDeceptionRejected = true ∧
  l.childrenOfLightWalk = true ∧ l.darknessReprovedByLight = true

structure WisdomSpiritWalk where
  awakeAriseLightGiven : Bool := true
  circumspectWiseWalk : Bool := true
  timeRedeemed : Bool := true
  lordWillUnderstood : Bool := true
  wineExcessRejected : Bool := true
  spiritFilled : Bool := true
  psalmsHymnsSpiritualSongs : Bool := true
  thanksAlways : Bool := true
  mutualSubmission : Bool := true
deriving DecidableEq, Repr

def wisdomSpiritWalk : WisdomSpiritWalk := {}

def wisdomSpiritWitness (w : WisdomSpiritWalk) : Prop :=
  w.awakeAriseLightGiven = true ∧ w.circumspectWiseWalk = true ∧
  w.timeRedeemed = true ∧ w.lordWillUnderstood = true ∧
  w.wineExcessRejected = true ∧ w.spiritFilled = true ∧
  w.psalmsHymnsSpiritualSongs = true ∧ w.thanksAlways = true ∧
  w.mutualSubmission = true

theorem ephesians_love_light :
    loveLightWitness loveLightWalk := by
  unfold loveLightWitness loveLightWalk
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_wisdom_spirit :
    wisdomSpiritWitness wisdomSpiritWalk := by
  unfold wisdomSpiritWitness wisdomSpiritWalk
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_light_wisdom_witness :
    loveLightWitness loveLightWalk ∧ wisdomSpiritWitness wisdomSpiritWalk := by
  exact ⟨ephesians_love_light, ephesians_wisdom_spirit⟩

end EphesiansLightWisdomWitness
end Gnosis.Witnesses.Bible.Ephesians
