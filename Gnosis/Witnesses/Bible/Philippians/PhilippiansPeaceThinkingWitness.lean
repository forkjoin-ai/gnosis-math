import Init

namespace Gnosis.Witnesses.Bible.Philippians
namespace PhilippiansPeaceThinkingWitness

/-!
# Philippians 4:1-9 -- Same Mind, Rejoicing, Prayer, and Peace Thinking

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94566-94593`.

The chapter opens with communal repair, then turns anxiety into prayer with
thanksgiving. Peace guards hearts and minds, while disciplined thought selects
true, honest, just, pure, lovely, and praiseworthy things.

No `sorry`, no new `axiom`.
-/

structure RepairRejoicePrayer where
  standFastInLord : Bool := true
  euodiasSyntycheSameMind : Bool := true
  fellowlabourersBookOfLife : Bool := true
  rejoiceAlways : Bool := true
  moderationKnownLordNear : Bool := true
  carefulForNothing : Bool := true
  prayerSupplicationThanksgiving : Bool := true
  peaceGuardsHeartsMinds : Bool := true
deriving DecidableEq, Repr

def repairRejoicePrayer : RepairRejoicePrayer := {}

def repairPrayerPeaceWitness (r : RepairRejoicePrayer) : Prop :=
  r.standFastInLord = true ∧ r.euodiasSyntycheSameMind = true ∧
  r.fellowlabourersBookOfLife = true ∧ r.rejoiceAlways = true ∧
  r.moderationKnownLordNear = true ∧ r.carefulForNothing = true ∧
  r.prayerSupplicationThanksgiving = true ∧ r.peaceGuardsHeartsMinds = true

structure PeaceThinking where
  trueHonestJustPure : Bool := true
  lovelyGoodReport : Bool := true
  virtuePraiseThought : Bool := true
  learnedReceivedHeardSeenDo : Bool := true
  godOfPeaceWithYou : Bool := true
deriving DecidableEq, Repr

def peaceThinking : PeaceThinking := {}

def peaceThinkingWitness (p : PeaceThinking) : Prop :=
  p.trueHonestJustPure = true ∧ p.lovelyGoodReport = true ∧
  p.virtuePraiseThought = true ∧ p.learnedReceivedHeardSeenDo = true ∧
  p.godOfPeaceWithYou = true

theorem philippians_repair_prayer_peace :
    repairPrayerPeaceWitness repairRejoicePrayer := by
  unfold repairPrayerPeaceWitness repairRejoicePrayer
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_peace_thinking :
    peaceThinkingWitness peaceThinking := by
  unfold peaceThinkingWitness peaceThinking
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_peace_thinking_witness :
    repairPrayerPeaceWitness repairRejoicePrayer ∧ peaceThinkingWitness peaceThinking := by
  exact ⟨philippians_repair_prayer_peace, philippians_peace_thinking⟩

end PhilippiansPeaceThinkingWitness
end Gnosis.Witnesses.Bible.Philippians
