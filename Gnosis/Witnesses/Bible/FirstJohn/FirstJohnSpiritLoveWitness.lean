namespace Gnosis.Witnesses.Bible.FirstJohn
namespace FirstJohnSpiritLoveWitness

/-!
# 1 John 4 -- Try the Spirits, Flesh Confession, and Fearless Love

Source slice: 1 John 4:1-21.

Chapter invariant: love is not credulity. The command to love one another is
paired with an instruction to test spirits, because false prophecy can mimic
warmth while refusing the manifested flesh of Christ.

Primary gap/counterproof: unseen-God language cannot bypass the seen brother.
The chapter closes the escape hatch: a claim to love God while hating the
visible brother is a lie. The invisible is audited through the visible without
collapsing the invisible into the visible.

Unseen sat: perfected love does not soothe fear; it casts fear out because fear
has torment. The source of love is prior gift, not heroic affect. "We love"
follows "he first loved us."

No `sorry`, no new `axiom`.
-/

structure SpiritTest where
  everySpiritNotBelieved : Bool := true
  spiritsTriedAgainstGod : Bool := true
  fleshConfessionMarksGodwardSpirit : Bool := true
  nonConfessionMarksAntichrist : Bool := true
  greaterIndwellingOvercomesWorld : Bool := true
deriving DecidableEq, Repr

def spiritTest : SpiritTest := {}

def fleshConfessionDiscernsSpirit (s : SpiritTest) : Prop :=
  s.everySpiritNotBelieved = true ∧
  s.spiritsTriedAgainstGod = true ∧
  s.fleshConfessionMarksGodwardSpirit = true ∧
  s.nonConfessionMarksAntichrist = true ∧
  s.greaterIndwellingOvercomesWorld = true

structure LoveSourceWitness where
  loveOneAnotherBecauseLoveOfGod : Bool := true
  nonLoveFailsGodKnowledge : Bool := true
  sonSentThatWeMightLive : Bool := true
  loveBeginsInGodNotUs : Bool := true
  unseenGodDwellsWhereBrotherLoveLives : Bool := true
deriving DecidableEq, Repr

def loveSourceWitness : LoveSourceWitness := {}

def loveSourceBeforeAgent (l : LoveSourceWitness) : Prop :=
  l.loveOneAnotherBecauseLoveOfGod = true ∧
  l.nonLoveFailsGodKnowledge = true ∧
  l.sonSentThatWeMightLive = true ∧
  l.loveBeginsInGodNotUs = true ∧
  l.unseenGodDwellsWhereBrotherLoveLives = true

structure FearlessVisibleBrother where
  confessedSonMarksMutualDwelling : Bool := true
  boldnessInJudgmentThroughPerfectedLove : Bool := true
  perfectLoveCastsOutFear : Bool := true
  firstLovedGroundsOurLove : Bool := true
  visibleBrotherHatredFalsifiesGodLove : Bool := true
  godLoveCommandsBrotherLove : Bool := true
deriving DecidableEq, Repr

def fearlessVisibleBrother : FearlessVisibleBrother := {}

def unseenAuditedByVisible (f : FearlessVisibleBrother) : Prop :=
  f.confessedSonMarksMutualDwelling = true ∧
  f.boldnessInJudgmentThroughPerfectedLove = true ∧
  f.perfectLoveCastsOutFear = true ∧
  f.firstLovedGroundsOurLove = true ∧
  f.visibleBrotherHatredFalsifiesGodLove = true ∧
  f.godLoveCommandsBrotherLove = true

theorem first_john_flesh_confession_discerns_spirit :
    fleshConfessionDiscernsSpirit spiritTest := by
  unfold fleshConfessionDiscernsSpirit spiritTest
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_love_source_before_agent :
    loveSourceBeforeAgent loveSourceWitness := by
  unfold loveSourceBeforeAgent loveSourceWitness
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_unseen_audited_by_visible :
    unseenAuditedByVisible fearlessVisibleBrother := by
  unfold unseenAuditedByVisible fearlessVisibleBrother
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_spirit_love_witness :
    fleshConfessionDiscernsSpirit spiritTest ∧
    loveSourceBeforeAgent loveSourceWitness ∧
    unseenAuditedByVisible fearlessVisibleBrother := by
  exact ⟨first_john_flesh_confession_discerns_spirit,
    first_john_love_source_before_agent,
    first_john_unseen_audited_by_visible⟩

end FirstJohnSpiritLoveWitness
end Gnosis.Witnesses.Bible.FirstJohn
