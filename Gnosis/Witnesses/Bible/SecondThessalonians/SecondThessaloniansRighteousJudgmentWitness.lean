import Init

namespace Gnosis.Witnesses.Bible.SecondThessalonians
namespace SecondThessaloniansRighteousJudgmentWitness

/-!
# 2 Thessalonians 1:1-12 -- Persecution, Righteous Judgment, and Worthy Calling

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95130-95166`.

The opening refuses to read persecution as system failure. Endurance under
tribulation becomes a manifest token of righteous judgment: trouble is recompensed
to troublers, rest is given to the troubled, and the name is glorified in the
called.

No `sorry`, no new `axiom`.
-/

structure PersecutionToken where
  faithGrowsExceedingly : Bool := true
  charityAboundsEachOther : Bool := true
  patienceFaithInPersecutions : Bool := true
  sufferingCountsWorthyKingdom : Bool := true
deriving DecidableEq, Repr

def persecutionToken : PersecutionToken := {}

def persecutionAsJudgmentToken (p : PersecutionToken) : Prop :=
  p.faithGrowsExceedingly = true ∧
  p.charityAboundsEachOther = true ∧
  p.patienceFaithInPersecutions = true ∧
  p.sufferingCountsWorthyKingdom = true

structure RighteousRecompense where
  tribulationRecompensedToTroublers : Bool := true
  troubledReceiveRest : Bool := true
  lordRevealedWithMightyAngels : Bool := true
  vengeanceOnNotKnowingGod : Bool := true
  destructionFromPresenceNamed : Bool := true
  glorifiedInSaints : Bool := true
  testimonyBelieved : Bool := true
  callingFulfilledWithPower : Bool := true
  nameGlorifiedInYouAndYouInHim : Bool := true
deriving DecidableEq, Repr

def righteousRecompense : RighteousRecompense := {}

def righteousRecompenseWitness (r : RighteousRecompense) : Prop :=
  r.tribulationRecompensedToTroublers = true ∧
  r.troubledReceiveRest = true ∧
  r.lordRevealedWithMightyAngels = true ∧
  r.vengeanceOnNotKnowingGod = true ∧
  r.destructionFromPresenceNamed = true ∧
  r.glorifiedInSaints = true ∧
  r.testimonyBelieved = true ∧
  r.callingFulfilledWithPower = true ∧
  r.nameGlorifiedInYouAndYouInHim = true

theorem second_thessalonians_persecution_token :
    persecutionAsJudgmentToken persecutionToken := by
  unfold persecutionAsJudgmentToken persecutionToken
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem second_thessalonians_righteous_recompense :
    righteousRecompenseWitness righteousRecompense := by
  unfold righteousRecompenseWitness righteousRecompense
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_thessalonians_righteous_judgment_witness :
    persecutionAsJudgmentToken persecutionToken ∧
    righteousRecompenseWitness righteousRecompense := by
  exact ⟨second_thessalonians_persecution_token,
    second_thessalonians_righteous_recompense⟩

end SecondThessaloniansRighteousJudgmentWitness
end Gnosis.Witnesses.Bible.SecondThessalonians
