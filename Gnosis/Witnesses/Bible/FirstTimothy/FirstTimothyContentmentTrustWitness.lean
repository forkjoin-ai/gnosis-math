import Init

namespace Gnosis.Witnesses.Bible.FirstTimothy
namespace FirstTimothyContentmentTrustWitness

/-!
# 1 Timothy 6 -- Wholesome Words, Contentment, Riches, and Guarded Trust

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95546-95577`.

The final counterproof is gain-as-godliness and false knowledge. Contentment is
great gain; uncertain riches are displaced by the living God; Timothy must guard
the entrusted deposit.

No `sorry`, no new `axiom`.
-/

structure GainGodlinessCounterproof where
  doctrineNotBlasphemedByService : Bool := true
  wholesomeWordsGodlinessDoctrine : Bool := true
  proudQuestionStrifeNamed : Bool := true
  corruptGainGodlinessError : Bool := true
  godlinessContentmentGreatGain : Bool := true
  nothingBroughtNothingCarried : Bool := true
  richDesireSnareNamed : Bool := true
  moneyLoveRootError : Bool := true
deriving DecidableEq, Repr

def gainGodlinessCounterproof : GainGodlinessCounterproof := {}

def gainGodlinessRejected (g : GainGodlinessCounterproof) : Prop :=
  g.doctrineNotBlasphemedByService = true ∧ g.wholesomeWordsGodlinessDoctrine = true ∧
  g.proudQuestionStrifeNamed = true ∧ g.corruptGainGodlinessError = true ∧
  g.godlinessContentmentGreatGain = true ∧ g.nothingBroughtNothingCarried = true ∧
  g.richDesireSnareNamed = true ∧ g.moneyLoveRootError = true

structure GuardedTrust where
  fleeFollowVirtues : Bool := true
  fightGoodFightLayHoldLife : Bool := true
  goodConfessionBeforeWitnesses : Bool := true
  commandmentKeptUntilAppearing : Bool := true
  kingOfKingsDwellsUnapproachableLight : Bool := true
  richTrustLivingGodNotRiches : Bool := true
  richInGoodWorksReadyDistribute : Bool := true
  keepCommittedTrust : Bool := true
  falseScienceAvoided : Bool := true
deriving DecidableEq, Repr

def guardedTrust : GuardedTrust := {}

def guardedTrustWitness (t : GuardedTrust) : Prop :=
  t.fleeFollowVirtues = true ∧ t.fightGoodFightLayHoldLife = true ∧
  t.goodConfessionBeforeWitnesses = true ∧ t.commandmentKeptUntilAppearing = true ∧
  t.kingOfKingsDwellsUnapproachableLight = true ∧ t.richTrustLivingGodNotRiches = true ∧
  t.richInGoodWorksReadyDistribute = true ∧ t.keepCommittedTrust = true ∧
  t.falseScienceAvoided = true

theorem first_timothy_gain_godliness_rejected :
    gainGodlinessRejected gainGodlinessCounterproof := by
  unfold gainGodlinessRejected gainGodlinessCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_guarded_trust :
    guardedTrustWitness guardedTrust := by
  unfold guardedTrustWitness guardedTrust
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_contentment_trust_witness :
    gainGodlinessRejected gainGodlinessCounterproof ∧ guardedTrustWitness guardedTrust := by
  exact ⟨first_timothy_gain_godliness_rejected, first_timothy_guarded_trust⟩

end FirstTimothyContentmentTrustWitness
end Gnosis.Witnesses.Bible.FirstTimothy
