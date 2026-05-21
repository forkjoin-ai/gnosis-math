namespace Gnosis.Witnesses.Bible.FirstJohn
namespace FirstJohnCainDeedTruthWitness

/-!
# 1 John 3 -- Sonship, Cain, Deed-Truth, and Greater-Than-Heart Assurance

Source slice: 1 John 3:1-24.

Chapter invariant: sonship is real before it is fully visible. "It doth not yet
appear what we shall be" is not uncertainty collapse; it is hope that purifies
because future likeness already exerts pressure on present conduct.

Primary gap/counterproof: Cain exposes hate as anti-brother computation. Murder
does not begin at the weapon; it begins where righteous works become intolerable
to evil works. Love without material openness to a brother's need fails the
dwelling test.

Unseen sat: the heart is not the final court. Condemnation is acknowledged, but
God is greater than the heart and knows all things. Assurance is not
self-hypnosis; it is deed-and-truth alignment under a larger judge.

No `sorry`, no new `axiom`.
-/

structure SonshipPurity where
  calledSonsUnknownByWorld : Bool := true
  notYetAppearedButLikenessPromised : Bool := true
  seeingAsHeIsPurifiesHope : Bool := true
  manifestedToTakeAwaySins : Bool := true
  seedRemainingMarksNewBirth : Bool := true
deriving DecidableEq, Repr

def sonshipPurity : SonshipPurity := {}

def futureLikenessPurifies (s : SonshipPurity) : Prop :=
  s.calledSonsUnknownByWorld = true ∧
  s.notYetAppearedButLikenessPromised = true ∧
  s.seeingAsHeIsPurifiesHope = true ∧
  s.manifestedToTakeAwaySins = true ∧
  s.seedRemainingMarksNewBirth = true

structure CainBrotherTest where
  righteousnessAndLoveManifestChildren : Bool := true
  loveOneAnotherHeardFromBeginning : Bool := true
  cainSlewBecauseWorksEvil : Bool := true
  brotherHatredAbidesInDeath : Bool := true
  hateCountsAsMurder : Bool := true
deriving DecidableEq, Repr

def cainBrotherTest : CainBrotherTest := {}

def cainHateCounterproof (c : CainBrotherTest) : Prop :=
  c.righteousnessAndLoveManifestChildren = true ∧
  c.loveOneAnotherHeardFromBeginning = true ∧
  c.cainSlewBecauseWorksEvil = true ∧
  c.brotherHatredAbidesInDeath = true ∧
  c.hateCountsAsMurder = true

structure DeedTruthAssurance where
  lifeLaidDownFormsBrotherLove : Bool := true
  closedCompassionFailsLoveDwelling : Bool := true
  loveInDeedAndTruth : Bool := true
  godGreaterThanCondemningHeart : Bool := true
  believeAndLoveCommandJoined : Bool := true
  spiritGivenMarksAbiding : Bool := true
deriving DecidableEq, Repr

def deedTruthAssurance : DeedTruthAssurance := {}

def greaterThanHeartAssurance (d : DeedTruthAssurance) : Prop :=
  d.lifeLaidDownFormsBrotherLove = true ∧
  d.closedCompassionFailsLoveDwelling = true ∧
  d.loveInDeedAndTruth = true ∧
  d.godGreaterThanCondemningHeart = true ∧
  d.believeAndLoveCommandJoined = true ∧
  d.spiritGivenMarksAbiding = true

theorem first_john_future_likeness_purifies :
    futureLikenessPurifies sonshipPurity := by
  unfold futureLikenessPurifies sonshipPurity
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_cain_hate_counterproof :
    cainHateCounterproof cainBrotherTest := by
  unfold cainHateCounterproof cainBrotherTest
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_greater_than_heart :
    greaterThanHeartAssurance deedTruthAssurance := by
  unfold greaterThanHeartAssurance deedTruthAssurance
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_cain_deed_truth_witness :
    futureLikenessPurifies sonshipPurity ∧
    cainHateCounterproof cainBrotherTest ∧
    greaterThanHeartAssurance deedTruthAssurance := by
  exact ⟨first_john_future_likeness_purifies,
    first_john_cain_hate_counterproof,
    first_john_greater_than_heart⟩

end FirstJohnCainDeedTruthWitness
end Gnosis.Witnesses.Bible.FirstJohn
