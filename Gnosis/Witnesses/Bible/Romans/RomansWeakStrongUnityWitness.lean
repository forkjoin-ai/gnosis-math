namespace Gnosis.Witnesses.Bible.Romans
namespace RomansWeakStrongUnityWitness

/-!
# Romans 14-15 -- Weak, Strong, Edification, Gentile Praise, and Mission Debt

Source slice: Romans 14:1-15:33.

Invariant: liberty is load-bearing restraint. Food and days are not allowed to
become contempt engines. The strong do not get to turn correctness into damage;
the weak do not get to turn scruple into jurisdiction over another servant.

Unseen sat: the good can be spoken evil of when it is performed without love.
The kingdom is not meat and drink; it is righteousness, peace, and joy. Paul
then scales the same rule outward: receive one another, let scriptures produce
hope, let Gentile praise confirm mercy, and make material contribution answer
spiritual participation.

No `sorry`, no new `axiom`.
-/

structure WeakStrongConscience where
  weakReceivedWithoutDisputes : Bool := true
  eatingDespisingAndJudgingRejected : Bool := true
  dayDifferenceKeptUntoLord : Bool := true
  noneLivesOrDiesToSelf : Bool := true
  judgmentSeatEqualizesAccounts : Bool := true
  libertyCannotSetStumblingblock : Bool := true
  meatCannotDestroyGodsWork : Bool := true
  faithMustNotViolateConscience : Bool := true
deriving DecidableEq, Repr

def weakStrongConscience : WeakStrongConscience := {}

def libertyBearsTheWeak (w : WeakStrongConscience) : Prop :=
  w.weakReceivedWithoutDisputes = true ∧
  w.eatingDespisingAndJudgingRejected = true ∧
  w.dayDifferenceKeptUntoLord = true ∧
  w.noneLivesOrDiesToSelf = true ∧
  w.judgmentSeatEqualizesAccounts = true ∧
  w.libertyCannotSetStumblingblock = true ∧
  w.meatCannotDestroyGodsWork = true ∧
  w.faithMustNotViolateConscience = true

structure UnityMissionHope where
  strongBearWeakInfirmities : Bool := true
  christPleasedNotHimself : Bool := true
  scripturesWrittenForHope : Bool := true
  receiveOneAnotherAsChristReceived : Bool := true
  gentilePraiseConfirmsMercy : Bool := true
  ministeringGentilesAsOffering : Bool := true
  notBuildingOnAnotherFoundation : Bool := true
  materialContributionSealsFruit : Bool := true
  prayersStriveForAcceptedService : Bool := true
deriving DecidableEq, Repr

def unityMissionHope : UnityMissionHope := {}

def missionScalesEdification (u : UnityMissionHope) : Prop :=
  u.strongBearWeakInfirmities = true ∧
  u.christPleasedNotHimself = true ∧
  u.scripturesWrittenForHope = true ∧
  u.receiveOneAnotherAsChristReceived = true ∧
  u.gentilePraiseConfirmsMercy = true ∧
  u.ministeringGentilesAsOffering = true ∧
  u.notBuildingOnAnotherFoundation = true ∧
  u.materialContributionSealsFruit = true ∧
  u.prayersStriveForAcceptedService = true

theorem romans_liberty_bears_the_weak :
    libertyBearsTheWeak weakStrongConscience := by
  unfold libertyBearsTheWeak weakStrongConscience
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem romans_mission_scales_edification :
    missionScalesEdification unityMissionHope := by
  unfold missionScalesEdification unityMissionHope
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem romans_weak_strong_unity_witness :
    libertyBearsTheWeak weakStrongConscience ∧
    missionScalesEdification unityMissionHope := by
  exact ⟨romans_liberty_bears_the_weak,
    romans_mission_scales_edification⟩

end RomansWeakStrongUnityWitness
end Gnosis.Witnesses.Bible.Romans
