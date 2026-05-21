namespace Gnosis.Witnesses.Bible.James
namespace JamesTongueWisdomWitness

/-!
# James 3 -- Tongue, Fire, and Wisdom From Above

Source slice: James 3:1-18.

Chapter invariant: speech is a steering organ. The tongue is small not because
speech is minor, but because small operators can govern whole systems: a bit
turns a horse, a helm turns a ship, and a mouth can set a life-course on fire.

Primary gap/counterproof: blessing God while cursing the divine likeness in
humans is not mixed spirituality; it is a corrupted fountain. James refuses the
fantasy that a person can speak poison and still claim an undefiled source.

Unseen sat: wisdom is known by its fruit texture. Earthly, sensual, devilish
wisdom generates envy, strife, confusion, and evil work; wisdom from above is
pure, peaceable, gentle, intreatable, merciful, fruitful, impartial, and without
hypocrisy.

No `sorry`, no new `axiom`.
-/

structure TongueSteering where
  teachersBearGreaterJudgment : Bool := true
  wordControlBridlesBody : Bool := true
  bitTurnsHorse : Bool := true
  helmTurnsShip : Bool := true
  smallTongueBoastsGreatMatter : Bool := true
deriving DecidableEq, Repr

def tongueSteering : TongueSteering := {}

def tongueSteeringWitness (t : TongueSteering) : Prop :=
  t.teachersBearGreaterJudgment = true ∧
  t.wordControlBridlesBody = true ∧
  t.bitTurnsHorse = true ∧
  t.helmTurnsShip = true ∧
  t.smallTongueBoastsGreatMatter = true

structure CorruptFountainCounterproof where
  tongueFireDefilesWholeBody : Bool := true
  humanTamingCannotTameTongue : Bool := true
  blessingAndCursingShouldNotShareMouth : Bool := true
  fountainCannotYieldSweetAndBitter : Bool := true
  figTreeCannotBearOlives : Bool := true
deriving DecidableEq, Repr

def corruptFountainCounterproof : CorruptFountainCounterproof := {}

def corruptFountainRejected (c : CorruptFountainCounterproof) : Prop :=
  c.tongueFireDefilesWholeBody = true ∧
  c.humanTamingCannotTameTongue = true ∧
  c.blessingAndCursingShouldNotShareMouth = true ∧
  c.fountainCannotYieldSweetAndBitter = true ∧
  c.figTreeCannotBearOlives = true

structure WisdomFromAbove where
  meekWorksShowWisdom : Bool := true
  bitterEnvyLiesAgainstTruth : Bool := true
  earthlyWisdomProducesConfusion : Bool := true
  aboveWisdomIsPurePeaceableGentle : Bool := true
  aboveWisdomIsMercifulFruitfulImpartial : Bool := true
  righteousnessFruitSownInPeace : Bool := true
deriving DecidableEq, Repr

def wisdomFromAbove : WisdomFromAbove := {}

def wisdomFromAboveWitness (w : WisdomFromAbove) : Prop :=
  w.meekWorksShowWisdom = true ∧
  w.bitterEnvyLiesAgainstTruth = true ∧
  w.earthlyWisdomProducesConfusion = true ∧
  w.aboveWisdomIsPurePeaceableGentle = true ∧
  w.aboveWisdomIsMercifulFruitfulImpartial = true ∧
  w.righteousnessFruitSownInPeace = true

theorem james_tongue_steering :
    tongueSteeringWitness tongueSteering := by
  unfold tongueSteeringWitness tongueSteering
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem james_corrupt_fountain_rejected :
    corruptFountainRejected corruptFountainCounterproof := by
  unfold corruptFountainRejected corruptFountainCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem james_wisdom_from_above :
    wisdomFromAboveWitness wisdomFromAbove := by
  unfold wisdomFromAboveWitness wisdomFromAbove
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem james_tongue_wisdom_witness :
    tongueSteeringWitness tongueSteering ∧
    corruptFountainRejected corruptFountainCounterproof ∧
    wisdomFromAboveWitness wisdomFromAbove := by
  exact ⟨james_tongue_steering,
    james_corrupt_fountain_rejected,
    james_wisdom_from_above⟩

end JamesTongueWisdomWitness
end Gnosis.Witnesses.Bible.James
