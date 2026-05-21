import Init

namespace Gnosis.Witnesses.Bible.Philippians
namespace PhilippiansLifeDeathConductWitness

/-!
# Philippians 1:19-30 -- Life, Death, Gospel Conduct, and Shared Suffering

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94410-94443`.

The life/death strait is resolved by gospel usefulness: to live is Christ, to die
gain, but abiding serves their joy of faith. The community proof is fearless,
one-spirit striving under shared conflict.

No `sorry`, no new `axiom`.
-/

structure LifeDeathStrait where
  prayerAndSpiritSupply : Bool := true
  christMagnifiedInBody : Bool := true
  lifeIsChrist : Bool := true
  deathIsGain : Bool := true
  departWithChristFarBetter : Bool := true
  abideNeedfulForOthers : Bool := true
  furtheranceJoyOfFaith : Bool := true
deriving DecidableEq, Repr

def lifeDeathStrait : LifeDeathStrait := {}

def lifeDeathWitness (l : LifeDeathStrait) : Prop :=
  l.prayerAndSpiritSupply = true ∧ l.christMagnifiedInBody = true ∧
  l.lifeIsChrist = true ∧ l.deathIsGain = true ∧ l.departWithChristFarBetter = true ∧
  l.abideNeedfulForOthers = true ∧ l.furtheranceJoyOfFaith = true

structure GospelConductConflict where
  conversationBecomesGospel : Bool := true
  standFastOneSpirit : Bool := true
  oneMindStrivingForFaith : Bool := true
  adversariesNotTerrifying : Bool := true
  salvationTokenFromGod : Bool := true
  beliefAndSufferingGiven : Bool := true
  sameConflictShared : Bool := true
deriving DecidableEq, Repr

def gospelConductConflict : GospelConductConflict := {}

def gospelConductWitness (g : GospelConductConflict) : Prop :=
  g.conversationBecomesGospel = true ∧ g.standFastOneSpirit = true ∧
  g.oneMindStrivingForFaith = true ∧ g.adversariesNotTerrifying = true ∧
  g.salvationTokenFromGod = true ∧ g.beliefAndSufferingGiven = true ∧
  g.sameConflictShared = true

theorem philippians_life_death :
    lifeDeathWitness lifeDeathStrait := by
  unfold lifeDeathWitness lifeDeathStrait
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_gospel_conduct :
    gospelConductWitness gospelConductConflict := by
  unfold gospelConductWitness gospelConductConflict
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_life_death_conduct_witness :
    lifeDeathWitness lifeDeathStrait ∧ gospelConductWitness gospelConductConflict := by
  exact ⟨philippians_life_death, philippians_gospel_conduct⟩

end PhilippiansLifeDeathConductWitness
end Gnosis.Witnesses.Bible.Philippians
