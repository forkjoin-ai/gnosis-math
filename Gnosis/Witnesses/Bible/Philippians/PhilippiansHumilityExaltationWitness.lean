import Init

namespace Gnosis.Witnesses.Bible.Philippians
namespace PhilippiansHumilityExaltationWitness

/-!
# Philippians 2:1-11 -- One-Minded Humility and Exalted Name

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94444-94476`.

The Christ hymn is a descent-ascent topology: no vainglory, form of servant,
obedience to cross, then name above every name and cosmic confession.

No `sorry`, no new `axiom`.
-/

structure OneMindedHumility where
  consolationLoveSpiritMercies : Bool := true
  sameLoveOneAccordMind : Bool := true
  strifeVaingloryRejected : Bool := true
  othersEsteemedBetter : Bool := true
  othersThingsRegarded : Bool := true
deriving DecidableEq, Repr

def oneMindedHumility : OneMindedHumility := {}

def humilityWitness (h : OneMindedHumility) : Prop :=
  h.consolationLoveSpiritMercies = true ∧ h.sameLoveOneAccordMind = true ∧
  h.strifeVaingloryRejected = true ∧ h.othersEsteemedBetter = true ∧
  h.othersThingsRegarded = true

structure DescentExaltation where
  mindOfChristCommanded : Bool := true
  formOfGodNoRobbery : Bool := true
  madeNoReputationServant : Bool := true
  likenessOfMen : Bool := true
  humbledToCrossDeath : Bool := true
  highlyExaltedNameAboveEveryName : Bool := true
  everyKneeBows : Bool := true
  everyTongueConfessesLord : Bool := true
deriving DecidableEq, Repr

def descentExaltation : DescentExaltation := {}

def descentExaltationWitness (d : DescentExaltation) : Prop :=
  d.mindOfChristCommanded = true ∧ d.formOfGodNoRobbery = true ∧
  d.madeNoReputationServant = true ∧ d.likenessOfMen = true ∧
  d.humbledToCrossDeath = true ∧ d.highlyExaltedNameAboveEveryName = true ∧
  d.everyKneeBows = true ∧ d.everyTongueConfessesLord = true

theorem philippians_humility :
    humilityWitness oneMindedHumility := by
  unfold humilityWitness oneMindedHumility
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_descent_exaltation :
    descentExaltationWitness descentExaltation := by
  unfold descentExaltationWitness descentExaltation
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_humility_exaltation_witness :
    humilityWitness oneMindedHumility ∧ descentExaltationWitness descentExaltation := by
  exact ⟨philippians_humility, philippians_descent_exaltation⟩

end PhilippiansHumilityExaltationWitness
end Gnosis.Witnesses.Bible.Philippians
