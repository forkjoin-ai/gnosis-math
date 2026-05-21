import Init

namespace Gnosis.Witnesses.Bible.SecondThessalonians
namespace SecondThessaloniansTruthTraditionComfortWitness

/-!
# 2 Thessalonians 2:13-17 -- Chosen Through Truth, Stand Fast, Comforted Work

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95208-95223`.

After the delusion warning, the positive stabilizer is truth-belief through
Spirit sanctification. Tradition is not nostalgia here; it is anti-shake memory
anchored by word and epistle, comfort, and good work.

No `sorry`, no new `axiom`.
-/

structure TruthChosenCalling where
  thanksForBeloved : Bool := true
  chosenFromBeginningToSalvation : Bool := true
  sanctificationOfSpirit : Bool := true
  beliefOfTruth : Bool := true
  calledByGospel : Bool := true
  obtainsGloryOfChrist : Bool := true
deriving DecidableEq, Repr

def truthChosenCalling : TruthChosenCalling := {}

def truthChosenWitness (t : TruthChosenCalling) : Prop :=
  t.thanksForBeloved = true ∧
  t.chosenFromBeginningToSalvation = true ∧
  t.sanctificationOfSpirit = true ∧
  t.beliefOfTruth = true ∧
  t.calledByGospel = true ∧
  t.obtainsGloryOfChrist = true

structure TraditionComfort where
  standFast : Bool := true
  traditionsHeldByWordEpistle : Bool := true
  lovedAndEverlastingConsolation : Bool := true
  goodHopeThroughGrace : Bool := true
  heartsComforted : Bool := true
  establishedInGoodWordWork : Bool := true
deriving DecidableEq, Repr

def traditionComfort : TraditionComfort := {}

def traditionComfortWitness (c : TraditionComfort) : Prop :=
  c.standFast = true ∧
  c.traditionsHeldByWordEpistle = true ∧
  c.lovedAndEverlastingConsolation = true ∧
  c.goodHopeThroughGrace = true ∧
  c.heartsComforted = true ∧
  c.establishedInGoodWordWork = true

theorem second_thessalonians_truth_chosen :
    truthChosenWitness truthChosenCalling := by
  unfold truthChosenWitness truthChosenCalling
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_thessalonians_tradition_comfort :
    traditionComfortWitness traditionComfort := by
  unfold traditionComfortWitness traditionComfort
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_thessalonians_truth_tradition_comfort_witness :
    truthChosenWitness truthChosenCalling ∧
    traditionComfortWitness traditionComfort := by
  exact ⟨second_thessalonians_truth_chosen,
    second_thessalonians_tradition_comfort⟩

end SecondThessaloniansTruthTraditionComfortWitness
end Gnosis.Witnesses.Bible.SecondThessalonians
