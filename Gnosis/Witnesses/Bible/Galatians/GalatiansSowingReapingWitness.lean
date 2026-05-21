import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansSowingReapingWitness

/-!
# Galatians 6:7-10 -- Sowing, Reaping, and Non-Weary Good

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93962-93976`.

The witness is a delayed-yield ledger. Flesh sowing reaps corruption; Spirit
sowing reaps life. The practical output is perseverance in good while the
seasonal delay remains unresolved.

No `sorry`, no new `axiom`.
-/

structure SowingLedger where
  godNotMocked : Bool := true
  whatManSowsHeReaps : Bool := true
  fleshSowingReapsCorruption : Bool := true
  spiritSowingReapsLifeEverlasting : Bool := true
deriving DecidableEq, Repr

def sowingLedger : SowingLedger := {}

def sowingReapingBoundary (s : SowingLedger) : Prop :=
  s.godNotMocked = true ∧
  s.whatManSowsHeReaps = true ∧
  s.fleshSowingReapsCorruption = true ∧
  s.spiritSowingReapsLifeEverlasting = true

structure PerseveringGood where
  notWearyInWellDoing : Bool := true
  dueSeasonReap : Bool := true
  faintNotCondition : Bool := true
  opportunityDoGoodToAll : Bool := true
  householdOfFaithEspecially : Bool := true
deriving DecidableEq, Repr

def perseveringGood : PerseveringGood := {}

def perseveranceWitness (p : PerseveringGood) : Prop :=
  p.notWearyInWellDoing = true ∧
  p.dueSeasonReap = true ∧
  p.faintNotCondition = true ∧
  p.opportunityDoGoodToAll = true ∧
  p.householdOfFaithEspecially = true

theorem galatians_sowing_reaping_boundary :
    sowingReapingBoundary sowingLedger := by
  unfold sowingReapingBoundary sowingLedger
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_perseverance_witness :
    perseveranceWitness perseveringGood := by
  unfold perseveranceWitness perseveringGood
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_sowing_reaping_witness :
    sowingReapingBoundary sowingLedger ∧
    perseveranceWitness perseveringGood := by
  exact ⟨galatians_sowing_reaping_boundary,
    galatians_perseverance_witness⟩

end GalatiansSowingReapingWitness
end Gnosis.Witnesses.Bible.Galatians
