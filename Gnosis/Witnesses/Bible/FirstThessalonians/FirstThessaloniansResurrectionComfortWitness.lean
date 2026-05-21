import Init

namespace Gnosis.Witnesses.Bible.FirstThessalonians
namespace FirstThessaloniansResurrectionComfortWitness

/-!
# 1 Thessalonians 4:13-18 -- Sleep, Resurrection, Coming, and Comfort

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95072-95095`.

The resurrection witness blocks hopeless sorrow. Those asleep are not bypassed:
the dead in Christ rise first, the living are caught up together, and the final
instruction is mutual comfort.

No `sorry`, no new `axiom`.
-/

structure ResurrectionComfort where
  notIgnorantConcerningAsleep : Bool := true
  sorrowNotAsNoHope : Bool := true
  jesusDiedAndRose : Bool := true
  sleepingBroughtWithJesus : Bool := true
  livingDoNotPreventAsleep : Bool := true
  lordDescendsWithShoutTrump : Bool := true
  deadInChristRiseFirst : Bool := true
  caughtUpTogetherEverWithLord : Bool := true
  comfortOneAnotherWords : Bool := true
deriving DecidableEq, Repr

def resurrectionComfort : ResurrectionComfort := {}

def resurrectionComfortWitness (r : ResurrectionComfort) : Prop :=
  r.notIgnorantConcerningAsleep = true ∧ r.sorrowNotAsNoHope = true ∧
  r.jesusDiedAndRose = true ∧ r.sleepingBroughtWithJesus = true ∧
  r.livingDoNotPreventAsleep = true ∧ r.lordDescendsWithShoutTrump = true ∧
  r.deadInChristRiseFirst = true ∧ r.caughtUpTogetherEverWithLord = true ∧
  r.comfortOneAnotherWords = true

theorem first_thessalonians_resurrection_comfort :
    resurrectionComfortWitness resurrectionComfort := by
  unfold resurrectionComfortWitness resurrectionComfort
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstThessaloniansResurrectionComfortWitness
end Gnosis.Witnesses.Bible.FirstThessalonians
