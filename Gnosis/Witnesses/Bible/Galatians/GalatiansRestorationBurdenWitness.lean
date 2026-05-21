import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansRestorationBurdenWitness

/-!
# Galatians 6:1-6 -- Restoration, Burdens, and Self-Proof

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93940-93961`.

The Spirit-fruit ledger becomes a repair protocol: restore the overtaken one in
meekness, bear shared burdens, and still test one's own work. This keeps mercy
from collapsing into self-deception and keeps responsibility from becoming
isolation.

No `sorry`, no new `axiom`.
-/

structure MeekRestoration where
  overtakenFaultNamed : Bool := true
  spiritualRestore : Bool := true
  spiritOfMeekness : Bool := true
  selfConsiderationAgainstTemptation : Bool := true
deriving DecidableEq, Repr

def meekRestoration : MeekRestoration := {}

def restorationProtocol (r : MeekRestoration) : Prop :=
  r.overtakenFaultNamed = true ∧
  r.spiritualRestore = true ∧
  r.spiritOfMeekness = true ∧
  r.selfConsiderationAgainstTemptation = true

structure BurdenDiscipline where
  bearOneAnotherBurdens : Bool := true
  fulfillLawOfChrist : Bool := true
  selfDeceptionBySomethingnessRejected : Bool := true
  proveOwnWork : Bool := true
  ownBurdenStillBorne : Bool := true
  taughtCommunicatesGoodThings : Bool := true
deriving DecidableEq, Repr

def burdenDiscipline : BurdenDiscipline := {}

def burdenDisciplineWitness (b : BurdenDiscipline) : Prop :=
  b.bearOneAnotherBurdens = true ∧
  b.fulfillLawOfChrist = true ∧
  b.selfDeceptionBySomethingnessRejected = true ∧
  b.proveOwnWork = true ∧
  b.ownBurdenStillBorne = true ∧
  b.taughtCommunicatesGoodThings = true

theorem galatians_restoration_protocol :
    restorationProtocol meekRestoration := by
  unfold restorationProtocol meekRestoration
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_burden_discipline :
    burdenDisciplineWitness burdenDiscipline := by
  unfold burdenDisciplineWitness burdenDiscipline
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_restoration_burden_witness :
    restorationProtocol meekRestoration ∧
    burdenDisciplineWitness burdenDiscipline := by
  exact ⟨galatians_restoration_protocol,
    galatians_burden_discipline⟩

end GalatiansRestorationBurdenWitness
end Gnosis.Witnesses.Bible.Galatians
