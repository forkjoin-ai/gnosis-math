import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansAbrahamFaithBlessingWitness

/-!
# Galatians 3:6-9 -- Abraham Faith and Nations Blessing

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93720-93733`.

The chapter reads Abraham as a faith-indexed witness before it reads him as an
ethnic boundary. The unseen sat is the earlier invariant: trust is counted before
lineage policing, so the blessing can propagate to the nations without rerouting
through circumcision capture.

No `sorry`, no new `axiom`.
-/

structure AbrahamFaithAccounting where
  abrahamBelievedGod : Bool := true
  beliefAccountedForRighteousness : Bool := true
  faithChildrenRecognized : Bool := true
deriving DecidableEq, Repr

def abrahamFaithAccounting : AbrahamFaithAccounting := {}

def faithAccountingWitness (a : AbrahamFaithAccounting) : Prop :=
  a.abrahamBelievedGod = true ∧
  a.beliefAccountedForRighteousness = true ∧
  a.faithChildrenRecognized = true

structure NationsBlessingSignal where
  scriptureForesawGentileJustification : Bool := true
  gospelPreachedBeforeToAbraham : Bool := true
  allNationsBlessedInAbraham : Bool := true
  faithBlessedWithFaithfulAbraham : Bool := true
deriving DecidableEq, Repr

def nationsBlessingSignal : NationsBlessingSignal := {}

def nationsBlessedByFaith (n : NationsBlessingSignal) : Prop :=
  n.scriptureForesawGentileJustification = true ∧
  n.gospelPreachedBeforeToAbraham = true ∧
  n.allNationsBlessedInAbraham = true ∧
  n.faithBlessedWithFaithfulAbraham = true

theorem galatians_abraham_faith_accounting :
    faithAccountingWitness abrahamFaithAccounting := by
  unfold faithAccountingWitness abrahamFaithAccounting
  exact ⟨rfl, rfl, rfl⟩

theorem galatians_nations_blessed_by_faith :
    nationsBlessedByFaith nationsBlessingSignal := by
  unfold nationsBlessedByFaith nationsBlessingSignal
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_abraham_faith_blessing_witness :
    faithAccountingWitness abrahamFaithAccounting ∧
    nationsBlessedByFaith nationsBlessingSignal := by
  exact ⟨galatians_abraham_faith_accounting,
    galatians_nations_blessed_by_faith⟩

end GalatiansAbrahamFaithBlessingWitness
end Gnosis.Witnesses.Bible.Galatians
