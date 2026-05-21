import Init

namespace Gnosis.Witnesses.Bible.Torah
namespace DeuteronomyLawCurseTreeWitness

/-!
# Leviticus 18 and Deuteronomy 21, 27 -- Do-and-Live, Law Curse, Tree Curse

Source text:
- `docs/ebooks/source-texts/bible-kjv.txt:10595-10618`
- `docs/ebooks/source-texts/bible-kjv.txt:17660-17678`
- `docs/ebooks/source-texts/bible-kjv.txt:18138-18148`

This Torah witness preserves the source-side law ledger: doing the judgments as
life, the curse for not confirming all words of the law, and the hanged-on-tree
curse. Galatians owns the later apostolic rerouting of these anchors.

No `sorry`, no new `axiom`.
-/

structure DoAndLiveLedger where
  judgmentsAndOrdinancesToKeep : Bool := true
  walkThereinCommanded : Bool := true
  manDoingThemLivesInThem : Bool := true
deriving DecidableEq, Repr

def doAndLiveLedger : DoAndLiveLedger := {}

def doAndLiveAnchor (d : DoAndLiveLedger) : Prop :=
  d.judgmentsAndOrdinancesToKeep = true ∧
  d.walkThereinCommanded = true ∧
  d.manDoingThemLivesInThem = true

structure CurseLedger where
  hangedOnTreeNamed : Bool := true
  hangedAccursedOfGod : Bool := true
  bodyNotRemainAllNight : Bool := true
  landDefilementGuarded : Bool := true
  notConfirmingAllLawWordsCursed : Bool := true
  allPeopleAmen : Bool := true
deriving DecidableEq, Repr

def curseLedger : CurseLedger := {}

def curseLedgerAnchor (c : CurseLedger) : Prop :=
  c.hangedOnTreeNamed = true ∧
  c.hangedAccursedOfGod = true ∧
  c.bodyNotRemainAllNight = true ∧
  c.landDefilementGuarded = true ∧
  c.notConfirmingAllLawWordsCursed = true ∧
  c.allPeopleAmen = true

theorem torah_do_and_live_anchor :
    doAndLiveAnchor doAndLiveLedger := by
  unfold doAndLiveAnchor doAndLiveLedger
  exact ⟨rfl, rfl, rfl⟩

theorem torah_curse_ledger_anchor :
    curseLedgerAnchor curseLedger := by
  unfold curseLedgerAnchor curseLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem deuteronomy_law_curse_tree_witness :
    doAndLiveAnchor doAndLiveLedger ∧
    curseLedgerAnchor curseLedger := by
  exact ⟨torah_do_and_live_anchor,
    torah_curse_ledger_anchor⟩

end DeuteronomyLawCurseTreeWitness
end Gnosis.Witnesses.Bible.Torah
