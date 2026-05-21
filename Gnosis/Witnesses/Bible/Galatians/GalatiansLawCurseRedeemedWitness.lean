import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansLawCurseRedeemedWitness

/-!
# Galatians 3:10-14 -- Law Curse, Tree Curse, and Redeemed Promise

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93734-93750`.

This is an antitheorem against law as life-giving closure. The law ledger
contains a total-continuance requirement; failure turns the ledger into curse.
Galatians then routes the curse through the tree and reopens the Abrahamic
blessing and Spirit promise by faith.

No `sorry`, no new `axiom`.
-/

structure LawCurseBoundary where
  worksOfLawUnderCurse : Bool := true
  continuanceRequirementNamed : Bool := true
  noManJustifiedByLaw : Bool := true
  justLiveByFaith : Bool := true
  lawNotOfFaith : Bool := true
deriving DecidableEq, Repr

def lawCurseBoundary : LawCurseBoundary := {}

def lawAsCurseBoundary (b : LawCurseBoundary) : Prop :=
  b.worksOfLawUnderCurse = true ∧
  b.continuanceRequirementNamed = true ∧
  b.noManJustifiedByLaw = true ∧
  b.justLiveByFaith = true ∧
  b.lawNotOfFaith = true

structure RedeemedFromCurse where
  christRedeemedFromLawCurse : Bool := true
  madeCurseForUs : Bool := true
  treeCurseCited : Bool := true
  abrahamBlessingToGentiles : Bool := true
  spiritPromiseReceivedThroughFaith : Bool := true
deriving DecidableEq, Repr

def redeemedFromCurse : RedeemedFromCurse := {}

def curseReroutedToPromise (r : RedeemedFromCurse) : Prop :=
  r.christRedeemedFromLawCurse = true ∧
  r.madeCurseForUs = true ∧
  r.treeCurseCited = true ∧
  r.abrahamBlessingToGentiles = true ∧
  r.spiritPromiseReceivedThroughFaith = true

theorem galatians_law_as_curse_boundary :
    lawAsCurseBoundary lawCurseBoundary := by
  unfold lawAsCurseBoundary lawCurseBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_curse_rerouted_to_promise :
    curseReroutedToPromise redeemedFromCurse := by
  unfold curseReroutedToPromise redeemedFromCurse
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_law_curse_redeemed_witness :
    lawAsCurseBoundary lawCurseBoundary ∧
    curseReroutedToPromise redeemedFromCurse := by
  exact ⟨galatians_law_as_curse_boundary,
    galatians_curse_rerouted_to_promise⟩

end GalatiansLawCurseRedeemedWitness
end Gnosis.Witnesses.Bible.Galatians
