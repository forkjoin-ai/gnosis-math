import Init

namespace Gnosis.Witnesses.Bible.Torah
namespace GenesisHagarSarahPromiseWitness

/-!
# Genesis 16 and 21 -- Hagar, Sarah, Ishmael, and Isaac Heir Boundary

Source text:
- `docs/ebooks/source-texts/bible-kjv.txt:1199-1250`
- `docs/ebooks/source-texts/bible-kjv.txt:1644-1668`

This Torah witness owns the source-side Hagar/Sarah and Ishmael/Isaac material
that Galatians 4 later projects into its bondwoman/freewoman topology.

No `sorry`, no new `axiom`.
-/

structure HagarIshmaelSource where
  saraiHadEgyptianHandmaidHagar : Bool := true
  hagarConceivedByAbram : Bool := true
  householdConflictRecorded : Bool := true
  angelFoundHagarInWilderness : Bool := true
  ishmaelNamedBecauseAfflictionHeard : Bool := true
  hagarBoreIshmaelToAbram : Bool := true
deriving DecidableEq, Repr

def hagarIshmaelSource : HagarIshmaelSource := {}

def hagarIshmaelAnchor (h : HagarIshmaelSource) : Prop :=
  h.saraiHadEgyptianHandmaidHagar = true ∧
  h.hagarConceivedByAbram = true ∧
  h.householdConflictRecorded = true ∧
  h.angelFoundHagarInWilderness = true ∧
  h.ishmaelNamedBecauseAfflictionHeard = true ∧
  h.hagarBoreIshmaelToAbram = true

structure IsaacHeirBoundary where
  sarahSawHagarSonMocking : Bool := true
  castOutBondwomanAndSon : Bool := true
  bondwomanSonNotHeirWithIsaac : Bool := true
  commandGrievedAbraham : Bool := true
  inIsaacSeedCalled : Bool := true
  bondwomanSonAlsoNationBecauseSeed : Bool := true
deriving DecidableEq, Repr

def isaacHeirBoundary : IsaacHeirBoundary := {}

def isaacHeirAnchor (i : IsaacHeirBoundary) : Prop :=
  i.sarahSawHagarSonMocking = true ∧
  i.castOutBondwomanAndSon = true ∧
  i.bondwomanSonNotHeirWithIsaac = true ∧
  i.commandGrievedAbraham = true ∧
  i.inIsaacSeedCalled = true ∧
  i.bondwomanSonAlsoNationBecauseSeed = true

theorem genesis_hagar_ishmael_anchor :
    hagarIshmaelAnchor hagarIshmaelSource := by
  unfold hagarIshmaelAnchor hagarIshmaelSource
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem genesis_isaac_heir_anchor :
    isaacHeirAnchor isaacHeirBoundary := by
  unfold isaacHeirAnchor isaacHeirBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem genesis_hagar_sarah_promise_witness :
    hagarIshmaelAnchor hagarIshmaelSource ∧
    isaacHeirAnchor isaacHeirBoundary := by
  exact ⟨genesis_hagar_ishmael_anchor,
    genesis_isaac_heir_anchor⟩

end GenesisHagarSarahPromiseWitness
end Gnosis.Witnesses.Bible.Torah
