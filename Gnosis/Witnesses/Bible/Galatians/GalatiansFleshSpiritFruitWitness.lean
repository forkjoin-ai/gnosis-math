import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansFleshSpiritFruitWitness

/-!
# Galatians 5:16-26 -- Flesh Works, Spirit Fruit, and Crucified Desire

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93911-93939`.

The chapter's final ledger is sharply diagnostic: flesh has manifest works and
inheritance failure; Spirit has fruit and no law against it. The contrarian
signal is that fruit, not boundary-marking, becomes the visible proof surface.

No `sorry`, no new `axiom`.
-/

structure SpiritFleshConflict where
  walkInSpiritCommanded : Bool := true
  fleshLustNotFulfilled : Bool := true
  fleshAgainstSpirit : Bool := true
  spiritAgainstFlesh : Bool := true
  contrarietyBlocksWill : Bool := true
  spiritLedNotUnderLaw : Bool := true
deriving DecidableEq, Repr

def spiritFleshConflict : SpiritFleshConflict := {}

def spiritFleshBoundary (s : SpiritFleshConflict) : Prop :=
  s.walkInSpiritCommanded = true ∧
  s.fleshLustNotFulfilled = true ∧
  s.fleshAgainstSpirit = true ∧
  s.spiritAgainstFlesh = true ∧
  s.contrarietyBlocksWill = true ∧
  s.spiritLedNotUnderLaw = true

structure FleshWorksLedger where
  worksOfFleshManifest : Bool := true
  impurityAndIdolatryNamed : Bool := true
  socialStrifeNamed : Bool := true
  excessAndSuchLikeNamed : Bool := true
  fleshWorkersDoNotInheritKingdom : Bool := true
deriving DecidableEq, Repr

def fleshWorksLedger : FleshWorksLedger := {}

def fleshWorksInheritanceFailure (f : FleshWorksLedger) : Prop :=
  f.worksOfFleshManifest = true ∧
  f.impurityAndIdolatryNamed = true ∧
  f.socialStrifeNamed = true ∧
  f.excessAndSuchLikeNamed = true ∧
  f.fleshWorkersDoNotInheritKingdom = true

structure SpiritFruitLedger where
  loveJoyPeace : Bool := true
  longsufferingGentlenessGoodnessFaith : Bool := true
  meeknessTemperance : Bool := true
  againstSuchNoLaw : Bool := true
  christFleshCrucifiedWithAffections : Bool := true
  liveAndWalkInSpirit : Bool := true
  vainGloryProvocationEnvyRejected : Bool := true
deriving DecidableEq, Repr

def spiritFruitLedger : SpiritFruitLedger := {}

def spiritFruitProofSurface (f : SpiritFruitLedger) : Prop :=
  f.loveJoyPeace = true ∧
  f.longsufferingGentlenessGoodnessFaith = true ∧
  f.meeknessTemperance = true ∧
  f.againstSuchNoLaw = true ∧
  f.christFleshCrucifiedWithAffections = true ∧
  f.liveAndWalkInSpirit = true ∧
  f.vainGloryProvocationEnvyRejected = true

theorem galatians_spirit_flesh_boundary :
    spiritFleshBoundary spiritFleshConflict := by
  unfold spiritFleshBoundary spiritFleshConflict
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_flesh_works_inheritance_failure :
    fleshWorksInheritanceFailure fleshWorksLedger := by
  unfold fleshWorksInheritanceFailure fleshWorksLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_spirit_fruit_proof_surface :
    spiritFruitProofSurface spiritFruitLedger := by
  unfold spiritFruitProofSurface spiritFruitLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_flesh_spirit_fruit_witness :
    spiritFleshBoundary spiritFleshConflict ∧
    fleshWorksInheritanceFailure fleshWorksLedger ∧
    spiritFruitProofSurface spiritFruitLedger := by
  exact ⟨galatians_spirit_flesh_boundary,
    galatians_flesh_works_inheritance_failure,
    galatians_spirit_fruit_proof_surface⟩

end GalatiansFleshSpiritFruitWitness
end Gnosis.Witnesses.Bible.Galatians
