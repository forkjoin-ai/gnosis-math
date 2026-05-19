import Init

/-
  ThreeGorgesScaleMismatchWitness.lean
  ====================================

  Three Gorges / megaproject displacement as scale-mismatch witness: a system
  can be locally engineered and still break human-scale meaning.

  Cultural floor: the anchor is large infrastructure whose benefits, risks,
  displacement, landscape change, and memory costs live at different scales.
  The category is not "engineering bad." It is the failure mode where no single
  local ledger entry can carry the moral geometry of river, town, ancestor,
  energy, flood control, relocation, and downstream ecology.

  Formal reading in this repository:

  * scale mismatch maps to `scaleBreaksMoralIntuition`.
  * infrastructure ledgering maps to `localBenefitCannotCloseGlobalCost`.
  * displacement maps to `placeMemorySubmergedByProject`.

  This file does not prove a civil-engineering verdict. It names the categorical
  failure: the project scale can exceed the moral resolution of its interface.

  Repo cousins: `BorgesOnExactitudeInScienceWitness` (map scale pathology);
  `TopologicalCinema` (framed perception); `Civil/*` modules (engineering
  formulas without this moral ledger); `AttilaGrassNeverGrowsWitness`
  (irreversible trace).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace ThreeGorgesScaleMismatchWitness

/-- Tag: project scale breaks ordinary moral intuition. -/
abbrev scaleBreaksMoralIntuition (claim : Prop) : Prop :=
  claim

/-- Tag: local benefits do not close the global cost ledger. -/
abbrev localBenefitCannotCloseGlobalCost (claim : Prop) : Prop :=
  claim

/-- Tag: place-memory is submerged or displaced by project scale. -/
abbrev placeMemorySubmergedByProject (claim : Prop) : Prop :=
  claim

/--
  Scale mismatch bundle: scale break + ledger mismatch + place-memory loss.
-/
structure ScaleMismatchWitness (scale ledger memory : Prop) where
  intuitionBreak : scaleBreaksMoralIntuition scale
  ledgerOpen : localBenefitCannotCloseGlobalCost ledger
  memoryDisplaced : placeMemorySubmergedByProject memory

theorem scale_mismatch_conjuncts
    (S L M : Prop) (w : ScaleMismatchWitness S L M) : S ∧ L ∧ M :=
  And.intro w.intuitionBreak (And.intro w.ledgerOpen w.memoryDisplaced)

def buildScaleMismatchWitness
    (S L M : Prop) (hS : S) (hL : L) (hM : M) : ScaleMismatchWitness S L M :=
  ⟨hS, hL, hM⟩

end ThreeGorgesScaleMismatchWitness
