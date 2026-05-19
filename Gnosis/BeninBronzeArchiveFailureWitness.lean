import Init

/-
  BeninBronzeArchiveFailureWitness.lean
  =====================================

  Benin Bronzes / Edo court art as archive-failure witness: a machine or
  institution can preserve an object while destroying the living coordinates
  that made the object intelligible.

  Cultural floor: the court works associated with the Kingdom of Benin are not
  treated here as generic "museum objects." This file uses them as an operator
  warning: extraction into an archive may preserve metal, image, and inventory
  number while severing palace, ritual, lineage, diplomatic, and craft context.

  Formal reading in this repository:

  * archive failure maps to `archivePreservesWithoutUnderstanding`.
  * extraction maps to `objectSurvivesContextSevered`.
  * repair is not mere storage; it requires `contextRestorationRequiresRelation`.

  This file does not prove restitution policy and does not summarize Benin
  history. It names the categorical failure: preservation without relation is
  not understanding.

  Repo cousins: `BorgesOnExactitudeInScienceWitness` (map pathology);
  `MagritteTreacheryOfImagesWitness` (sign vs referent); `DaguerrePhotographyNoFreeCopyWitness`
  (record persistence and deletion liability); `DuchampRetinalTrapWitness`
  (institutional status bit); `ColonialCensusCompressionWitness` (administrative
  capture by category).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace BeninBronzeArchiveFailureWitness

/-- Tag: archive preserves the object but not the understanding relation. -/
abbrev archivePreservesWithoutUnderstanding (claim : Prop) : Prop :=
  claim

/-- Tag: the material object survives while ritual / political / kin context is severed. -/
abbrev objectSurvivesContextSevered (claim : Prop) : Prop :=
  claim

/-- Tag: repair requires relation, not just inventory stability. -/
abbrev contextRestorationRequiresRelation (claim : Prop) : Prop :=
  claim

/--
  Archive failure bundle: preserved object + severed context + relational repair.
-/
structure ArchiveFailureWitness (archive severance repair : Prop) where
  preservedWithoutKnowing : archivePreservesWithoutUnderstanding archive
  contextCut : objectSurvivesContextSevered severance
  repairIsRelational : contextRestorationRequiresRelation repair

theorem archive_failure_conjuncts
    (A S R : Prop) (w : ArchiveFailureWitness A S R) : A ∧ S ∧ R :=
  And.intro w.preservedWithoutKnowing (And.intro w.contextCut w.repairIsRelational)

def buildArchiveFailureWitness
    (A S R : Prop) (hA : A) (hS : S) (hR : R) : ArchiveFailureWitness A S R :=
  ⟨hA, hS, hR⟩

end BeninBronzeArchiveFailureWitness
