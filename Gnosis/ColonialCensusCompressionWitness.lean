/-
  ColonialCensusCompressionWitness.lean
  =====================================

  Colonial census / administrative classification as compression-failure witness:
  a living person, community, practice, or relation is forced into a state-readable
  cell, and the cell is then mistaken for the life.

  Cultural floor: the anchor here is not one empire's paperwork only. The failure
  appears wherever census, caste/race category, pass, registry, or identity table
  becomes the operational truth that people must fit. The machine keeps the
  summary and loses the witness.

  Formal reading in this repository:

  * compression failure maps to `summaryErasesWitness`.
  * calibration failure maps to `measurementReplacesPhenomenon`.
  * administrative violence maps to `categoryBecomesOperationalReality`.

  This file does not prove a historical theory of colonialism. It names the
  categorical machine failure: a lossy category becomes a governing ontology.

  Repo cousins: `BorgesOnExactitudeInScienceWitness` (map/model pathology);
  `OrwellNineteenEightyFourWitness` (political fact speech); `ProtagorasManIsMeasureWitness`
  (measure as epistemic hazard); `BeninBronzeArchiveFailureWitness` (archive
  without context); `BaudrillardSimulacraSimulationWitness` (sign regime leading
  practice).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace ColonialCensusCompressionWitness

/-- Tag: summary / category erases the living witness residual. -/
abbrev summaryErasesWitness (claim : Prop) : Prop :=
  claim

/-- Tag: the measurement instrument's scale replaces the phenomenon. -/
abbrev measurementReplacesPhenomenon (claim : Prop) : Prop :=
  claim

/-- Tag: administrative category becomes operational reality. -/
abbrev categoryBecomesOperationalReality (claim : Prop) : Prop :=
  claim

/--
  Census compression bundle: lossy summary + measurement ontology +
  category governance.
-/
structure CensusCompressionWitness (summary measure category : Prop) where
  residualLost : summaryErasesWitness summary
  scaleOntology : measurementReplacesPhenomenon measure
  categoryRules : categoryBecomesOperationalReality category

theorem census_compression_conjuncts
    (S M C : Prop) (w : CensusCompressionWitness S M C) : S ∧ M ∧ C :=
  And.intro w.residualLost (And.intro w.scaleOntology w.categoryRules)

def buildCensusCompressionWitness
    (S M C : Prop) (hS : S) (hM : M) (hC : C) : CensusCompressionWitness S M C :=
  ⟨hS, hM, hC⟩

end ColonialCensusCompressionWitness
