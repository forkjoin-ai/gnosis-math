/-
  BorgesOnExactitudeInScienceWitness.lean
  =======================================

  Jorge Luis Borges, *On Exactitude in Science* (1946; often collected with prior
  fiction — the 1946 dating follows common anthology attribution), the cartography
  fable (one English précis):

    In that Empire, cartography grew so proud that a province map filled a
    city; an empire map filled a province; and finally the Guild produced
    a map of the Empire whose size was that of the Empire, coinciding point for
    point with the territory.

  Hard culture / knowability: this is the obituary of the “Model” as innocent
  compression. At perfect exactitude, the map stops being a map — it adds no
  epistemic margin over walking on the ground; “model theory” in the folk sense
  collapses into identity, and   inference has nowhere to stand. The sting rhymes
  with `ProtagorasManIsMeasureWitness` (local measures) and `GoodhartsLaw` (metrics
  under optimization pressure), but Borges names the 1:1 pathology: zero useful
  abstraction. See also `UnknowableAntiTheorems` for the repo’s formal “limits of
  legibility” cluster (different mathematics, same humility job).

  Repo cousins: `MagritteTreacheryOfImagesWitness` (1929 — label ≠ object;
  pointer vs address — semiotic floor before maximalist map pathology);
  `BaudrillardSimulacraSimulationWitness` (map precedes territory /
  hyperreal — fatal upgrade: simulation stack survives the referent);
  `CioranTroubleWithBeingBornWitness` (consciousness / self vs map /
  world — void loyalty floor);
  `TruthOneManyNamesWitness` (honest charts vs one useless 1:1 chart);
  `ProtagorasManIsMeasureWitness`; `GoodhartsLaw`; `UnknowableAntiTheorems`.

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace BorgesOnExactitudeInScienceWitness

/-- Fable scales (tags only — not a geography `Type`). -/
inductive CartographicScale where
  | provinceSwallowsCity
  | empireSwallowsProvince
  | empireCoincidesWithEmpire
  deriving DecidableEq, Repr

/--
  “Point-for-point coincidence” — the model has been inflated until it is no longer
  a proper subobject of the territory in the epistemic sense (package as your own `Prop`).
-/
abbrev PerfectCoincidence (claim : Prop) : Prop :=
  claim

structure ExactitudeObituaryWitness (literalism : Prop) where
  mapIsTerritory : PerfectCoincidence literalism

theorem coincidence_asserted (L : Prop) (w : ExactitudeObituaryWitness L) : L :=
  w.mapIsTerritory

def buildWitness (L : Prop) (h : L) : ExactitudeObituaryWitness L :=
  ⟨h⟩

end BorgesOnExactitudeInScienceWitness
