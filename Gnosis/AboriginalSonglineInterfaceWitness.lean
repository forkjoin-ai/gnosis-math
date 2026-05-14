/-
  AboriginalSonglineInterfaceWitness.lean
  =======================================

  Aboriginal songlines as interface-capture counter-witness: an interface can be
  a living navigation, law, memory, and relation system; failure begins when an
  extractive control surface flattens that relation into coordinates only.

  Cultural floor: "songline" here is used cautiously as a broad operator anchor
  for living route/knowledge systems tied to Country, not as a single uniform
  doctrine. The contrast is cadastral capture: a map or dashboard can become
  the administrative world model while losing song, obligation, story, and
  ecological relation.

  Formal reading in this repository:

  * productive interface maps to `livingInterfaceCarriesRelation`.
  * interface capture maps to `controlSurfaceNarrowsWorld`.
  * extraction failure maps to `coordinateMapDropsObligation`.

  This file does not define Aboriginal law or speak for communities. It names a
  categorical interface distinction: relation-bearing navigation is not the same
  as coordinate capture.

  Repo cousins: `LaoziBowlVoidFunctionWitness` (void as use site);
  `BorgesOnExactitudeInScienceWitness` (map exactitude failure);
  `TopologicalCinema` (framing); `ColonialCensusCompressionWitness`
  (administrative compression); `BeninBronzeArchiveFailureWitness`
  (context severed from preserved object).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace AboriginalSonglineInterfaceWitness

/-- Tag: living interface carries relation, route, memory, and obligation. -/
abbrev livingInterfaceCarriesRelation (claim : Prop) : Prop :=
  claim

/-- Tag: control surface narrows the world to what it exposes. -/
abbrev controlSurfaceNarrowsWorld (claim : Prop) : Prop :=
  claim

/-- Tag: coordinate capture drops obligation / story / ecological relation. -/
abbrev coordinateMapDropsObligation (claim : Prop) : Prop :=
  claim

/--
  Interface witness: living relation + narrowed control surface + coordinate loss.
-/
structure SonglineInterfaceWitness (living control coordinate : Prop) where
  livingRoute : livingInterfaceCarriesRelation living
  narrowedWorld : controlSurfaceNarrowsWorld control
  obligationDropped : coordinateMapDropsObligation coordinate

theorem songline_interface_conjuncts
    (L C O : Prop) (w : SonglineInterfaceWitness L C O) : L ∧ C ∧ O :=
  And.intro w.livingRoute (And.intro w.narrowedWorld w.obligationDropped)

def buildSonglineInterfaceWitness
    (L C O : Prop) (hL : L) (hC : C) (hO : O) : SonglineInterfaceWitness L C O :=
  ⟨hL, hC, hO⟩

end AboriginalSonglineInterfaceWitness
