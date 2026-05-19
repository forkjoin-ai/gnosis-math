import Init

/-
  BoschGardenEarthlyDelightsWitness.lean
  ======================================

  Hieronymus Bosch (~1450–1516), *The Garden of Earthly Delights* (oil triptych,
  ~1490–1510 — dating is museum-label dependent).

  Hard-culture floor (in-repo English): the network of consequences —
  a total negation of the idea that actions are isolated (each
  deed maps to ramifying edges in the triptych’s visual graph,
  not a sociology theorem here).

  Operator couplet (English gloss; in-repo composite — not attributed as Bosch’s
  manuscript line):

    “The mind is a city, and every street leads to a judgment.”

  Subversion: the witness tags refuse the comfort that one can
  move down a single alley without waking elsewhere in
  the same topology (moral / psychological metaphor only).

  Proved toy (Init only): `toy_consequence_path_len` counts five `Nat`
  nodes in `List.range`, a numerical shadow for “path has
  edges” only; not the triptych as graph theory.

  Repo cousins: `HeartTongueTotalNegationWitness` (total negation shape —
  interface myths there, causal isolation myth here);
  `GoyaSleepOfReasonWitness` (systemic nightmare — later accent, shared
  density of consequence imagery); `MenckenConscienceShadowWitness`
  (detection pressure in the social grid — different variable);
  `BaconVelazquezPopeStudiesWitness` (body under stress — different century
  and medium).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace BoschGardenEarthlyDelightsWitness

/-- Tag: consequence network — edges bind acts (you discharge). -/
abbrev consequenceNetwork (claim : Prop) : Prop :=
  claim

/-- Tag: refusal of causal isolation between actions (total negation target). -/
abbrev negatesIsolatedActionMyth (claim : Prop) : Prop :=
  claim

/-- Tag: mind as city / streets → judgment (operator couplet layer). -/
abbrev mindCityJudgmentStreets (claim : Prop) : Prop :=
  claim

/--
  Garden bundle: network + isolation myth denied + city couplet.
-/
structure GardenConsequenceWitness (network isolation city : Prop) where
  edges : consequenceNetwork network
  notIslands : negatesIsolatedActionMyth isolation
  topology : mindCityJudgmentStreets city

theorem garden_conjuncts (N I C : Prop) (w : GardenConsequenceWitness N I C) : N ∧ I ∧ C :=
  And.intro w.edges (And.intro w.notIslands w.topology)

def buildGardenWitness (N I C : Prop) (hN : N) (hI : I) (hC : C) : GardenConsequenceWitness N I C :=
  ⟨hN, hI, hC⟩

/-- Toy: fixed path length on `List.range` (not the painting’s graph). -/
theorem toy_consequence_path_len : (List.range 5).length = 5 := by
  simp [List.length_range]

end BoschGardenEarthlyDelightsWitness
