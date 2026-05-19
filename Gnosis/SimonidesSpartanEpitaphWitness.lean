import Init

/-
  SimonidesSpartanEpitaphWitness.lean
  ===================================

  Simonides of Ceos, epitaph for the Spartans fallen at Thermopylae (trad.):

    “Stranger, tell the Spartans / that we lie here, / obedient to / their laws.”

  Witness / testimony / bearing tree (repo spine): this poem is a relay
  witness — not proof of a theorem inside the fallen, but a message edge
  addressed to the passer-by to carry home to Lacedaemon. Same moral family
  as `Gnosis.Witnesses` (runtime witness records), `WitnessPointTheorem` (ledger
  anchor for “where the witness sits”), and `TruthOneManyNamesWitness` (one
  denotation, many routes): one fact of the grave, many strangers may speak
  it. Testimony language runs through `FoldedBuleyeanView` / `ChurchPillars`
  (weight as emergent testimony from the fold). Bearing tree is the folklore
  image in `docs/ebooks/source-texts/README.md` (oral chain + marked tree): here
  the trunk is *tell → site → nomos* — the stranger is the branch that bears
  the inscription back to the polis.

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace SimonidesSpartanEpitaphWitness

/-- The passer-by is charged with relay (first line: “Stranger, tell…”). -/
abbrev StrangerRelay (mustTell : Prop) : Prop :=
  mustTell

/-- The ground-witness: “we lie here” (inscription meets earth). -/
abbrev WeLieHere (burialSite : Prop) : Prop :=
  burialSite

/-- The nomos-witness: obedience named as the reason the site is true. -/
abbrev ObedientToSpartanLaws (nomos : Prop) : Prop :=
  nomos

/-- The three-line epitaph as one bundled bearing proposition. -/
structure SpartanEpitaphWitness (relay site law : Prop) : Prop where
  bearingDuty : StrangerRelay relay
  inscriptionGround : WeLieHere site
  lawfulRest : ObedientToSpartanLaws law

theorem epitaph_unfolds (relay site law : Prop) (w : SpartanEpitaphWitness relay site law) :
    relay ∧ site ∧ law :=
  And.intro w.bearingDuty (And.intro w.inscriptionGround w.lawfulRest)

/-- From three accepted witnesses, build the epitaph bundle (constructive relay). -/
def buildEpitaph (relay site law : Prop) (hr : relay) (hs : site) (hl : law) :
    SpartanEpitaphWitness relay site law :=
  ⟨hr, hs, hl⟩

end SimonidesSpartanEpitaphWitness
