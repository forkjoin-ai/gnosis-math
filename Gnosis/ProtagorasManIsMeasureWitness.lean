/-
  ProtagorasManIsMeasureWitness.lean
  ==================================

  Protagoras of Abdera (Greek, **c. 490–420 BC**), *measure* fragment (one English
  gloss; numbering varies by edition — **trad. DK** sources cluster this line under
  Protagoras’ ethical-relativist dossier):

    “Of all things the measure is Man: of the things that are, that they are, and of
    the things that are not, that they are not.”

  Greek tag (transliteration): *pantōn chrēmatōn metron estin anthrōpos*.

  **Hard culture (prose):** “truth” here is read as a **local measurement** indexed
  by the **witness** (the *anthrōpos* slot) — not a single static monolith you can
  lift out of context. Plato’s dialogues argue against this posture; in-repo we only
  **record** the Protagorean **shape** as a witness bundle (no claim that Plato
  “failed” or “succeeded” — that is editorial history, not Lean data).

  **Borges / exactitude (model obituary):** `BorgesOnExactitudeInScienceWitness` — at
  **1:1** scale, a “map” ceases to **compress**; local measures lose their **margin**
  the way a walkable duplicate loses cartography. Same **knowability** sting, fable register.

  **Goodhart / Strathern cluster (modern formal spine):** once a **metric** is
  pressed into service as a **control target**, it stops behaving like an innocent
  **readout** — the canonical slogan is Strathern’s gloss of Goodhart: **“when a
  measure becomes a target, it ceases to be a good measure.”** That is exactly the
  **game-theoretic** shadow of Protagorean locality: the “measure” was always
  **observer-indexed**; under optimization pressure it becomes a **cached game
  interface**, not a transparent window. The repo’s Init-proof wedge lives in
  `Gnosis.GoodhartsLaw` (via `godWeight` strict-antitone bookkeeping in `Gnosis.GodFormula`).
  A looser conversational variant — **“a measure ceases to be a good measure when
  it is measured”** — is not the historical quotation, but names the same **reflexive
  instrumentation** sting for witness-layer navigation.

  **Repo cousins:** `SchopenhauerHorizonFallacyWitness` (horizon / cognitive sandbox — measure
  of **world** mistaken for **private** bounds);
  `TruthOneManyNamesWitness` (many charts, one carrier when charts
  **agree** — contrast: Protagoras stresses **local** sheets even when they **diverge**);
  `HeraclitusUpDownPathWitness` (observer metadata vs path invariant);
  `MenckenConscienceShadowWitness` (inner voice indexed by social environment);
  `ParmenidesOnNatureWitness` (Eleatic floor — different negation job);
  `Gnosis.GoodhartsLaw` (formal wedge: measure-as-target distorts readout).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace ProtagorasManIsMeasureWitness

variable {ι : Type}

/--
  **Local truth sheet** at witness index `i` — “of the things that are, that they are”
  *for this measurer* (content is whatever you attach to `truthAt i`).
-/
abbrev LocalMeasure (truthAt : ι → Prop) (i : ι) : Prop :=
  truthAt i

/--
  Protagorean bundle: every index gets its **own** admitted sheet (the fragment’s
  “measure is man” formalized as **family**, not as one global `Prop`).
-/
structure ManIsMeasureWitness (truthAt : ι → Prop) where
  eachWitnessMeasures : ∀ i : ι, LocalMeasure truthAt i

theorem sheet_at (truthAt : ι → Prop) (w : ManIsMeasureWitness truthAt) (i : ι) :
    truthAt i :=
  w.eachWitnessMeasures i

def buildWitness (truthAt : ι → Prop) (h : ∀ i, truthAt i) : ManIsMeasureWitness truthAt :=
  ⟨h⟩

end ProtagorasManIsMeasureWitness
