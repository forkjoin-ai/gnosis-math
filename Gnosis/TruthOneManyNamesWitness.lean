/-
  TruthOneManyNamesWitness.lean
  =============================

  Indian tradition (Ṛg Veda, widely quoted paraphrase):

    “Truth is one; / the wise call it / by many names.”

  **Formal spine (Init):** one carrier `Truth`, many indices `ι` of “names” or
  traditions, and an assignment `ι → Truth`. Agreement — all names pick out the
  **same** witness — is `manyNamesAgree`. With at least one index, that witness is
  **unique** (`unique_witness_of_many_names`). This is the discrete chart-compatibility
  picture: many local appellations, one underlying point (compare glueing charts
  on a manifold: overlap forces equality of the represented germ).

  This file does **not** assert that any particular religion exhausts `Truth`;
  it only certifies the *shape* “many labels, one denotation” when agreement holds.

  **See also** `SimonidesSpartanEpitaphWitness`: one inscription, many strangers
  may **bear** the same message home — the relay edge is a different geometry than
  chart glueing, but the “one truth, many mouths” habit rhymes.

  **See also** `RigVedaNasadiyaSuktaWitness`: same broad corpus, opposite **gesture**
  — neither existence nor nothingness is assertable at the hymn’s *then*.

  **See also** `MumonkanGatelessGateWitness`: many **paths**, no privileged “gate”
  index in the Zen couplet’s pedagogy (cousin geometry, different tradition).

  **See also** `BorgesOnExactitudeInScienceWitness`: when the “chart” becomes **as big
  as the world**, chart-compatibility is no longer **information** — the fable’s
  obituary for the **model**.

  **See also** `MagritteTreacheryOfImagesWitness`: **label** **≠** **object** — the
  opposite **gesture** from “many **honest** names, **one** denotation” when agreement holds;
  Magritte names the **scandal** of **confusing** sign for thing.

  **See also** `GoebbelsBigLieRepetitionWitness`: **forced** **monochrome** **narrative** **vs**
  **merge**-**honest** **fork** **attenuation** — **different** **geometry** **than** **honest**
  **many**-**names** **agreement**, **but** **names** **the** **same** **pressure** **point**
  **from** **below**.

  **See also** `CummingsLeafFallsParenthesisWitness`: **one** **surface** **word** **hosts**
  **another** **process** **in** **typography** — **not** the **same** **formal** **shape** as
  `manyNamesAgree`, **but** a **cousin** **pressure** on **how** **“one”** **and** **“loneliness”**
  **share** **space**.

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace TruthOneManyNamesWitness

variable {ι : Type} {Truth : Type}

/-- The wise map each name-index to a point of the one truth-carrier. -/
abbrev wiseCall (assign : ι → Truth) : ι → Truth :=
  assign

/-- All local names refer to the same distinguished witness. -/
def manyNamesAgree (assign : ι → Truth) (w : Truth) : Prop :=
  ∀ i : ι, assign i = w

theorem unique_witness_of_many_names [Nonempty ι] (assign : ι → Truth) (w w' : Truth)
    (hw : manyNamesAgree assign w) (hw' : manyNamesAgree assign w') : w = w' := by
  rcases ‹Nonempty ι› with ⟨i⟩
  exact (hw i).symm.trans (hw' i)

/-- Constant naming: every tradition uses the same word — trivial agreement. -/
theorem constant_names_agree (w : Truth) : manyNamesAgree (fun _ : ι => w) w := by
  intro _
  rfl

end TruthOneManyNamesWitness
