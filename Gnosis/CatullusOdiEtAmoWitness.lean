/-
  CatullusOdiEtAmoWitness.lean
  ============================

  Catullus 85 (*Carmen* 85, “odi et amo”):

    “I hate and I love. / Why do I do this, you may ask? / I do not know,
     but I feel it happening / and I am in torment.”

  **Negative witness (contrast `BashoClinamenTrillWitness`):** Basho’s haiku
  chains a **positive** witness — the trill **certifies** the sting. Here the
  speaker certifies **torment** (*sentio*) while the **why-slot stays empty**
  (*nescio*): phenomenology without an answering reason. The diagram is an
  **epistemic void beside an affective chart**, like a cover with a hole where
  the explanation chart should attach (`DickinsonNeverSawMoorTopology` habit:
  assertoric lift without the matching justification morphism).

  **Versus rumination / consciousness overflow (`LocalizedOverflowConsciousness`):**
  rumination is **conscious-local persistent overflow** — long observation traces
  where thought-signal exceeds what the conscious band can stably hold, so the
  sieve reports **overflow-as-structure** with a **positive awareness gap**
  (`rumination_is_conscious_local_overflow`, `rumination_yields_thought_consciousness_overflow`).
  That is “too much dyed thread through the soul’s loom” in bandwidth terms.
  Catullus is the **orthogonal** failure mode: not overflow of noise, but
  **underflow of explanation** while affect still runs — *nescio* beside *sentio*,
  not saturation beside gap. Read beside Aurelius (*Meditations* 5.16,
  `MeditationsThoughtDyedWitness`): there the soul **takes** the tint of repeated
  thoughts; here the torment **runs** without the “color” of a known *why*.
  See also `PsychologyAsInterference.rumination_loop`
  and `DepressionAsDampedOscillation.rumination_loop` for the interference
  reading of rumination proper.

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace CatullusOdiEtAmoWitness

/-- Both affective poles asserted at once — no forced synthesis. -/
abbrev OdiEtAmo (odi amo : Prop) : Prop :=
  odi ∧ amo

/-- A would-be *reason* that would settle the “quare”; `KnowsWhy R` means `R`
    is taken as known. The void is `¬ KnowsWhy R`, i.e. `¬ R`. -/
abbrev KnowsWhy (reason : Prop) : Prop :=
  reason

/-- **Negative witness bundle:** polarity + felt torment + no accepted reason.

    Compare `basho_clinamen_trill_witness`: there the oscillation **implies** a
    sting. Here feeling **does not** deliver a `why` — the witness and the void
    coexist. -/
structure TormentWitnessWithoutWhy (odi amo feels knowsWhy : Prop) : Prop where
  poly : OdiEtAmo odi amo
  phenomenology : feels
  epistemic_void : ¬ KnowsWhy knowsWhy

/-- There is always some proposition (take `False`) that the speaker does **not**
    know — so the Catullan configuration can be filled as *witness + void* without
    collapsing the torment line. -/
theorem exists_torment_witness_with_explanatory_void
    (odi amo feels : Prop) (hp : OdiEtAmo odi amo) (hf : feels) :
    ∃ (why : Prop), TormentWitnessWithoutWhy odi amo feels why :=
  ⟨False, ⟨hp, hf, id⟩⟩

/-- The same bundle, but with an arbitrary **unsatisfied** reason slot: any
    proposition `why` you *fail* to know still supports the negative witness. -/
theorem torment_witness_given_not_knowing
    (odi amo feels why : Prop) (hp : OdiEtAmo odi amo) (hf : feels) (hn : ¬ why) :
    TormentWitnessWithoutWhy odi amo feels why :=
  ⟨hp, hf, hn⟩

/-- One-line spine for the poem’s last step: feeling does not entail knowing why. -/
theorem feeling_does_not_imply_reason (feels why : Prop) : feels → (¬ why) → feels ∧ ¬ why :=
  fun hf hn => And.intro hf hn

end CatullusOdiEtAmoWitness
