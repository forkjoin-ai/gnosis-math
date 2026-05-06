/-
  WildeDecayOfLyingSincerityWitness.lean
  =======================================

  **Wildean sieve (in-repo tag):** the **tyranny of the sincere** — where “being true to
  yourself” collapses into a **moral aesthetic** that mistakes **performance of earnestness**
  for **discipline of thought**.

  Oscar Wilde, *The Decay of Lying* (**1889**) and *The Soul of Man Under Socialism*
  (**1891**; first publication in *Fortnightly Review*): a contrarian pivot from treating
  **facts** as the **external sovereign** (compare `OrwellNineteenEightyFourWitness` on
  **bedrock** speech about shared reality) toward an **internal sovereignty of style**
  — not “lies are good,” but a **warning** that **sincerity-cult** moralism can become a
  **category error** when it tries to occupy the slot reserved for **capital-T** absolutes
  the repository does **not** pretend to discharge in Init.

  **Quotation (Vivian’s line in *The Decay of Lying*, English):**

    “A little sincerity is a dangerous thing, and a great deal of it is absolutely fatal.”

  **Category hygiene (prose):** “truth” here maps to a **mis-sized** moral object — **not**
  the same functor as **agent truth** (attestations, logs, reproducible claims, **small-t**
  propositions you actually prove elsewhere). Conflating them reads as a **type error**
  in the witness stack, not as a proof that Wilde “refutes” Orwell.

  **Repo cousins:** `CohenAnthemWitness` (“**perfect** **offering**” **vs** **crack** — **popular**
  **song** **floor** on **perfectionism**; **rhymes** **with** **sincerity** **costume** **pressure**
  **here**); `MenckenConscienceShadowWitness` (social telemetry — different sting);
  `ProtagorasManIsMeasureWitness` (measure — different hazard); `OrwellNineteenEightyFourWitness`
  (fact/speech floor — **tension**, not contradiction, with Wilde’s aesthetic pole).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace WildeDecayOfLyingSincerityWitness

/-- Tag: external “sovereignty of facts” / public bedrock idiom (you define the `Prop`). -/
abbrev externalFactSovereignty (claim : Prop) : Prop :=
  claim

/-- Tag: internal “sovereignty of **style**” / form-of-life idiom (Wilde pole). -/
abbrev internalStyleSovereignty (claim : Prop) : Prop :=
  claim

/-- Tag: “sincerity” treated as a **moral fatal hazard** at scale (Wilde’s epigrammatic sting). -/
abbrev sincerityAsFatalPressure (claim : Prop) : Prop :=
  claim

/--
  Names the **move** from external fact-sovereignty talk to internal style-sovereignty talk —
  **no** theorem that either **entails** the other.
-/
structure FactToStyleMoveWitness (externalTag styleTag : Prop) where
  externalLayer : externalFactSovereignty externalTag
  internalLayer : internalStyleSovereignty styleTag

theorem fact_style_conjuncts (E S : Prop) (w : FactToStyleMoveWitness E S) : E ∧ S :=
  And.intro w.externalLayer w.internalLayer

def buildFactStyleWitness (E S : Prop) (hE : E) (hS : S) : FactToStyleMoveWitness E S :=
  ⟨hE, hS⟩

/-- Tag: **small-t** truth — ordinary propositions / correspondence talk (you discharge). -/
abbrev lowercaseTruth (claim : Prop) : Prop :=
  claim

/-- Tag: **agent** truth — procedures, attestations, falsifiable claims (even less “capitalized”). -/
abbrev agentTruth (claim : Prop) : Prop :=
  claim

/--
  Bundles the **move** Wilde names: style-sovereignty **and** sincerity-as-hazard — **no**
  implication that style **cancels** shared arithmetic (`OrwellNineteenEightyFourWitness`).
-/
structure WildeanSieveWitness (styleClaim sincerityHazard : Prop) where
  styleSovereignty : internalStyleSovereignty styleClaim
  sincereTyranny : sincerityAsFatalPressure sincerityHazard

theorem sieve_conjuncts (S T : Prop) (w : WildeanSieveWitness S T) : S ∧ T :=
  And.intro w.styleSovereignty w.sincereTyranny

def buildSieveWitness (S T : Prop) (hS : S) (hT : T) : WildeanSieveWitness S T :=
  ⟨hS, hT⟩

/--
  **Category hygiene bundle:** keeps **lowercase** truth talk and **agent** truth talk
  **separate** in the type system until you intentionally identify them elsewhere.
-/
structure TruthCategorySeparationWitness (smallT agentT : Prop) where
  ordinary : lowercaseTruth smallT
  operational : agentTruth agentT

theorem truth_layers (A B : Prop) (w : TruthCategorySeparationWitness A B) : A ∧ B :=
  And.intro w.ordinary w.operational

def buildTruthSeparationWitness (A B : Prop) (hA : A) (hB : B) : TruthCategorySeparationWitness A B :=
  ⟨hA, hB⟩

end WildeDecayOfLyingSincerityWitness
