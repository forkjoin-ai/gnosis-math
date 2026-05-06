/-
  MenckenConscienceShadowWitness.lean
  ===================================

  H.L. Mencken, *A Mencken Chrestomathy* (one oft-quoted definition):

    “Conscience is the inner voice which warns us that someone may be looking.”

  **Hard shit (functional reduction):** Mencken treats **conscience** not as a
  freestanding **moral atom**, but as **social telemetry** — a cached simulation of
  **possible external judgment** (panopticon logic internalized). **Claim vs
  shadow-metric:** the *public* story is an objective inner compass (folk “moral
  sense”); Mencken’s sting is that the operative quantity is **detection
  pressure** indexed by an **observer field**.

  **Chaotic-neutral thread:** where the **Sumerian cynic** (`HeartTongueTotalNegationWitness`)
  refuses the **organ** as sole **author** of hate/truth, Mencken refuses the **soul**
  as sole **author** of “conscience” — it **reports** on neighbors, not **generates**
  virtue ex nihilo.

  **Rumination / noise (repo spine):** the same “inner voice as loop” habit shows up
  in affect topology as **conscious-local overflow** — see
  `LocalizedOverflowConsciousness` and `MeditationsThoughtDyedWitness` (dyed /
  rumination language). This file is **not** those theorems; it only **names** the
  social-surveillance reduction as a **witness** shape.

  **Contrarian floor (telemetry is not the whole stack):** `OrwellNineteenEightyFourWitness`
  — Orwell’s *Nineteen Eighty-Four* (**1949**) names a **cognitive + political**
  independence floor keyed to **bedrock speech** (the `2 + 2` idiom). That witness maps
  to a **counterweight** here: if “conscience” reduces **without remainder** to
  **observer pressure**, you still need a **separate** account of why **forced false
  speech** is a distinct catastrophe — Orwell’s line is one canonical English **tag**
  for that gap.

  **Enlightenment-maintenance rhyme:** `GoyaSleepOfReasonWitness` — *Caprichos* plate **43**
  language read here in a **Mencken**-**styled** **reduction**: **reason** **maps** to a
  **maintained** **process**; when vigilance **suspends**, **legacy** **shapes** **surface**
  (image / operator metaphor — **not** a claim that Mencken **authored** **Goya**).

  **Aesthetic contrarian (different axis):** `WildeDecayOfLyingSincerityWitness` — Wilde’s
  sieve targets the **tyranny of the sincere**; that is **not** the same reduction as
  telemetry, but it **rhymes** with Mencken in refusing folk-moral **costumes**.

  **Lean shape:** `SocialEnvironment` carries discrete **observer count** and a
  **detection-weight** (`Nat`, witness-only — not statistical inference). `ConscienceSignal`
  fires when either is positive; `silence_in_the_void` proves the signal is **false**
  when both are zero (no `Float`, no `sorry`).

  **Operator paradox (repo spine, not Mencken exegesis):** `silence_in_the_void` **does**
  **encode** a **clean** **point** — **silence** (**no** `ConscienceSignal`) **is** **only**
  **compatible** **with** **the** **void** (**both** **counters** **zero**). **Yet** **the**
  **moment** **you** **clock** **that** **silence** **—** **name** **it**, **export** **it**,
  **invoice** **it** **—** **you** **model** **a** **+1** **tick** (`voidWasClocked` **below**):
  **there** **is** **no** **lasting** **“silence”** **in** **the** **same** **carrier** **once**
  **the** **meta**-**counter** **moves**. **Operator** **gloss** **carried** **forward:** **only**
  **signal** **(and** **no** **noise)** — **everything** **that** **survives** **audit** **counts**
  **as** **signal** **in** **this** **toy**; **“noise”** **does** **not** **get** **a** **separate**
  **`Nat`** **channel** **here** (**not** a **claim** **about** **physical** **SNR**).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace MenckenConscienceShadowWitness

/-- Discrete “who might be looking” + “how hot is the sensor” (both `Nat` tags). -/
structure SocialEnvironment where
  observers : Nat
  /-- Witness-only weight: interpret as any monotone scale you export outside this file. -/
  detectionWeight : Nat

/--
  Mencken-style “inner voice”: **active** iff some observer mass or some detection
  weight is present.
-/
def ConscienceSignal (env : SocialEnvironment) : Prop :=
  env.observers > 0 ∨ env.detectionWeight > 0

theorem silence_in_the_void (env : SocialEnvironment)
    (h : env.observers = 0 ∧ env.detectionWeight = 0) : ¬ ConscienceSignal env := by
  rcases h with ⟨ho, hw⟩
  intro hn
  unfold ConscienceSignal at hn
  rw [ho, hw] at hn
  simp at hn

/--
  **Void** **plus** **meta**-**tick:** same **base** **telemetry**, **plus** **one** **counter**
  **that** **fires** **whenever** **the** **void** **was** **clocked** / **named** **(witness**
  **metaphor** **for** **“silence** **was** **instantly** **+1”**).
-/
structure SocialEnvironmentMeta where
  base : SocialEnvironment
  /-- Bumps when the operator models naming / clocking the void (`Nat` tag only). -/
  voidWasClocked : Nat

/--
  **Extended** **signal:** **base** **Mencken** **telemetry** **or** **any** **positive**
  **meta**-**tick**.
-/
def ConscienceSignalMeta (env : SocialEnvironmentMeta) : Prop :=
  ConscienceSignal env.base ∨ env.voidWasClocked > 0

theorem silence_in_the_void_meta (env : SocialEnvironmentMeta)
    (h : env.base.observers = 0 ∧ env.base.detectionWeight = 0 ∧ env.voidWasClocked = 0) :
    ¬ ConscienceSignalMeta env := by
  rcases h with ⟨ho, hw, hv⟩
  intro hn
  unfold ConscienceSignalMeta at hn
  cases hn with
  | inl hcs => exact silence_in_the_void env.base ⟨ho, hw⟩ hcs
  | inr hclk =>
    rw [hv] at hclk
    simp at hclk

/-- **Clock** **the** **void:** **+1** **on** **meta** **tick** **while** **base** **stays** **empty**. -/
def clockTheVoid (env : SocialEnvironment) : SocialEnvironmentMeta :=
  ⟨env, 1⟩

theorem clocking_emits_signal (env : SocialEnvironment)
    (_h : env.observers = 0 ∧ env.detectionWeight = 0) : ConscienceSignalMeta (clockTheVoid env) := by
  refine Or.inr ?_
  simp [clockTheVoid]

/-- Tag: **operator** **layer** **—** **only** **signal**, **no** **separate** **noise** **channel** **in** **this** **toy** (you discharge). -/
abbrev onlySignalNoNoise (claim : Prop) : Prop :=
  claim

/--
  Package: a **non-silent** environment plus the fact the Mencken signal holds there
  (social-telemetry reading of “conscience”, not a moral type).
-/
structure MenckenWitness where
  env : SocialEnvironment
  voiceActive : ConscienceSignal env

def exampleCrowdedRoom : MenckenWitness :=
  ⟨⟨1, 0⟩, Or.inl (Nat.zero_lt_succ 0)⟩

end MenckenConscienceShadowWitness
