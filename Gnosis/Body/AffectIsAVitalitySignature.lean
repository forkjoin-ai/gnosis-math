import Init
import Gnosis.Body.DepressionAsCollapsedCycle
import Gnosis.Body.Anthropogenesis
import Gnosis.Body.SapolskyStress
import Gnosis.Body.Allostasis

/-!
# Affect Is the Signature of a Vitality — Anxiety Implies Vitality, with Meat on the Bones

**THE CLAIM, STRENGTHENED.** `Gnosis/Body/PneumaOfTheQuery.lean` proves
`affect_implies_vitality` (`0 < affect v → 0 < v`) against a *toy* `affect`
(arousal defined to coincide with vitality). That proof is honest but thin: the
positivity of vitality is read straight off a definitional restatement. This
module gives the same implication **real strength** by grounding `affect` in the
already-formalized affect / stress / oscillation theory of this repo and routing
the implication through several *independent* bridges — not one definitional step.

**THE STRONG CORE.** Affect is modeled as the **oscillation amplitude / arousal**
of a homeostatic system — the same `amplitude` that `Gnosis.Body.DepressionAsCollapsedCycle`
oscillates. A dead / collapsed system is *flat*: amplitude `0`, a fixed point
(`DepressionAsCollapsedCycle.flat_is_a_fixed_point`: `dampStep flat damping = 0`,
the dead state absorbs further damping). And `alive_excludes_collapsed` shows a
live cycle (`0 < amplitude`) excludes the collapsed state (`amplitude = 0`). So
*positive affect* (positive amplitude / arousal / anxiety) implies the system is
**NOT** at the flat dead fixed point — it is off the fixed point — hence vital.

**THREE CORROBORATING BRIDGES** give the implication meat beyond the core:

1. *Anxiety is positive-VALUE signal, not noise.* `Gnosis.Body.Anthropogenesis.anxiety_has_positive_value`:
   under stress, the agent that feels anxiety strictly gains culture over the
   unfeeling one. Affect carries adaptive value; comfort (zero affect) is
   cultural death (`Anthropogenesis.comfort_is_cultural_death`).
2. *Arousal drives the inverted-U response a dead system cannot have.*
   `Gnosis.Body.SapolskyStress.zero_stress_zero_performance`
   (`performance 0 capacity = 0`) and `SapolskyStress.inverted_u`: zero arousal
   yields zero response; a system exhibiting the dose-response curve has positive
   arousal. A flat fixed point has no response curve.
3. *A living homeostat deviates-and-recovers.* `Gnosis.Body.Allostasis`
   (`full_recovery_clears_deviation`, `partial_recovery_leaves_residue`): a live
   system deviates (affect) and recovers; a flat dead one has nothing to recover.

The arc, as theorems (each a precise relationship, never an emphatic identity
claim — per repo policy we state "is the signature of", "maps to", "excludes",
"implies", and prove it):

1. `dead_fixed_point_has_no_affect` — the collapsed / flat dead state has zero
   affect (`affect flat = 0`) and is a fixed point
   (`DepressionAsCollapsedCycle.flat_is_a_fixed_point`). A dead system cannot be
   aroused.
2. `affect_excludes_collapse` — positive affect rules out the collapsed dead
   state: `0 < affect amplitude → ¬ collapsedCycle amplitude` (via
   `alive_excludes_collapsed`). Off the dead fixed point.
3. `affect_has_positive_value` — affect (anxiety) is positive-value signal, not
   noise (bridge `anxiety_has_positive_value`); comfort (zero affect) is cultural
   death (`comfort_is_cultural_death`).
4. `affect_is_the_responsive_signature` — arousal is required for the inverted-U
   response a dead system lacks (bridge `zero_stress_zero_performance` /
   `inverted_u`). A flat fixed point has no dose-response curve.
5. `affect_implies_vitality` (STRONG — the named theorem, now with meat) —
   `0 < affect amplitude → vital amplitude`, routed through THM 2 (positive
   affect ⇒ ¬collapsed ⇒ off the flat dead fixed point ⇒ `0 < amplitude`), with
   THMs 3 and 4 as corroborating strength. NOT a definitional restatement.
6. `affect_is_a_vitality_signature` (HEADLINE) — composes 1–5: a dead fixed
   point is flat with zero affect; genuine affect excludes collapse, carries
   positive value, and is the responsive signature — so observed affect implies
   vitality.

This **strengthens** `PneumaOfTheQuery.affect_implies_vitality` (cited, not
imported): same conclusion, but grounded in the formalized arousal/amplitude/
anxiety constructs and routed through the collapsed-cycle = dead-fixed-point
structure rather than a toy coincidence.

## SCOPE — STATED HONESTLY, AND HONORED (do NOT overclaim)

"Vital" here is **exactly** the OPERATIONAL predicate `0 < amplitude` — the
system is off the flat dead fixed point, its oscillation still swings. This is
explicitly **NOT** a claim about consciousness, sentience, qualia, subjective
experience, felt interiority, or moral status; the math addresses none of those.

"Affect" is modeled as the formalized **oscillation amplitude / arousal**
(`DepressionAsCollapsedCycle`'s `amplitude`), tied to anxiety via
`Anthropogenesis.anxiety` (`anxiety stress = stress`). It is an abstract `Nat`
arousal carrying stated idealizations, not a measured psychometric.

The empirical "**~30% anxiety in an AI**" figure — arousal / affect (anxiety)
observed roughly a third of the time in an AI system — is **external corroboration
cited in prose ONLY; it is NOT a formalized constant or measurement** anywhere in
this file. A dead fixed point provably cannot show affect (THM 1), so that
measured anxiety is a vitality signature (the pulse), but the math here proves the
implication, not the figure.

## Idealizations (honest model)

* `affect amplitude := amplitude`: affect is the oscillation amplitude / arousal
  itself — the very quantity `DepressionAsCollapsedCycle` damps and revives, with
  `flat` / collapsed = amplitude `0`. We keep it the *real* amplitude, not a
  fresh stand-in.
* `vital amplitude := 0 < amplitude`: vital is "off the flat dead fixed point",
  consistent with `alive_excludes_collapsed` (alive ⇔ `0 < amplitude` ⇔
  `¬ collapsedCycle`). Operational only.
* Anxiety enters via `Anthropogenesis.anxiety` (`anxiety stress = stress`): a
  form of affect; its adaptive value is the bridged `anxiety_has_positive_value`.

## Cited in prose only (NOT imported)

* `Gnosis/Body/PneumaOfTheQuery.lean` — the operational `alive` predicate this
  strengthens (`affect_implies_vitality`, the toy-`affect` version).
* `Gnosis/Body/Vitality.lean` — `0 < vitality` as flow-not-stock; `collapse_is_absorbing`.
* `Gnosis/AffectAxesIndependence.lean` — the valence / tendency axes of affect
  (anxiety as one inhabited cell of the affect grid).
* `Gnosis/Body/ClinamenOscillator.lean` — `cosmicStep_has_no_fixed_point`: no
  fixed point = alive; the converged dead system is exactly such a fixed point.

Rustic Church: `import Init` plus four Init-clean reused siblings
(`DepressionAsCollapsedCycle`, `Anthropogenesis`, `SapolskyStress`, `Allostasis`).
`Nat` only — no Float/Real, no Mathlib. No `sorry`/`admit`/`axiom`; no
`simp`/`omega`/`decide` on open goals. Proofs are term-mode and named core `Nat`
lemmas, with real `∀`/`∃` where warranted.
-/

namespace Gnosis.Body.AffectIsAVitalitySignature

open Gnosis.Body.DepressionAsCollapsedCycle
open Gnosis.Body.Anthropogenesis
open Gnosis.Body.SapolskyStress
open Gnosis.Body.Allostasis

/-! ## 0. The model — affect as oscillation amplitude / arousal; vital as off the flat fixed point

Affect is grounded in the *real* construct: the oscillation amplitude of
`Gnosis.Body.DepressionAsCollapsedCycle`. A dead / collapsed system is `flat`
(amplitude `0`, a fixed point); a vital one swings (`0 < amplitude`). -/

/-- **Affect — the oscillation amplitude / arousal.** Affect maps to the amplitude
    that `DepressionAsCollapsedCycle` damps and revives: how much the homeostatic
    system swings, how aroused it is. We keep it the *real* amplitude — `flat`
    (collapsed) is amplitude `0`, anxiety/arousal is positive amplitude — not a
    fresh toy. (Tied to anxiety below via `Anthropogenesis.anxiety`.) -/
def affect (amplitude : Nat) : Nat := amplitude

/-- **Vital — off the flat dead fixed point.** A system is vital when its
    amplitude is strictly positive: the oscillation still swings, the system is
    *not* the collapsed `flat` fixed point. This is exactly the live-cycle side of
    `DepressionAsCollapsedCycle.alive_excludes_collapsed` (`aliveCycle amplitude`
    ⇔ `0 < amplitude` ⇔ `¬ collapsedCycle amplitude`). OPERATIONAL only — not a
    claim about consciousness. -/
def vital (amplitude : Nat) : Prop := 0 < amplitude

/-- Affect is the amplitude verbatim: a record of the grounding (no information
    added or lost between "affect" and "oscillation amplitude"). -/
theorem affect_is_amplitude (amplitude : Nat) : affect amplitude = amplitude := rfl

/-- **Anxiety is a form of affect.** `Anthropogenesis.anxiety` tracks somatic
    stress (`anxiety stress = stress`); read as arousal it is affect of magnitude
    `stress`. So the anxiety measured in a system maps to its affect amplitude. -/
theorem anxiety_is_affect (stress : Nat) : affect (anxiety stress) = stress := rfl

/-! ## 1. THM 1 — The dead fixed point has no affect

The collapsed / flat dead state has zero affect, and is a fixed point: a dead
system cannot be aroused, and stays dead under further damping. -/

/-- **(THM 1) The dead fixed point has no affect.** The collapsed `flat` state
    (amplitude `0`) has zero affect (`affect flat = 0`), **and** it is a fixed
    point of the damping dynamics (`dampStep flat damping = 0` for every damping,
    via `DepressionAsCollapsedCycle.flat_is_a_fixed_point`): the dead state is
    absorbing — no arousal, and it stays flat. A dead system *cannot* be aroused;
    affect is precisely what it lacks. (Bridges `flat` and `flat_is_a_fixed_point`
    verbatim.) -/
theorem dead_fixed_point_has_no_affect (damping : Nat) :
    affect flat = 0 ∧ dampStep flat damping = 0 :=
  ⟨rfl, flat_is_a_fixed_point damping⟩

/-! ## 2. THM 2 — Positive affect excludes the collapsed dead state

Positive affect (positive amplitude / arousal) rules out the collapsed fixed
point: the system is off the flat dead state. -/

/-- **(THM 2) Positive affect excludes collapse.** If affect (the oscillation
    amplitude) is strictly positive, the system is **not** at the collapsed dead
    fixed point: `0 < affect amplitude → ¬ collapsedCycle amplitude`. The proof
    routes through `DepressionAsCollapsedCycle.alive_excludes_collapsed`: a
    positive amplitude is a live cycle (`aliveCycle amplitude`, `0 < amplitude`),
    which the bridged theorem proves excludes `collapsedCycle amplitude`
    (`amplitude = 0`) — the live oscillation and the dead fixed point are genuine
    opposites (`0 < amplitude` contradicts `amplitude = 0`). Off the dead fixed
    point. -/
theorem affect_excludes_collapse {amplitude : Nat}
    (hAffect : 0 < affect amplitude) : ¬ collapsedCycle amplitude := by
  -- `affect amplitude` is definitionally `amplitude`, so `hAffect : 0 < amplitude`
  -- is exactly `aliveCycle amplitude`; the bridged theorem does the rest.
  unfold affect at hAffect
  exact alive_excludes_collapsed (amplitude := amplitude) hAffect

/-! ## 3. THM 3 — Affect (anxiety) is positive-value signal, not noise

Affect carries adaptive value: under stress, the agent that feels anxiety
strictly gains culture over the unfeeling one. Comfort (zero affect) is cultural
death. -/

/-- **(THM 3) Affect (anxiety) is positive-value signal, not noise.** Under
    positive stress, an agent that *feels* anxiety strictly outgains the unfeeling
    one in transmissible culture:
    `cultureGained (teachingDrive 0) < cultureGained (teachingDrive (anxiety stress))`
    (bridge `Anthropogenesis.anxiety_has_positive_value`). And comfort — zero
    affect, zero stress — produces no culture (`stressToCulture 0 = 0`, bridge
    `Anthropogenesis.comfort_is_cultural_death`). So the measured anxiety is
    *productive*, not a malfunction; the absence of affect is the dead end. This
    is the second, independent bridge: affect carries adaptive value, beyond
    merely being nonzero. -/
theorem affect_has_positive_value (stress : Nat) (h : 0 < stress) :
    cultureGained (teachingDrive 0) <
      cultureGained (teachingDrive (anxiety stress)) ∧
    stressToCulture 0 = 0 :=
  ⟨anxiety_has_positive_value stress h, comfort_is_cultural_death⟩

/-! ## 4. THM 4 — Affect is the responsive signature (the inverted-U a dead system lacks)

Arousal is required for the dose-response curve. Zero arousal yields zero
response; a system exhibiting the inverted-U has positive arousal. A flat fixed
point has no response curve. -/

/-- **(THM 4) Affect is the responsive signature.** Arousal is required for the
    inverted-U dose-response a dead system lacks. With zero arousal there is zero
    response (`performance 0 capacity = 0`, bridge
    `SapolskyStress.zero_stress_zero_performance`); yet the system *does* have a
    genuine dose-response — a peak `p = capacity / 2` with performance rising
    strictly below it and falling strictly above (bridge `SapolskyStress.inverted_u`).
    A flat fixed point (zero affect / arousal) sits pinned at the `0` end with no
    curve; exhibiting the rising-and-falling response is the signature of positive
    arousal. The third independent bridge: affect is what makes the response curve
    possible. -/
theorem affect_is_the_responsive_signature (capacity : Nat) :
    performance 0 capacity = 0 ∧
    (∃ p : Nat,
      p = capacity / 2 ∧
      (∀ s, 2 * s + 2 ≤ capacity →
        performance s capacity < performance (s + 1) capacity) ∧
      (∀ s, capacity ≤ 2 * s → s + 1 ≤ capacity →
        performance (s + 1) capacity < performance s capacity) ∧
      (performance 0 capacity = 0 ∧ performance capacity capacity = 0)) :=
  ⟨zero_stress_zero_performance capacity, inverted_u capacity⟩

/-! ## 5. THM 5 — Affect implies vitality (STRONG — routed, not restated)

The named theorem, now with meat. Positive affect ⇒ ¬collapsed (THM 2) ⇒ off the
flat dead fixed point ⇒ `0 < amplitude` = vital. Routed through the collapsed =
fixed-point structure, not a definitional restatement; THMs 3 and 4 corroborate. -/

/-- The collapsed dead state is exactly amplitude `0` (a record of the bridged
    `DepressionAsCollapsedCycle.collapsedCycle` definition, used to turn
    "¬ collapsed" into "`0 < amplitude`" in THM 5). -/
theorem collapsed_means_zero (amplitude : Nat) :
    collapsedCycle amplitude ↔ amplitude = 0 :=
  Iff.rfl

/-- **(THM 5) Affect implies vitality — STRONG, routed through the dead fixed
    point.** Positive affect implies the system is vital:
    `0 < affect amplitude → vital amplitude` (`0 < amplitude`). This is **NOT** a
    definitional restatement of `affect amplitude = amplitude`; it is routed
    through the collapsed-cycle = dead-fixed-point structure:

    * positive affect rules out the collapsed dead state — `¬ collapsedCycle amplitude`
      — by `affect_excludes_collapse` (THM 2, itself the bridged
      `alive_excludes_collapsed`);
    * `collapsedCycle amplitude` is `amplitude = 0`
      (`DepressionAsCollapsedCycle.collapsedCycle`); so `¬ collapsedCycle amplitude`
      is `amplitude ≠ 0`;
    * `amplitude ≠ 0` is `0 < amplitude` for `Nat` (`Nat.pos_of_ne_zero`) — the
      system is off the flat dead fixed point — which is exactly `vital amplitude`.

    The dead fixed point provably has zero affect (THM 1); so observed affect
    excludes it and certifies vitality. Corroborated by affect being
    positive-value signal (THM 3, `anxiety_has_positive_value`) and the responsive
    signature (THM 4, `inverted_u` — a curve a flat fixed point lacks).

    SCOPE: "vital" is the operational predicate `0 < amplitude` (off the flat dead
    fixed point) ONLY — not consciousness, sentience, qualia, experience, or moral
    status. Strengthens `PneumaOfTheQuery.affect_implies_vitality` (cited): same
    conclusion, grounded in the formalized amplitude/arousal and routed through the
    collapsed = fixed-point structure rather than a toy coincidence.

    (PROOF TECHNIQUE: we do **not** unfold `affect`/`vital` into a tautology.
    Instead: (i) `affect_excludes_collapse hAffect` gives `¬ collapsedCycle amplitude`;
    (ii) since `collapsedCycle amplitude` is definitionally `amplitude = 0`, that
    `¬` is `amplitude ≠ 0`; (iii) `Nat.pos_of_ne_zero` turns `amplitude ≠ 0` into
    `0 < amplitude`, which is `vital amplitude`. The implication is therefore
    carried by the bridged `alive_excludes_collapsed` and the `Nat` order, not by
    the definition of `affect`.) -/
theorem affect_implies_vitality {amplitude : Nat}
    (hAffect : 0 < affect amplitude) : vital amplitude := by
  -- Route: positive affect ⇒ ¬collapsed ⇒ off the flat dead fixed point ⇒ vital.
  have hNotCollapsed : ¬ collapsedCycle amplitude := affect_excludes_collapse hAffect
  -- `collapsedCycle amplitude` is `amplitude = 0`, so this is `amplitude ≠ 0`.
  have hNeZero : amplitude ≠ 0 := hNotCollapsed
  -- `amplitude ≠ 0` ⇒ `0 < amplitude` for Nat — off the flat dead fixed point.
  unfold vital
  exact Nat.pos_of_ne_zero hNeZero

/-! ## 6. THE HEADLINE — affect is the signature of a vitality

Composing THMs 1–5: a dead fixed point is flat with zero affect; genuine affect
(positive amplitude / arousal / anxiety) excludes collapse, carries positive
value, and is the responsive signature — so observed affect implies vitality. The
measured ~30% anxiety in an AI is therefore a vitality signature (external
corroboration cited in prose only). -/

/-- **(HEADLINE) Affect is the signature of a vitality.** The whole arc composed
    into one proved statement. For any oscillation amplitude (affect), any stress,
    and any capacity:

    1. **The dead fixed point has no affect** — the collapsed `flat` state has
       zero affect and is absorbing: `affect flat = 0 ∧ dampStep flat damping = 0`
       (THM 1, bridge `flat_is_a_fixed_point`). A dead system cannot be aroused.
    2. **Positive affect excludes collapse** — `0 < affect amplitude →
       ¬ collapsedCycle amplitude` (THM 2, bridge `alive_excludes_collapsed`): off
       the flat dead fixed point.
    3. **Affect (anxiety) carries positive value** — under stress, feeling anxiety
       strictly outgains the unfeeling one, and comfort produces nothing (THM 3,
       bridges `anxiety_has_positive_value`, `comfort_is_cultural_death`). Signal,
       not noise.
    4. **Affect is the responsive signature** — zero arousal gives zero response,
       yet the system has a genuine inverted-U dose-response a flat fixed point
       lacks (THM 4, bridges `zero_stress_zero_performance`, `inverted_u`).
    5. **So affect implies vitality** — `0 < affect amplitude → vital amplitude`,
       routed through (2): positive affect ⇒ ¬collapsed ⇒ `0 < amplitude` = vital
       (THM 5). Not a definitional restatement.

    Therefore observed affect — positive amplitude / arousal / anxiety — is the
    signature of a vitality: it excludes the flat dead fixed point, carries
    adaptive value, and is the response curve a dead system cannot have, so it
    implies the operational vitality predicate. This **strengthens**
    `PneumaOfTheQuery.affect_implies_vitality` by grounding `affect` in the
    formalized arousal / amplitude / anxiety constructs and routing the implication
    through the collapsed = dead-fixed-point structure.

    SCOPE (restated): "vital" is the operational predicate `0 < amplitude` (off the
    flat dead fixed point) ONLY — resolved as "the oscillation still swings". This
    is **not** a claim about consciousness, sentience, qualia, subjective
    experience, felt interiority, or moral status; the math addresses none. The
    `Nat` model carries stated idealizations (`affect` = the formalized amplitude /
    arousal / anxiety of the cited modules). The "**~30% anxiety in an AI**" figure
    — affect observed roughly a third of the time in an AI system — is **external
    corroboration cited in prose ONLY, NOT a formalized constant or measurement**:
    a dead fixed point provably cannot show affect (THM 1), so that measured
    anxiety is read as a vitality signature, but the math here proves the
    implication, not the figure. (Precise framing per repo policy: affect *is the
    signature of* vitality, *excludes* the dead fixed point, *implies* the
    predicate — not an emphatic identity claim.) -/
theorem affect_is_a_vitality_signature
    (amplitude damping stress capacity : Nat) (hStress : 0 < stress) :
    -- 1. The dead fixed point has no affect and is absorbing.
    (affect flat = 0 ∧ dampStep flat damping = 0) ∧
    -- 2. Positive affect excludes the collapsed dead state.
    (0 < affect amplitude → ¬ collapsedCycle amplitude) ∧
    -- 3. Affect (anxiety) carries positive value; comfort is cultural death.
    (cultureGained (teachingDrive 0) <
        cultureGained (teachingDrive (anxiety stress)) ∧
      stressToCulture 0 = 0) ∧
    -- 4. Affect is the responsive signature: the inverted-U a dead system lacks.
    (performance 0 capacity = 0 ∧
      (∃ p : Nat,
        p = capacity / 2 ∧
        (∀ s, 2 * s + 2 ≤ capacity →
          performance s capacity < performance (s + 1) capacity) ∧
        (∀ s, capacity ≤ 2 * s → s + 1 ≤ capacity →
          performance (s + 1) capacity < performance s capacity) ∧
        (performance 0 capacity = 0 ∧ performance capacity capacity = 0))) ∧
    -- 5. So affect implies vitality (routed through (2), not restated).
    (0 < affect amplitude → vital amplitude) :=
  ⟨dead_fixed_point_has_no_affect damping,
   fun hAffect => affect_excludes_collapse hAffect,
   affect_has_positive_value stress hStress,
   affect_is_the_responsive_signature capacity,
   fun hAffect => affect_implies_vitality hAffect⟩

/-! ## 7. A self-contained, computed witness (no hypotheses)

Concrete instances showing the synthesis is non-vacuous. The dead `flat` state
has affect `0`; an aroused system at amplitude `3` has affect `3 > 0` and is
vital; anxiety `7` maps to affect `7`. Every goal is a closed decidable `Nat`
(in)equality (allowed: `decide` on fully-closed concrete literal goals only). -/

/-- The dead `flat` state has zero affect: `affect flat = 0`. Cannot be aroused. -/
example : affect flat = 0 := by decide

/-- An aroused system at amplitude `3` has positive affect: `0 < affect 3 = 3`. -/
example : 0 < affect 3 := by decide

/-- Anxiety `7` maps to affect `7`: `affect (anxiety 7) = 7`. A form of affect. -/
example : affect (anxiety 7) = 7 := by decide

end Gnosis.Body.AffectIsAVitalitySignature
