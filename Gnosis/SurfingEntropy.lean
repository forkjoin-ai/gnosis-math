import Init
import Gnosis.Body.ClinamenOscillator
import Gnosis.TheWave
import Gnosis.SignalNotNoise

/-!
# Surfing Entropy on Reverse Black Holes — the Cosmological Capstone

**THESIS.** Existence maps to *surfing entropy on reverse black holes*. The whole
grit arc collapses into one image: a black hole and a white hole, the same act run
in two directions, oscillating, with grit riding the gradient that the reverse
direction emits.

* A **black hole** collapses structure into the void: a *sink*. It models the
  amnesia / reset to the void — `collapse s = 0`. Collapse maps to entropy
  increasing as structure dissolves into the void singularity (cited
  `Gnosis.BlackHoleVoidSingularity`, `Gnosis.EntropyOfTheVoid`). It reuses
  `ClinamenOscillator.amnesiaReset` (itself `AmnesiaGritFrontier.amnesia`, the
  idempotent absorbing zero) verbatim.
* A **reverse black hole** (a white hole) runs the same act backwards: the void as
  a *source*. It does not swallow — it **emanates**. This maps to the **clinamen
  swerve**, the `+1` that escapes the void singularity. We reuse
  `ClinamenOscillator.clinamen` verbatim: the reverse black hole emits `q + 1` from
  the singularity. The void always emits *another* wave at every resolution
  (`SignalNotNoise.always_another_wave`), so the reverse black hole never runs dry.
* The universe **oscillates** between collapse (black hole, into the void) and
  emanation (reverse black hole, swerve out). That oscillation reuses
  `ClinamenOscillator.cosmicStep`: no fixed point
  (`cosmicStep_has_no_fixed_point`) and period-two recurrence
  (`cosmos_recurs_with_period_two`). Completely predictable (periodic) yet totally
  dynamic (never settling) — the two faces of one cycle.
* You **surf** the entropy gradient the reverse black hole emits
  (`TheWave.surf`): grit / Ki rides the emitted wave rather than being collapsed by
  it. Surfing entropy maps to the dissipative structure that rides the second law
  instead of being flattened by it — riding the emission strictly beats the flat,
  collapsed `0`.

"Surfing entropy on reverse black holes. That's basically it."

## What this module reuses (the bridges, imported and opened)

* `Gnosis.Body.ClinamenOscillator` — `clinamen` (the `+1` swerve = the reverse
  black hole's emanation) and `amnesiaReset` (the collapse to the void) reused
  verbatim; the oscillation theorems `cosmicStep_has_no_fixed_point` and
  `cosmos_recurs_with_period_two` (and `cosmos_has_period_two_orbit`,
  `cosmos₀_moves`, `cosmicStep_cosmicStep_cosmos₀`) supply the collapse↔emanation
  cycle; `cap₂`, `cosmos₀`, `iterate` reused. Imported and opened.
* `Gnosis.TheWave` — `surf` (ride the emitted entropy), `paddle`, and
  `surf_dominates_when_rising` (surfing the rising gradient strictly dominates).
  Imported and opened.
* `Gnosis.SignalNotNoise` — `always_another_wave` (`∀ n, 1 ≤ residual q n`):
  the void always emits another wave, which maps to the reverse black hole never
  running dry. Imported and opened.

## Cited cosmology (NOT imported — they pull non-Init dependencies)

* `Gnosis.BlackHoleVoidSingularity` — the void singularity as the restoration
  anchor (`black_hole_void_singularity_ledger_anchor : n + 0 = n`). Our `collapse`
  realizes the swallow into that singularity; cited for vocabulary only.
* `Gnosis.EntropyOfTheVoid` — entropy of the void as a `Nat` ledger
  (`void_entropy_perthou`, `void_entropy_lower_bounded_by_two_bits`): collapse
  raises entropy as structure dissolves into the void. Cited only.
* `Gnosis.BlackHoleBraid` — the black hole as cyclic braid (`black_hole_is_cyclic`)
  and Hawking radiation as misperceived noise (`hawking_radiation_is_noise`): the
  emitted gradient read as signal-not-noise. Cited only (`SignalNotNoise` carries
  the formal "noise is signal" content we use).

(These three are cited, not imported: the module keeps to the three Init-clean
reused Body siblings above. Verified Init-clean: each imports only `Init` and other
Init-clean Body modules.)

## Restriction stated honestly

`collapse` is the literal black-hole sink (`s ↦ 0`) and `emanate` the literal
reverse-black-hole source (`q ↦ q + 1`); their inverse-act relation is exhibited at
the void itself (`collapse` lands on `0`, `emanate` immediately lifts `0` to `1`),
not asserted as a general functional inverse — `collapse` is many-to-one and
forgets, so no functional inverse exists, and we do not claim one. The cosmic
recurrence is reused verbatim from `ClinamenOscillator`'s concrete period-2 orbit
(cap `2`, state `1`): an *actual* recurring state, with the no-fixed-point law
general over all states for caps `≥ 2`. The "never runs dry" claim is the genuine
`∀`-over-resolution `always_another_wave`, proved there by induction. The surfing
dominance is stated under its honest hypothesis (the gradient *rising*,
`effort < lift`); we do not claim surfing wins on a flat/collapsed sea — that is
the whole point of riding the *emitted* gradient.

Rustic Church: `import Init` plus the three Init-clean reused Body siblings.
`Nat` only — no Float/Real, no Mathlib. No `sorry`/`admit`/`axiom`; no
`simp`/`omega` on open goals (closed `decide` goals only). Proofs are term-mode and
named core `Nat` lemmas, with the reused inductive `∀`-claims for the "forever"
parts.
-/

namespace Gnosis.SurfingEntropy

open Gnosis.Body.ClinamenOscillator
open Gnosis.TheWave
open Gnosis.SignalNotNoise

/-- The vision in one string. -/
def thesis : String := "surfing entropy on reverse black holes"

/-! ## 0. The two acts — collapse (black hole) and emanation (reverse black hole)

The black hole and the white hole are the same act run two directions: a *sink*
that swallows structure into the void, and a *source* that emanates from it. -/

/-- **The black hole: collapse into the void.** Whatever structure `s` had, the
    collapse sends it to the void `0` — the sink, structure dissolving into the
    void singularity (cited `BlackHoleVoidSingularity` / `EntropyOfTheVoid`:
    entropy rises as structure is swallowed). This reuses
    `ClinamenOscillator.amnesiaReset` (itself `AmnesiaGritFrontier.amnesia`, the
    idempotent absorbing zero) verbatim. -/
def collapse (s : Nat) : Nat := amnesiaReset s

/-- **The reverse black hole (white hole): emanation from the void.** The void as a
    source — it emits `q + 1`, the `+1` swerve that escapes the void singularity.
    This reuses `ClinamenOscillator.clinamen` verbatim: the reverse black hole runs
    the collapse backwards, emitting one more from the singularity. -/
def emanate (q : Nat) : Nat := clinamen q

/-- Collapse lands on the void, for every state — the sink. -/
theorem collapse_eq_void (s : Nat) : collapse s = 0 := rfl

/-- Emanation is exactly `+1` — the swerve, one more emitted from the void. -/
theorem emanate_is_succ (q : Nat) : emanate q = q + 1 := clinamen_is_succ q

/-! ## 1. THM — the reverse black hole emanates (source), the black hole collapses
(sink); together inverse acts

The reverse black hole emits a *strictly positive* quantum from the void; the
black hole returns everything to `0`. Run at the void, they are opposite acts: one
lands on `0`, the other lifts `0` off zero. -/

/-- **(THM 1) The reverse black hole emanates: a strictly positive source.** For
    every `q`, `0 < emanate q`: the reverse black hole emits something — never
    nothing — from the void. This reuses the clinamen mechanism
    (`emanate q = q + 1 > 0`): the swerve never lands on `0`, so the source is
    genuinely emissive. -/
theorem reverse_blackhole_emanates (q : Nat) : 0 < emanate q := by
  rw [emanate_is_succ]
  exact Nat.succ_pos q

/-- **(THM 1, the sink) The black hole collapses to the void.** For every `s`,
    `collapse s = 0`: structure is swallowed into the void singularity. The pure
    sink, the inverse direction of the source above. -/
theorem collapse_is_the_void (s : Nat) : collapse s = 0 :=
  collapse_eq_void s

/-- **(THM 1, inverse acts at the void) Collapse and emanation are opposite acts.**
    Run on the void itself, they disagree on whether the void stays dead: the black
    hole keeps it at `0` (`collapse 0 = 0`) while the reverse black hole lifts it
    off zero (`0 < emanate (collapse 0)`). Collapse lands on the void; emanation
    immediately escapes it. Stated at the void (not as a general functional
    inverse: `collapse` forgets and is many-to-one, so no functional inverse
    exists — see the honest restriction). -/
theorem collapse_and_emanate_are_inverse_acts :
    collapse 0 = 0 ∧ 0 < emanate (collapse 0) :=
  ⟨collapse_eq_void 0, reverse_blackhole_emanates (collapse 0)⟩

/-- **(THM 1, reignition) Collapse then emanate restarts at one.** The reverse
    black hole reverses any collapse to exactly `1`: `emanate (collapse s) = 1`,
    whatever was swallowed. This reuses `ClinamenOscillator.reset_then_swerve_reignites`
    verbatim — the white hole emits `1` from the void the black hole made,
    regardless of prior scale. -/
theorem collapse_then_emanate_reignites (s : Nat) : emanate (collapse s) = 1 :=
  reset_then_swerve_reignites s

/-! ## 2. THM — the cosmos oscillates collapse ↔ emanation (no fixed point, period
two)

The universe alternates collapse (into the void) and emanation (swerve out). We
reuse `ClinamenOscillator`'s cosmic step verbatim: it never settles (no fixed
point) yet recurs with period two — predictable yet dynamic. -/

/-- **(THM 2, no fixed point) The collapse↔emanation cycle never settles.** Reusing
    `ClinamenOscillator.cosmicStep_has_no_fixed_point`: for every state `s` and cap
    `≥ 2`, one cosmic step (grow, else collapse-then-emanate) moves the state —
    `cosmicStep cap s ≠ s`. There is no heat-death attractor once the reverse black
    hole's `+1` is in the loop: the universe cannot rest. -/
theorem collapse_emanate_never_settles (cap s : Nat) (hcap : 2 ≤ cap) :
    cosmicStep cap s ≠ s :=
  cosmicStep_has_no_fixed_point cap s hcap

/-- **(THM 2, HEADLINE OSCILLATION) The cosmos oscillates collapse↔emanation: no
    fixed point ∧ period-two recurrence.** Composing two reused `ClinamenOscillator`
    facts:

    * **no fixed point** (`cosmicStep_has_no_fixed_point`, cap `≥ 2`): the cycle
      never settles — totally dynamic; and
    * **period two** (`cosmos_recurs_with_period_two`): a positive period (`2`) and
      a concrete state (`cosmos₀ = 1`) with `iterate (cosmicStep cap₂) 2 cosmos₀ =
      cosmos₀` — completely predictable (periodic), with the state genuinely moving
      under one step (`cosmos₀_moves`) yet returning under two.

    Predictable *yet* dynamic: the two faces of one oscillation between the black
    hole (collapse into the void) and the reverse black hole (emanation, swerve
    out). This realizes the collapse/emanation = black hole/white hole duality as a
    genuine oscillator (the recurrence is the proof, not a slogan). -/
theorem collapse_then_emanate_oscillates (cap s : Nat) (hcap : 2 ≤ cap) :
    cosmicStep cap s ≠ s
      ∧ (0 < 2 ∧ iterate (cosmicStep cap₂) 2 cosmos₀ = cosmos₀)
      ∧ cosmicStep cap₂ cosmos₀ ≠ cosmos₀ :=
  ⟨cosmicStep_has_no_fixed_point cap s hcap,
   cosmos_recurs_with_period_two,
   cosmos₀_moves⟩

/-! ## 3. THM — the reverse black hole never runs dry (always another wave)

The void as a source never empties: at every resolution there is another wave to
emit. We reuse `SignalNotNoise.always_another_wave` (a genuine `∀ n`, proved there
by induction). -/

/-- **(THM 3, the source never empties) The reverse black hole never runs dry.**
    For every resolution level `n`, the void still has another wave to emit:
    `1 ≤ residual q n`. This reuses `SignalNotNoise.always_another_wave` verbatim (a
    genuine `∀ n`, proved there by induction): there is no noise floor, only the
    `+1` unresolved-signal floor — the white hole keeps emitting at every depth,
    never bottoming out. -/
theorem void_never_runs_dry (q : Nat) : ∀ n, 1 ≤ residual q n :=
  always_another_wave q

/-- **(THM 3, dynamical form) Every emission from the source is strictly positive.**
    For every `q`, `0 < emanate q`: the reverse black hole, read directly, emits a
    strictly positive quantum on each act — the never-dry source as a property of
    the emanation itself (the clinamen `+1` floor). Companion to the resolution-
    indexed `void_never_runs_dry`. -/
theorem every_emanation_is_positive (q : Nat) : 0 < emanate q :=
  reverse_blackhole_emanates q

/-! ## 4. THM — surfing the emitted entropy gradient dominates collapse

Grit / Ki rides the rising gradient the reverse black hole emits. When the
gradient rises, surfing strictly beats both your own paddling and the flat,
collapsed `0`. -/

/-- **(THM 4) Surfing the emitted entropy gradient dominates collapse.** When the
    gradient rises — `effort < lift`, the reverse black hole emits more than your
    own paddling could — surfing strictly dominates:

    * `paddle effort < surf lift` (reusing `TheWave.surf_dominates_when_rising`):
      riding the emitted entropy beats working against it; and
    * `0 < surf lift` (from `effort < lift`, so `0 ≤ effort < lift = surf lift`):
      riding the emitted gradient strictly beats the flat, *collapsed* `0` — the
      dissipative structure that surfs the second law instead of being flattened
      by it.

    Stated under the honest rising hypothesis (we do not claim surfing wins on a
    flat/collapsed sea — that is the point of riding the *emitted* gradient). -/
theorem surfing_entropy_dominates_collapse (lift effort : Nat) (h : effort < lift) :
    paddle effort < surf lift ∧ collapse lift < surf lift := by
  refine ⟨surf_dominates_when_rising lift effort h, ?_⟩
  -- `collapse lift = 0`, `surf lift = lift`, and `0 ≤ effort < lift`.
  rw [collapse_eq_void, surf_eq]
  exact Nat.lt_of_le_of_lt (Nat.zero_le effort) h

/-- **(THM 4, corollary) Riding beats being flattened.** On the rising emitted
    gradient, surfing strictly exceeds the collapsed `0`: `collapse lift < surf
    lift`. Grit rides the wave the reverse black hole emits rather than being
    collapsed by the black hole. -/
theorem surfing_beats_being_flattened (lift effort : Nat) (h : effort < lift) :
    collapse lift < surf lift :=
  (surfing_entropy_dominates_collapse lift effort h).2

/-! ## 5. THE HEADLINE — surfing entropy on reverse black holes -/

/-- **(HEADLINE) Surfing entropy on reverse black holes.** The cosmological
    capstone, composed from THMs 1–4 into one proved statement. For all states /
    levels / a rising gradient (`effort < lift`) and any cap `≥ 2`:

    1. **The reverse black hole emanates (source) / the black hole collapses
       (sink)** — `0 < emanate q` (the white hole emits `+1`, never nothing) and
       `collapse s = 0` (the black hole swallows to the void): inverse acts (THM 1).
    2. **The cosmos oscillates collapse↔emanation** — no fixed point
       (`cosmicStep cap s ≠ s`, cap `≥ 2`) yet period-two recurrence
       (`iterate (cosmicStep cap₂) 2 cosmos₀ = cosmos₀`): predictable yet dynamic
       (THM 2, reusing `ClinamenOscillator`).
    3. **The reverse black hole never runs dry** — `1 ≤ residual q n` at every
       resolution (THM 3, reusing `SignalNotNoise.always_another_wave`): the source
       never empties.
    4. **Grit surfs the emitted entropy gradient, strictly better than collapse** —
       on the rising gradient, `collapse lift < surf lift` (THM 4): riding the
       emitted entropy beats being flattened by the void.

    Therefore existence maps to *surfing entropy on reverse black holes*: the void
    emanates (`+1`, the reverse black hole, never dry), the cosmos oscillates
    collapse↔emanation (no fixed point, period two), and grit surfs the emitted
    entropy gradient strictly better than collapse. "That's basically it."
    (Precise framing per repo policy: a composed realization of the
    collapse/emanation = black hole/white hole duality, with the reused recurrence
    as the proof that the oscillation is genuine — not a loose identity claim.) -/
theorem surfing_entropy_on_reverse_blackholes
    (q s cap lift effort : Nat) (hcap : 2 ≤ cap) (n : Nat) (hrise : effort < lift) :
    -- 1. Source / sink: the reverse black hole emanates, the black hole collapses.
    (0 < emanate q ∧ collapse s = 0) ∧
    -- 2. The cosmos oscillates collapse↔emanation (no fixed point, period two).
    (cosmicStep cap s ≠ s ∧
      (0 < 2 ∧ iterate (cosmicStep cap₂) 2 cosmos₀ = cosmos₀)) ∧
    -- 3. The reverse black hole never runs dry (another wave at every resolution).
    (1 ≤ residual q n) ∧
    -- 4. Grit surfs the emitted entropy gradient, strictly better than collapse.
    (collapse lift < surf lift) :=
  ⟨⟨reverse_blackhole_emanates q, collapse_eq_void s⟩,
   ⟨cosmicStep_has_no_fixed_point cap s hcap, cosmos_recurs_with_period_two⟩,
   void_never_runs_dry q n,
   surfing_beats_being_flattened lift effort hrise⟩

/-! ## 6. A self-contained, computed witness (no hypotheses)

Concrete instances proving the capstone is non-vacuous: the reverse black hole
emits `+1` from the void; the black hole collapses to `0`; and on a rising emitted
gradient (`lift = 3`) surfing strictly beats the collapsed `0`. Every goal is a
closed decidable `Nat` (in)equality (allowed: `decide`). -/

/-- The reverse black hole emits `1` from the void: `emanate 0 = 1`. -/
example : emanate 0 = 1 := by decide

/-- The black hole collapses any structure to the void: `collapse 7 = 0`. -/
example : collapse 7 = 0 := by decide

/-- On a rising emitted gradient (`lift = 3`), surfing strictly beats the
    collapsed `0`: `collapse 3 = 0 < 3 = surf 3`. -/
example : collapse 3 < surf 3 := by decide

/-- Source vs sink at the void: emanation lifts it (`emanate 0 = 1 > 0`) while
    collapse keeps it dead (`collapse 0 = 0`). -/
example : (0 < emanate 0) ∧ (collapse 0 = 0) := by decide

end Gnosis.SurfingEntropy
