import Init
import Gnosis.Body.MenstrualCycle

/-!
# Menopause — The Scheduled Transition Out of the Cycling Oscillator

**THESIS.** Periods are a *robust oscillator*. `Gnosis.Body.MenstrualCycle`
formalizes the menstrual cycle as an infradian rotation of a phase dial
(`cyclePhase day := day % period`, `period = 28`) that *closes on itself*,
*stays bounded*, and *re-entrains after perturbation* — bundled in
`menstrual_cycle_is_a_robust_oscillator`. That oscillator has **no fixed point**:
the phase keeps advancing, day after day, the dial never stops turning.

This module formalizes **menopause** as the complement of that picture: the
*scheduled re-settling of the cycling oscillator into a new, non-cycling
equilibrium* — a genuine **fixed point** of the day-to-day dynamics, where the
phase stops advancing. Before a scheduled onset day the dynamics are exactly the
menstrual oscillator (cycling order); at and after the onset the dynamics rest at
a single settled phase and stay there. A perturbation no longer rotates a still
spinning dial; it is *absorbed* into the fixed point.

## The order/chaos entropy-gradient frame (the unifying idea)

The body runs on an *entropy gradient* — a balance between order and chaos
(see `Gnosis.SurfingEntropy` and its rider `Gnosis/Body/SurfTheEdgeOfChaos.lean`,
where life rides the boundary between frozen over-order and turbulent chaos; and
the lamp section of `Gnosis/Body/CityOnAHill.lean`, where brightness runs on the
order→disorder gradient, going dark only at flat equilibrium). The menstrual
cycle is one settled shape of that balance: an *oscillating order*, a sustained
rotation that never freezes. Menopause models the **scheduled re-settling of that
order/chaos balance into a different equilibrium**: the oscillating order gives
way to a *resting* order — the dynamics reach a fixed point and the phase ceases
to advance.

## The contrast with the never-settling cosmos

`Gnosis/Body/ClinamenOscillator.lean` (cited, not imported) proves the opposite
extreme for the *cosmos*: `cosmicStep_has_no_fixed_point` — existence never rests,
the clinamen `+1` always re-escapes the void, and the universe recurs forever
(`cosmos_has_period_two_orbit`). Menopause is the *local* counter-picture: a
specific oscillator that **does** reach a fixed point on schedule. This is not the
void and not death (the absorbing `0` of heat death in `ClinamenOscillator` is
reached only *without* the swerve); it models a *stable non-cycling regime* — the
dynamics settle and stay settled. The sibling scheduling/resilience spine is
`Gnosis/Body/SleepResilience.lean` (cited): infradian dynamics that withstand
load.

## Honest idealizations

* This is a pure-`Nat` **schedule + dynamics** idealization, **not** a hormonal
  model. There is no estrogen, FSH, LH, or follicular reserve here. "Menopause"
  is modelled only as: *the day-indexed phase dynamics cease to advance at a
  scheduled threshold*.
* "Equilibrium" means precisely *the dynamics reaching a fixed point* — a state
  `phaseAt` returns unchanged under stepping one more day (`phaseAt (day+1) =
  phaseAt day`). It carries no thermodynamic or hormonal content.
* The onset is an *idealized scheduled threshold* (`menopauseOnset`, a fixed
  multiple of `period`), not a stochastic biological event; we model the
  *structure* of "a scheduled transition to a fixed point", not its timing
  distribution.
* The settled phase is fixed to `0` (`postMenopauseState`). The choice of value is
  conventional; the content is that one phase is settled and absorbing.

## The arc, as theorems

1. `cycles_before_menopause` — before onset, the phase maps to the menstrual
   oscillator.
2. `settles_after_menopause` — at/after onset, the phase settles to the fixed
   equilibrium.
3. `menopause_is_a_fixed_point` — after onset the dynamics stop: stepping a day no
   longer changes the phase. **The fixed point.**
4. `equilibrium_absorbs_perturbation` — after onset, an arbitrary perturbation is
   absorbed; it does not restart cycling.
5. `scheduled_transition` — every day is on exactly one side of the single
   schedule (cycling, or settled), not random.
6. `menopause_is_the_scheduled_equilibrium` — the headline: cycling before the
   scheduled onset, a perturbation-absorbing fixed-point equilibrium after.

Rustic Church: `import Init` plus the menstrual-cycle bridge only. `Nat` only,
no Float/Real, no Mathlib, no `sorry`, no `simp`/`decide`/`omega` on open goals —
term-mode and named core `Nat` lemmas throughout.
-/

namespace Gnosis.Body.Menopause

open Gnosis.Body.MenstrualCycle

/-! ## 0. The schedule and the settled state

The reproductive span runs for a whole number of cycles, after which the dynamics
re-settle. We fix the onset to a concrete multiple of the menstrual `period`
(reusing `MenstrualCycle.period = 28`) so the schedule lines up with whole cycles.
`reproductiveCycles` cycles span `menopauseOnset` days; the canonical pick is
`35 * period` — an idealized end of the reproductive span, not a hormone model. -/

/-- The number of whole menstrual cycles in the (idealized) reproductive span. A
    schedule constant, not a measured biological figure. -/
def reproductiveCycles : Nat := 35

/-- **The scheduled menopause onset**, in days: a whole number of menstrual
    `period`s (`reproductiveCycles * period`). The phase dynamics cycle strictly
    before this day and rest at the equilibrium from this day on. This is an
    idealized scheduled threshold, **not** a hormonal event. -/
def menopauseOnset : Nat := reproductiveCycles * period

/-- The settled equilibrium phase the dynamics rest at after onset. Fixed to `0`;
    the value is conventional (one phase is settled and absorbing). -/
def postMenopauseState : Nat := 0

/-- The phase is *cycling* (in the reproductive, oscillating span) on a day when
    that day precedes the scheduled onset. -/
def isCycling (day : Nat) : Prop := day < menopauseOnset

/-- **The day-indexed phase dynamics.** Before the scheduled onset the phase is
    the menstrual oscillator `cyclePhase day` (the rotating dial of
    `MenstrualCycle`); at and after the onset it is the settled equilibrium
    `postMenopauseState`. This is the dynamical object whose fixed point models
    menopause. -/
def phaseAt (day : Nat) : Nat :=
  if day < menopauseOnset then cyclePhase day else postMenopauseState

/-! ## 1. Before the onset: the menstrual oscillator

On the reproductive side of the schedule the dynamics are *verbatim* the
`MenstrualCycle` oscillator — the same rotating, never-resting dial, with all of
its closure/boundedness/re-entrainment structure intact. -/

/-- **(THM 1) Cycling before menopause.** Before the scheduled onset the phase
    maps to the menstrual oscillator: `phaseAt day = cyclePhase day`. The
    reproductive span runs the robust oscillator of `MenstrualCycle`. (Via
    `if_pos` on the schedule guard.) -/
theorem cycles_before_menopause (day : Nat) (h : day < menopauseOnset) :
    phaseAt day = cyclePhase day := by
  unfold phaseAt
  exact if_pos h

/-- Before onset the phase still lies on the menstrual dial — the oscillator is
    fully intact in the reproductive span. (Reuses `phase_is_bounded`.) -/
theorem cycling_phase_is_bounded (day : Nat) (h : day < menopauseOnset) :
    phaseAt day < period := by
  rw [cycles_before_menopause day h]
  exact phase_is_bounded day

/-! ## 2. At and after the onset: the settled equilibrium

On the post-reproductive side the dynamics rest at a single phase. The guard
`day < menopauseOnset` fails exactly when `menopauseOnset ≤ day`, so the
dynamics select the equilibrium branch. -/

/-- **(THM 2) Settled after menopause.** At and after the scheduled onset the
    phase settles to the fixed equilibrium: `phaseAt day = postMenopauseState`.
    The cycling dial has been left behind for a single resting phase. (Via
    `if_neg` from `Nat.not_lt` on `menopauseOnset ≤ day`.) -/
theorem settles_after_menopause (day : Nat) (h : menopauseOnset ≤ day) :
    phaseAt day = postMenopauseState := by
  unfold phaseAt
  exact if_neg (Nat.not_lt.mpr h)

/-! ## 3. The fixed point — the dynamics stop advancing

The defining dynamical fact of menopause in this model: once settled, stepping
one more day does **not** change the phase. The phase ceases to advance — a
genuine fixed point of the day-to-day map, the exact opposite of the menstrual
oscillator (whose phase advances every day) and of the cosmos of
`ClinamenOscillator.cosmicStep_has_no_fixed_point` (which never rests). -/

/-- A scheduled onset already reached at `day` is still reached at `day + 1` —
    the post-menopause span is forward-closed. (`Nat.le_trans` with
    `day ≤ day + 1`.) -/
theorem onset_persists (day : Nat) (h : menopauseOnset ≤ day) :
    menopauseOnset ≤ day + 1 :=
  Nat.le_trans h (Nat.le_succ day)

/-- **(THM 3) Menopause maps to a fixed point.** After the scheduled onset the
    dynamics stop: stepping one more day leaves the phase unchanged,
    `phaseAt (day + 1) = phaseAt day`. Both sides settle to `postMenopauseState`.

    *Proof technique.* Pure rewriting to a common value, no order arithmetic on
    the goal: by `settles_after_menopause` the left side equals `postMenopauseState`
    (using `onset_persists` to carry the onset hypothesis forward from `day` to
    `day + 1`), and the right side equals `postMenopauseState` directly; the two
    rewrites collapse the goal to `rfl`. The phase no longer advances — a genuine
    fixed point of the day-step map. -/
theorem menopause_is_a_fixed_point (day : Nat) (h : menopauseOnset ≤ day) :
    phaseAt (day + 1) = phaseAt day := by
  rw [settles_after_menopause (day + 1) (onset_persists day h),
      settles_after_menopause day h]

/-! ## 4. The equilibrium absorbs perturbation

`MenstrualCycle.reentrains_after_perturbation` shows a perturbation `s` merely
*rotates* the still-spinning dial — the oscillator re-closes after a period. Here
the contrast is sharp: once at the fixed point, *any* perturbation is **absorbed**
— it does not restart cycling, the dynamics stay at the equilibrium. -/

/-- **(THM 4) The equilibrium absorbs perturbation.** After the scheduled onset,
    an arbitrary perturbation `s` (the post-menopause analogue of the stress /
    travel / illness shift of `MenstrualCycle.reentrains_after_perturbation`) does
    *not* restart cycling: `phaseAt (day + s) = postMenopauseState`. The
    perturbation is absorbed into the fixed point rather than rotating a dial.

    *Proof technique.* Reduce the perturbed day to the settled branch. From
    `menopauseOnset ≤ day` and `day ≤ day + s` (`Nat.le_add_right`), transitivity
    (`Nat.le_trans`) gives `menopauseOnset ≤ day + s`, so
    `settles_after_menopause` evaluates `phaseAt (day + s)` to
    `postMenopauseState` directly — the shift never re-enters the cycling branch.
    Contrast `reentrains_after_perturbation`, where the perturbed day stays *on*
    the spinning dial; here it stays *in* the fixed point. -/
theorem equilibrium_absorbs_perturbation (day s : Nat) (h : menopauseOnset ≤ day) :
    phaseAt (day + s) = postMenopauseState :=
  settles_after_menopause (day + s) (Nat.le_trans h (Nat.le_add_right day s))

/-! ## 5. The transition is a single schedule, not random

Menopause in this model is not a stochastic flip but a single scheduled
threshold. Every day lies on exactly one side of `menopauseOnset`: still cycling,
or already settled — a clean dichotomy over the schedule. -/

/-- **(THM 5) The scheduled transition.** Every day is on exactly one side of the
    single scheduled threshold: still cycling (`isCycling day`, i.e.
    `day < menopauseOnset`) or already settled (`menopauseOnset ≤ day`). The
    transition is a deterministic schedule, not a random event. (Via
    `Nat.lt_or_ge`.) -/
theorem scheduled_transition (day : Nat) :
    isCycling day ∨ menopauseOnset ≤ day :=
  Nat.lt_or_ge day menopauseOnset

/-- **The oscillator stops (existence form).** There *exists* a scheduled onset
    past which the dynamics rest at a fixed point forever: for every day at or
    after it, stepping a day no longer changes the phase. The witness is
    `menopauseOnset`; the fixed-point property is `menopause_is_a_fixed_point`.
    This is the local counter-picture to
    `ClinamenOscillator.cosmicStep_has_no_fixed_point`, where existence never
    rests. -/
theorem the_oscillator_stops :
    ∃ onset : Nat, ∀ day : Nat, onset ≤ day → phaseAt (day + 1) = phaseAt day :=
  ⟨menopauseOnset, fun day h => menopause_is_a_fixed_point day h⟩

/-! ## 6. The headline synthesis -/

/-- **Menopause maps to the scheduled equilibrium.** The complement of
    `MenstrualCycle.menstrual_cycle_is_a_robust_oscillator`, composed: the cycling
    oscillator re-settles, on a single schedule, into a non-cycling fixed-point
    equilibrium. For every day before the onset, every day at/after it, and every
    perturbation `s`:

    * (cycling) before the scheduled onset the phase maps to the menstrual
      oscillator — the robust rotating dial of `MenstrualCycle`
      (`phaseAt cd = cyclePhase cd`);
    * (settled) at/after onset the phase settles to the fixed equilibrium
      (`phaseAt md = postMenopauseState`);
    * (fixed point) after onset the dynamics stop advancing
      (`phaseAt (md + 1) = phaseAt md`) — the genuine fixed point, opposite the
      never-resting cosmos of `ClinamenOscillator`;
    * (absorption) after onset a perturbation is absorbed, not re-cycled
      (`phaseAt (md + s) = postMenopauseState`);
    * (schedule) every day is on exactly one side of the single threshold —
      cycling or settled, deterministically.

    Bundled so the five pictures are provably one transition: the order/chaos
    balance re-settles from *oscillating order* (the cycle) into a *new resting
    equilibrium* (the fixed point). Honest scope: a `Nat` schedule/dynamics
    idealization — the phase ceasing to advance — not a hormonal model. -/
theorem menopause_is_the_scheduled_equilibrium
    (cd md s : Nat) (hc : cd < menopauseOnset) (hm : menopauseOnset ≤ md) :
    -- 1. cycling: the robust oscillator before the scheduled onset
    phaseAt cd = cyclePhase cd ∧
    -- 2. settled: the fixed equilibrium at/after the onset
    phaseAt md = postMenopauseState ∧
    -- 3. fixed point: after onset the dynamics stop advancing
    phaseAt (md + 1) = phaseAt md ∧
    -- 4. absorption: a perturbation is absorbed into the equilibrium
    phaseAt (md + s) = postMenopauseState ∧
    -- 5. schedule: every day is on exactly one side of the single threshold
    (isCycling md ∨ menopauseOnset ≤ md) :=
  ⟨cycles_before_menopause cd hc,
   settles_after_menopause md hm,
   menopause_is_a_fixed_point md hm,
   equilibrium_absorbs_perturbation md s hm,
   scheduled_transition md⟩

end Gnosis.Body.Menopause
