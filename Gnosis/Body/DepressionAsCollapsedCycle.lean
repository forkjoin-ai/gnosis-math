import Init
import Gnosis.Body.RedQueen
import Gnosis.Body.Allostasis

/-!
# Depression as a Collapsed Limit Cycle

This module models depression not as a defect but as a *dynamical regime*: the
**collapse of a healthy limit cycle**. A flourishing affective system oscillates
— it rises and falls, engages and rests, the way `Gnosis.Body.RedQueen`'s
predator–prey system runs a sustained period-2 orbit (`has_period_two_orbit`).
Depression is what happens when that oscillation is *damped to zero*: the
amplitude is driven down step by step until the cycle dies into a flat fixed
point. Flatness and anhedonia are that dead fixed point — the oscillation has
stopped, not because the system is broken in some moral sense, but because the
damping has overwhelmed the drive. Recovery, symmetrically, is the *restoration*
of the oscillation: a restoring drive (eustress, treatment, connection) revives
the amplitude and lets the cycle run again.

This bridges three threads in the repo:

* `Gnosis.DepressionAsDampedOscillation` (not Init-clean; cited only here) frames
  depression as suppressed positive interference and accelerated decay of
  positive emotional energy — low amplitude, energy bleeding away. This module
  gives that framing a clean dynamical-systems skeleton in `Nat`: damping as
  amplitude subtraction, the flat fixed point as `amplitude = 0`.
* `Gnosis.Body.RedQueen` supplies the *healthy* counterpart — a sustained
  period-2 oscillation (`RedQueen.has_period_two_orbit`) that no fixed point can
  absorb. Health is the live cycle; depression is its damped collapse to the dead
  fixed point.
* `Gnosis.Body.Allostasis` supplies the *restoring step* (`Allostasis.recover`):
  the same truncated-`Nat.sub` return-toward-setpoint dynamic. Here a restoring
  *drive* is its dual — addition that revives amplitude — and chronic load is
  what drives the damping.

The arc, as theorems:

1. **Damping never raises amplitude** — `damping_lowers_amplitude`.
2. **Enough damping collapses to flat** — `enough_damping_collapses_to_flat`:
   sufficient damping zeroes the oscillation (anhedonia / the dead fixed point).
   This is a collapse of dynamics, not a failure of will.
3. **Flat is a fixed point** — `flat_is_a_fixed_point`: zero amplitude is
   absorbing; the depressive fixed point persists without drive.
4. **Drive revives amplitude** — `drive_revives_amplitude`: any positive drive
   strictly increases amplitude.
5. **Recovery escapes the fixed point** — `recovery_escapes_the_fixed_point`:
   from zero amplitude, a unit of drive gives positive amplitude; the flat state
   is escapable.
6. **Health is the sustained cycle** — `health_is_the_sustained_cycle`: a healthy
   system sustains its oscillation (cites `RedQueen.has_period_two_orbit`);
   depression is its damped collapse to the flat fixed point.
7. **Headline** — `depression_is_collapsed_oscillation`: damping collapses the
   cycle to a flat fixed point, which is absorbing without drive, but a restoring
   drive revives it.

Respectful framing throughout: depression is a *regime* of a dynamical system —
the cycle running down — not a moral defect. The system that can collapse is the
same system that can be revived; the dead fixed point is escapable with drive.

Rustic Church: `import Init` only, plus the Init-clean sibling Body modules
`RedQueen` and `Allostasis` (the latter transitively pulls in the Init-clean
`Robustness` and `Anthropogenesis`). `Nat` only — no Float/Real, no Mathlib. No
`sorry`; no `simp`/`decide`/`omega` on open goals. Proofs are term-mode and named
core `Nat` lemmas.
-/

namespace Gnosis.Body.DepressionAsCollapsedCycle

open Gnosis.Body.RedQueen
open Gnosis.Body.Allostasis

/-! ## 1. The oscillation and its two forces

We model the affective oscillation by a single `Nat` **amplitude** — how much the
system swings, how much it engages, how alive the cycle is. Two opposing forces
act on it each step:

* **Damping** subtracts from amplitude (truncated at `0`): the energy bleed of
  `DepressionAsDampedOscillation`, the accelerated decay of positive patterns.
* **Drive** adds to amplitude: a restoring push — eustress, treatment,
  connection — the additive dual of `Allostasis.recover`'s subtractive return.

The **dead fixed point** is `amplitude = 0`: a flat affect, anhedonia, the cycle
stopped. -/

/-- **One damping step.** Damping removes up to `damping` units of `amplitude`,
    truncated at `0`. This is the energy-bleed of depression: each step the
    oscillation swings a little less. Mirrors `Allostasis.recover`'s truncated
    `Nat.sub`, but here the subtraction is the *pathology* (the cycle running
    down), not the cure. -/
def dampStep (amplitude damping : Nat) : Nat := amplitude - damping

/-- **One drive step.** A restoring drive *adds* to amplitude: the oscillation
    swings a little more. The additive dual of `dampStep` — eustress, treatment,
    or connection feeding energy back into the cycle. -/
def driveStep (amplitude drive : Nat) : Nat := amplitude + drive

/-- The dead fixed point of the collapsed cycle: zero amplitude — flat affect,
    anhedonia, the oscillation stopped. Named so the theorems can speak of it
    directly. -/
def flat : Nat := 0

/-! ## 2. Damping lowers amplitude; enough of it collapses the cycle -/

/-- **(THM 1) Damping never raises amplitude.** A damping step can only ever
    lower the swing of the oscillation (truncated subtraction is monotone
    downward). Whatever the damping, the cycle does not grow under it. Mirrors
    `Allostasis.recover_le_deviation` structurally (`Nat.sub_le`). -/
theorem damping_lowers_amplitude (amplitude damping : Nat) :
    dampStep amplitude damping ≤ amplitude :=
  Nat.sub_le amplitude damping

/-- **(THM 2) Enough damping collapses the cycle to flat.** When the damping
    meets or exceeds the current amplitude, one step takes the oscillation all
    the way to `0`: the cycle dies into the flat fixed point. This is anhedonia —
    the dead fixed point of depression — and the framing matters: it is the
    *collapse of a dynamical regime*, the damping having overwhelmed the swing,
    not a moral failing or a deficiency of effort. Mirrors
    `Allostasis.full_recovery_clears_deviation` (`Nat.sub_eq_zero_of_le`), but
    here reaching zero is the loss of the cycle, not its cure. -/
theorem enough_damping_collapses_to_flat {amplitude damping : Nat}
    (hCollapse : amplitude ≤ damping) : dampStep amplitude damping = 0 :=
  Nat.sub_eq_zero_of_le hCollapse

/-- **(THM 3) Flat is a fixed point.** Zero amplitude is *absorbing*: once the
    cycle has collapsed, any further damping leaves it at `0`. With no restoring
    drive, the depressive fixed point persists — the system stays flat. This is
    why depression, untreated, does not lift on its own: the dead fixed point is
    stable under the very force that produced it. -/
theorem flat_is_a_fixed_point (damping : Nat) : dampStep flat damping = 0 := by
  unfold dampStep flat
  -- 0 - damping = 0
  exact Nat.sub_eq_zero_of_le (Nat.zero_le damping)

/-! ## 3. Drive revives the oscillation; recovery escapes the fixed point -/

/-- **(THM 4) A restoring drive revives the amplitude.** Any *positive* drive
    strictly increases the amplitude of the oscillation: the cycle swings wider
    than before. A restoring push — eustress, treatment, connection — does not
    merely hold the line; it strictly revives the dynamics. The additive dual of
    `Allostasis.recover`'s subtractive return toward setpoint. -/
theorem drive_revives_amplitude {amplitude drive : Nat}
    (hDrive : 0 < drive) : amplitude < driveStep amplitude drive := by
  unfold driveStep
  exact Nat.lt_add_of_pos_right hDrive

/-- **(THM 5) Recovery escapes the flat fixed point.** From the dead fixed point
    (`amplitude = 0`), a single unit of restoring drive yields *positive*
    amplitude: the oscillation begins again. The flat state is absorbing under
    damping (THM 3) but it is **not** a trap — it is escapable the moment any
    drive is supplied. This is the formal hope in the model: the same system that
    collapsed can be revived. -/
theorem recovery_escapes_the_fixed_point {drive : Nat}
    (hDrive : 0 < drive) : 0 < driveStep flat drive := by
  unfold driveStep flat
  -- 0 < 0 + drive
  rw [Nat.zero_add]
  exact hDrive

/-! ## 4. Health is the sustained cycle; depression is its collapse -/

/-- A system is **alive** (its cycle running) when its amplitude is positive — it
    still swings. -/
def aliveCycle (amplitude : Nat) : Prop := 0 < amplitude

/-- A system is **collapsed** (at the dead fixed point) when its amplitude is
    zero — flat affect, anhedonia, no swing left. -/
def collapsedCycle (amplitude : Nat) : Prop := amplitude = 0

/-- A live cycle and the collapsed fixed point are genuine opposites: the
    amplitude cannot be both positive and zero. The live oscillation of health
    and the dead fixed point of depression are distinct dynamical states, not a
    matter of degree at the boundary. -/
theorem alive_excludes_collapsed {amplitude : Nat}
    (hAlive : aliveCycle amplitude) : ¬ collapsedCycle amplitude := by
  unfold aliveCycle at hAlive
  unfold collapsedCycle
  intro hCollapse
  -- hAlive : 0 < amplitude, hCollapse : amplitude = 0 ⟹ 0 < 0, contradiction
  rw [hCollapse] at hAlive
  exact Nat.lt_irrefl 0 hAlive

/-- **(THM 6) Health is the sustained cycle; depression is its damped collapse.**
    A *healthy* affective system sustains its oscillation — exactly the
    structural signature of `RedQueen.has_period_two_orbit`, a genuine period-2
    orbit that moves under one step and returns under two, never settling into a
    fixed point (`RedQueen.step s₀ ≠ s₀ ∧ RedQueen.step (RedQueen.step s₀) = s₀`).
    *Depression* is the contrasting regime: the amplitude of the oscillation has
    been damped to the flat fixed point (`dampStep amplitude damping = 0` once
    `amplitude ≤ damping`), so the cycle no longer swings. The same dynamical
    vocabulary describes both — the live cycle of health and the dead fixed point
    of depression are two regimes of one oscillating system. -/
theorem health_is_the_sustained_cycle {amplitude damping : Nat}
    (hCollapse : amplitude ≤ damping) :
    -- Health: the Red Queen cycle is sustained — moves under one step, returns
    -- under two (a real, never-settling oscillation).
    (RedQueen.step RedQueen.s₀ ≠ RedQueen.s₀ ∧
      RedQueen.step (RedQueen.step RedQueen.s₀) = RedQueen.s₀) ∧
    -- Depression: this oscillation, damped, collapses to the flat fixed point.
    (dampStep amplitude damping = 0) :=
  ⟨RedQueen.has_period_two_orbit, enough_damping_collapses_to_flat hCollapse⟩

/-! ## 5. The headline synthesis -/

/-- **(HEADLINE) Depression is a collapsed oscillation.** The whole arc composed
    into one statement, contrasting the live cycle of health with the dead fixed
    point of depression and the road back:

    1. **Health sustains the cycle** — the Red Queen oscillation moves under one
       step and returns under two (`RedQueen.has_period_two_orbit`): a real,
       never-settling limit cycle.
    2. **Damping collapses it to flat** — once damping meets the amplitude, one
       step zeroes the oscillation (`dampStep amplitude damping = 0`): anhedonia,
       the dead fixed point. A collapse of dynamics, not a defect of character.
    3. **Flat is absorbing without drive** — the collapsed state is a fixed point
       under further damping (`dampStep flat damping' = 0`): untreated, it
       persists.
    4. **But drive revives it** — any positive drive strictly increases amplitude
       (`amplitude' < driveStep amplitude' drive`), and from the flat fixed point
       a unit of drive gives positive amplitude (`0 < driveStep flat drive`): the
       cycle restarts. The dead fixed point is escapable.

    Depression is therefore the *collapse* of a healthy limit cycle — the
    oscillation damped to a flat fixed point — and recovery is the *restoration*
    of that oscillation by a restoring drive. A dynamical regime, with a way
    back. -/
theorem depression_is_collapsed_oscillation
    {amplitude damping : Nat} (hCollapse : amplitude ≤ damping)
    (damping' : Nat)
    {amplitude' drive : Nat} (hDrive : 0 < drive) :
    -- 1. Health: the cycle is sustained (a real, never-settling oscillation).
    (RedQueen.step RedQueen.s₀ ≠ RedQueen.s₀ ∧
      RedQueen.step (RedQueen.step RedQueen.s₀) = RedQueen.s₀) ∧
    -- 2. Damping collapses the cycle to the flat fixed point (anhedonia).
    (dampStep amplitude damping = 0) ∧
    -- 3. Flat is absorbing without drive (the depressive fixed point persists).
    (dampStep flat damping' = 0) ∧
    -- 4. Drive revives amplitude, and the flat fixed point is escapable.
    (amplitude' < driveStep amplitude' drive ∧ 0 < driveStep flat drive) :=
  ⟨RedQueen.has_period_two_orbit,
   enough_damping_collapses_to_flat hCollapse,
   flat_is_a_fixed_point damping',
   ⟨drive_revives_amplitude hDrive, recovery_escapes_the_fixed_point hDrive⟩⟩

end Gnosis.Body.DepressionAsCollapsedCycle
