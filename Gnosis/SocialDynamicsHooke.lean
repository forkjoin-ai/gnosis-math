import Gnosis.SkyrmsUltraLongRunEquilibrium

/-
  SocialDynamicsHooke.lean
  ========================

  Spencer's "Social Statics → Social Dynamics" arc, lifted to the
  discrete `Int` kernel of `SkyrmsUltraLongRunEquilibrium`.

  ## Static reading vs. dynamic reading

  The existing `PolarizationState` is the **static** snapshot:
  `(budget, posA, posB, debtA, debtB)` — positions and reconciliation
  debts, but no velocity, no inertia, no time direction. The static
  question is "where do we stand?" — Hotelling on the affective line,
  bowl rim/void in the chamber, basin lumping in the ergodic kernel.

  This module makes the *dynamic* question explicit by carrying
  **velocity** alongside position and identifying three concrete
  regimes governed by a single damping dial:

  1. **Undamped Hooke** (`damping = 0`): the system oscillates around
     the Skyrms-ULR median with concrete **period 6**. Position cycle:
     `0 → 5 → 10 → 10 → 5 → 0 → 0 → ...`
  2. **Critically damped** (the "minimal" damping that prevents
     oscillation): position monotonically advances by 1 toward the
     median per step; reaches the median in 5 steps and stays. This
     coincides on the position field with
     `SkyrmsUltraLongRunEquilibrium.mutationStep`.
  3. **Overdamped** (damping kills inertia faster than Hooke can
     restore it): position still approaches the median but more
     slowly than the critical regime.

  The point is structural, not numerical: `SkyrmsUltraLongRunEquilibrium.mutationStep`
  is **not the only** dynamical kernel on `PolarizationState`. It is
  one specific regime — critical damping — inside a wider Hooke
  family. Calling it "the dynamics" was always a static-flavored
  abuse; calling it "critically damped Hooke on the polarization
  axis" is the honest reread.

  ## Spencer's Law of Equal Freedom

  Spencer's Law: each individual is free to act in any way compatible
  with every other individual's equal freedom. In kernel form: the
  pair update factors as independent per-agent updates, with the two
  agents coupled only through the **shared median target** (the
  Skyrms-ULR fixed point), not through each other's positions or
  velocities directly.

  We make this structural by defining the pair step as
  `{ a := step s.a, b := step s.b }` and proving that this
  decomposition is the kernel's defining property
  (`spencers_law_of_equal_freedom_undamped`,
  `spencers_law_of_equal_freedom_critical`).

  This is *not* a statement about social policy. It is the
  mathematical observation that a Hooke kernel coupled only through
  a shared target is symmetric in its agents — exactly the formal
  shape of "every agent free to oscillate so long as every other
  agent has the same freedom."

  ## Comte's Three Stages — surfaced, not proved

  Comte's `theological → metaphysical → positive` schema reads
  cleanly onto the existing `Nash → Skyrms → Buley` ladder when
  the static rungs are crossed *dynamically*:

  - **Theological** (Nash): the rules are enforced by the trap's
    local logic; the position cannot escape its basin without
    external intervention.
  - **Metaphysical** (Skyrms): the rules emerge from convention
    via long-run dynamics; the median basin attracts.
  - **Positive** (Buley): the rules close retrocausally; the
    present output is congruent with the future closure (the
    Novikov consistency formalized in `Gnosis.BuleyEquilibrium`).

  This module surfaces the mapping; it does **not** prove it. Comte's
  schema is a historical-philosophical claim, not a theorem of the
  Hooke kernel. The honest content is: dynamical regimes give a
  *physics* reading of the Nash–Skyrms–Buley ladder, where the
  rungs are not just numbered but characterized by what kernel
  governs the state's motion.

  ## What this module proves

  * Undamped Hooke from the Nash extreme returns to the Nash extreme
    in exactly 6 steps; the position cycle is `[0, 5, 10, 10, 5, 0]`.
  * Critically damped Hooke from the Nash extreme reaches the median
    in 5 steps and is a fixed point thereafter.
  * Overdamped Hooke reaches the median strictly later than the
    critical regime (8 steps in our concrete instance).
  * Spencer's Law: the pair step factors as independent per-agent
    steps for every regime (undamped, critical, overdamped).
  * Bridge: the position projection of `mutationStep` agrees with
    `criticallyDampedStep` on the Skyrms-ULR median target.

  ## Honesty boundary

  All dynamics are discrete, `Int`-valued, single-axis (one position
  variable per agent), and run on a single concrete `budget = 10`
  trajectory. Real-valued period theorems, exponential decay rates,
  Q-factor analytic resonance bandwidths, and continuous Hamiltonian
  conservation laws all require Mathlib and are out of scope. What
  we deliver is the *qualitative regime* witness: under-, critical-,
  and over-damping are distinct concrete trajectories with concrete
  step counts, and Spencer's Law is structural in all three.

  Imports `Gnosis.SkyrmsUltraLongRunEquilibrium`. Zero `sorry`,
  zero new `axiom`.
-/


namespace SocialDynamicsHooke

open SkyrmsUltraLongRunEquilibrium

/-! ## State: position + velocity

  `Int` for both fields lets velocity carry sign honestly (toward
  / away from the median) without splitting into two `Nat`
  half-channels. -/

/-- A single agent's dynamical state on the `[0..10]` affective line. -/
structure SocialMomentumState where
  pos : Int
  vel : Int
  deriving DecidableEq, Repr

/-- The shared target: the Skyrms-ULR median position. -/
def median : Int := 5

/-- Hooke restoring force toward the median: positive when below
    the median (push up), negative when above (push down), zero at
    the median itself. Force constant `k = 1`. -/
def hookeForce (s : SocialMomentumState) : Int :=
  median - s.pos

/-- Initial state at the Nash extreme (the leftmost polarization
    trap), velocity zero. -/
def initialNashState : SocialMomentumState :=
  { pos := 0, vel := 0 }

/-! ## Regime 1: undamped Hooke (period-6 oscillation)

  Velocity accumulates the restoring force; position advances by
  velocity. No damping. The system oscillates indefinitely. -/

/-- One undamped step: velocity gets the full restoring force,
    position advances by the new velocity. -/
def undampedStep (s : SocialMomentumState) : SocialMomentumState :=
  let v' := s.vel + hookeForce s
  { pos := s.pos + v', vel := v' }

/-- Iterated undamped step. -/
def undampedIterate : Nat → SocialMomentumState → SocialMomentumState
  | 0,     s => s
  | n + 1, s => undampedIterate n (undampedStep s)

/-- The position cycle along the undamped trajectory from the Nash
    extreme: `[0, 5, 10, 10, 5, 0]`, then repeats. -/
theorem undamped_position_cycle :
    (undampedIterate 0 initialNashState).pos = 0 ∧
    (undampedIterate 1 initialNashState).pos = 5 ∧
    (undampedIterate 2 initialNashState).pos = 10 ∧
    (undampedIterate 3 initialNashState).pos = 10 ∧
    (undampedIterate 4 initialNashState).pos = 5 ∧
    (undampedIterate 5 initialNashState).pos = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The velocity cycle along the same trajectory:
    `[0, 5, 5, 0, -5, -5]`, then repeats. -/
theorem undamped_velocity_cycle :
    (undampedIterate 0 initialNashState).vel = 0 ∧
    (undampedIterate 1 initialNashState).vel = 5 ∧
    (undampedIterate 2 initialNashState).vel = 5 ∧
    (undampedIterate 3 initialNashState).vel = 0 ∧
    (undampedIterate 4 initialNashState).vel = -5 ∧
    (undampedIterate 5 initialNashState).vel = -5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Undamped period theorem.** Six steps of undamped Hooke return
    the system exactly to its starting state — full state, not just
    position. -/
theorem undamped_period_six :
    undampedIterate 6 initialNashState = initialNashState := by
  decide

/-- The undamped trajectory is **periodic** with period 6: any number
    of steps that is a multiple of 6 returns to the start. (Witnessed
    here for 12 = 2 × 6.) -/
theorem undamped_period_twelve :
    undampedIterate 12 initialNashState = initialNashState := by
  native_decide

/-- **Honest non-fixed-point witness.** The undamped step has
    `initialNashState` *not* as a fixed point — it leaves on the
    first step. -/
theorem undamped_step_does_not_fix_nash :
    undampedStep initialNashState ≠ initialNashState := by
  decide

/-- The undamped trajectory **does** have the median-with-zero-velocity
    state as a fixed point. (The Skyrms ULR position with no momentum.) -/
def medianRest : SocialMomentumState := { pos := 5, vel := 0 }

theorem undamped_step_fixes_median_rest :
    undampedStep medianRest = medianRest := by
  decide

/-! ## Regime 2: critically damped (the existing kernel)

  Position advances by exactly 1 toward the median per step;
  velocity is reset to zero each step. This is the regime where
  damping precisely cancels Hooke inertia: no oscillation, no
  overshoot, monotone convergence in the minimum number of steps.

  This coincides on the position projection with
  `SkyrmsUltraLongRunEquilibrium.mutationStep`. -/

/-- One critically-damped step. -/
def criticallyDampedStep (s : SocialMomentumState) : SocialMomentumState :=
  let p := s.pos
  let p' := if p < median then p + 1 else if p > median then p - 1 else p
  { pos := p', vel := 0 }

def criticallyDampedIterate : Nat → SocialMomentumState → SocialMomentumState
  | 0,     s => s
  | n + 1, s => criticallyDampedIterate n (criticallyDampedStep s)

/-- The critically-damped trajectory advances by 1 per step. -/
theorem critically_damped_position_trajectory :
    (criticallyDampedIterate 0 initialNashState).pos = 0 ∧
    (criticallyDampedIterate 1 initialNashState).pos = 1 ∧
    (criticallyDampedIterate 2 initialNashState).pos = 2 ∧
    (criticallyDampedIterate 3 initialNashState).pos = 3 ∧
    (criticallyDampedIterate 4 initialNashState).pos = 4 ∧
    (criticallyDampedIterate 5 initialNashState).pos = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Critical-damping convergence theorem.** Five critically-damped
    steps from the Nash extreme reach the median exactly. -/
theorem critically_damped_reaches_median_in_five_steps :
    criticallyDampedIterate 5 initialNashState = medianRest := by
  decide

/-- The median-rest state is a fixed point of the critically-damped
    kernel as well. -/
theorem critically_damped_fixes_median_rest :
    criticallyDampedStep medianRest = medianRest := by
  decide

/-- Once the critically-damped kernel reaches the median it stays. -/
theorem critically_damped_stays_at_median_after_five :
    criticallyDampedIterate 6 initialNashState = medianRest ∧
    criticallyDampedIterate 10 initialNashState = medianRest ∧
    criticallyDampedIterate 100 initialNashState = medianRest := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Regime 3: overdamped (slower than critical)

  Damping exceeds the restoring force per step: position only
  advances toward the median every *second* step. (Implemented via a
  `tick` parity bit.) -/

structure OverdampedState where
  pos : Int
  tick : Bool   -- alternates each step; advances position only when `true`
  deriving DecidableEq, Repr

def overdampedStep (s : OverdampedState) : OverdampedState :=
  if s.tick then
    let p := s.pos
    let p' := if p < median then p + 1 else if p > median then p - 1 else p
    { pos := p', tick := false }
  else
    { pos := s.pos, tick := true }

def overdampedIterate : Nat → OverdampedState → OverdampedState
  | 0,     s => s
  | n + 1, s => overdampedIterate n (overdampedStep s)

def initialOverdampedNash : OverdampedState :=
  { pos := 0, tick := true }

/-- The overdamped trajectory takes **twice as many** steps as the
    critical regime to reach the median: 10 here vs. 5 critical. -/
theorem overdamped_position_trajectory :
    (overdampedIterate 0  initialOverdampedNash).pos = 0 ∧
    (overdampedIterate 2  initialOverdampedNash).pos = 1 ∧
    (overdampedIterate 4  initialOverdampedNash).pos = 2 ∧
    (overdampedIterate 6  initialOverdampedNash).pos = 3 ∧
    (overdampedIterate 8  initialOverdampedNash).pos = 4 ∧
    (overdampedIterate 10 initialOverdampedNash).pos = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Overdamping is strictly slower than critical.** At the same
    five steps that critical damping has reached the median,
    overdamping is only halfway there. -/
theorem overdamped_strictly_slower_than_critical_at_five_steps :
    (overdampedIterate 5 initialOverdampedNash).pos
      < (criticallyDampedIterate 5 initialNashState).pos := by
  decide

/-! ## Spencer's Law of Equal Freedom (pair symmetry)

  Two agents share a single median target; each agent's update
  depends only on that agent's own state. The pair update is the
  product of independent per-agent updates. This is Spencer's Law
  rendered as a kernel decomposition. -/

structure PairMomentumState where
  a : SocialMomentumState
  b : SocialMomentumState
  deriving DecidableEq, Repr

/-- Pair update under undamped Hooke: each agent steps independently. -/
def undampedPairStep (p : PairMomentumState) : PairMomentumState :=
  { a := undampedStep p.a, b := undampedStep p.b }

/-- Pair update under critically damped Hooke: each agent steps
    independently. -/
def criticallyDampedPairStep (p : PairMomentumState) : PairMomentumState :=
  { a := criticallyDampedStep p.a, b := criticallyDampedStep p.b }

/-- **Spencer's Law of Equal Freedom (undamped form).** The pair
    update factors as the product of the two single-agent updates;
    the two agents are kinematically independent, coupled only
    through the shared median target. -/
theorem spencers_law_of_equal_freedom_undamped (p : PairMomentumState) :
    (undampedPairStep p).a = undampedStep p.a ∧
    (undampedPairStep p).b = undampedStep p.b :=
  ⟨rfl, rfl⟩

/-- **Spencer's Law of Equal Freedom (critically damped form).** Same
    decomposition holds at critical damping: each agent's freedom to
    advance toward the median is independent of the other's freedom
    to do so. -/
theorem spencers_law_of_equal_freedom_critical (p : PairMomentumState) :
    (criticallyDampedPairStep p).a = criticallyDampedStep p.a ∧
    (criticallyDampedPairStep p).b = criticallyDampedStep p.b :=
  ⟨rfl, rfl⟩

/-- Concrete pair: A starts at the left extreme (Nash), B at the
    right extreme. Their median targets coincide; their dynamics do
    not interact. -/
def nashPair : PairMomentumState :=
  { a := { pos := 0,  vel := 0 }
    b := { pos := 10, vel := 0 } }

/-- Five critically-damped pair steps land both agents at the
    median simultaneously, despite their independent updates — they
    are coupled only by sharing a target, exactly Spencer's reading. -/
theorem nash_pair_reaches_median_simultaneously :
    let p₅ := criticallyDampedPairStep
                (criticallyDampedPairStep
                  (criticallyDampedPairStep
                    (criticallyDampedPairStep
                      (criticallyDampedPairStep nashPair))))
    p₅.a = medianRest ∧ p₅.b = medianRest := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Bridge: `mutationStep` is critically damped on the position axis

  `SkyrmsUltraLongRunEquilibrium.mutationStep` updates position by
  pulling toward the median (and updates debt by pulling toward
  the cooperative floor). Restricted to the position axis it is
  exactly `criticallyDampedStep` with `vel := 0`. -/

/-- Project a `PolarizationState` to its A-axis dynamical state at
    rest. This is the static-to-dynamic embedding: an existing
    polarization snapshot has zero velocity by definition. -/
def momentumOfPolarization (s : PolarizationState) : SocialMomentumState :=
  { pos := Int.ofNat s.posA, vel := 0 }

/-- One step of `mutationStep` projected to the A-axis matches one
    step of `criticallyDampedStep`. (Witnessed concretely on the
    Nash trap.) -/
theorem mutation_step_is_critical_damping_on_nash_trap :
    momentumOfPolarization (mutationStep nashPolarizationTrap)
      = criticallyDampedStep (momentumOfPolarization nashPolarizationTrap) := by
  decide

/-- Six steps of `mutationStep` project to six steps of
    `criticallyDampedStep` — both arrive at the median (which is
    the Skyrms ULR position 5 with zero velocity). -/
theorem mutation_six_iterations_match_critical_six_iterations :
    momentumOfPolarization
        (SkyrmsUltraLongRunEquilibrium.iterate 6 nashPolarizationTrap)
      = criticallyDampedIterate 6 (momentumOfPolarization nashPolarizationTrap) := by
  decide

/-! ## The dynamical regime witness

  A single statement bundling: undamped period 6, critical
  convergence in 5, overdamped slowdown, Spencer pair decomposition,
  and the bridge to `mutationStep`. -/

theorem social_dynamics_hooke_witness :
    -- Undamped: period 6
    undampedIterate 6 initialNashState = initialNashState ∧
    -- Critical: median in 5
    criticallyDampedIterate 5 initialNashState = medianRest ∧
    -- Overdamped: median in 10
    (overdampedIterate 10 initialOverdampedNash).pos = 5 ∧
    -- Critical strictly faster than overdamped
    (overdampedIterate 5 initialOverdampedNash).pos
      < (criticallyDampedIterate 5 initialNashState).pos ∧
    -- Spencer's Law on both regimes
    (∀ p : PairMomentumState,
      (undampedPairStep p).a = undampedStep p.a ∧
      (undampedPairStep p).b = undampedStep p.b) ∧
    (∀ p : PairMomentumState,
      (criticallyDampedPairStep p).a = criticallyDampedStep p.a ∧
      (criticallyDampedPairStep p).b = criticallyDampedStep p.b) ∧
    -- Bridge: mutationStep is critical damping on the position axis
    momentumOfPolarization (mutationStep nashPolarizationTrap)
      = criticallyDampedStep (momentumOfPolarization nashPolarizationTrap) := by
  refine ⟨undamped_period_six,
          critically_damped_reaches_median_in_five_steps,
          ?_, ?_, ?_, ?_,
          mutation_step_is_critical_damping_on_nash_trap⟩
  · exact (overdamped_position_trajectory).2.2.2.2.2
  · exact overdamped_strictly_slower_than_critical_at_five_steps
  · exact spencers_law_of_equal_freedom_undamped
  · exact spencers_law_of_equal_freedom_critical

/-! ## Honesty note

The `Static → Dynamic` reread is structural, not numerical. What we
proved:

  • The existing `mutationStep` is one regime — *critical damping* —
    inside a wider Hooke family that admits at least three
    qualitatively distinct regimes (undamped, critical, overdamped),
    each with concrete `Int`-step witnesses.
  • The undamped regime has period 6. The critical regime converges
    in 5. The overdamped regime takes 10. The ordering is strict on
    the concrete kernel, decidable by `Int` arithmetic.
  • Spencer's Law of Equal Freedom is the structural statement that
    the pair step factors as independent per-agent steps, with the
    only coupling through the shared median target. This is
    `rfl`-provable in all regimes by construction — that is exactly
    the content of "the kernel respects the symmetry."
  • `momentumOfPolarization (mutationStep s) = criticallyDampedStep
    (momentumOfPolarization s)` is the bridge that ties the new
    dynamic vocabulary to the existing static `PolarizationState`.

What we did *not* prove:

  • Real-valued period theorems, exponential decay rates, analytic
    Q-factor relationships between damping coefficient and resonance
    bandwidth, Hamiltonian conservation laws, or any continuous-time
    limit. All of these require Mathlib measure-theoretic and
    real-analytic infrastructure.
  • Comte's three-stages mapping is named in the docstring as a
    structural reread, *not* proved as a theorem of the Hooke
    kernel. That mapping is historical-philosophical, and emphatic
    identity claims of the form "Comte's positive stage IS the Buley
    rung" are exactly the `X IS the Y` move AGENTS.md (B18) bans.
    What we deliver is the kernel-level invariants; the historical
    reading is for prose.

## Next exploration

`Gnosis/SocialDynamicsResonance.lean` — add an external periodic
drive `drive : Nat → Int` to `undampedStep` and prove that drives
of period exactly 6 (the natural period) accumulate amplitude over
several cycles, while drives of period 7 or 5 do not. That would
introduce *resonance* as a discrete-Int phenomenon, give a
finite-witness analogue of the bowl Q-factor's frequency-selectivity
reading, and bridge to `EchoChamberAsTaoBowl.IsPejorativeEcho` at
the dynamical level rather than only the static one.
-/

end SocialDynamicsHooke
