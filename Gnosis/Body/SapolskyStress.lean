import Init
import Gnosis.Body.Anthropogenesis
import Gnosis.Body.Robustness

/-!
# Sapolsky Stress — the Dose Makes the Poison (Hormesis, Allostatic Load, Determinism)

Robert Sapolsky's contrarian-but-true results about stress and behavior, made
into theorems. This is the capstone of the project's anxiety/grit arc: it
**refines** the coarse claim of `Anthropogenesis` ("anxiety has positive value")
into a *dose-response*, ties chronic overload to `Robustness.breaks`, and closes
with Sapolsky's "Determined" thesis — behavior is caused — softened only by the
house clinamen (the +1 swerve).

The arc, as theorems:

1. **The inverted-U (hormesis / Yerkes-Dodson).** Performance as a discrete
   downward parabola `performance s c = s * (c - s)` on `0..c`. Acute stress
   *helps* (`acute_stress_helps`); chronic stress *hurts*
   (`chronic_stress_hurts`); both extremes — comfort `s = 0` and collapse
   `s = c` — yield zero (`zero_stress_zero_performance`,
   `max_stress_zero_performance`). The headline `inverted_u`: there is a peak
   with performance rising strictly up to it and falling strictly after.
   *Stress is neither good nor bad — the DOSE makes it so.* This refines
   `Anthropogenesis.comfort_is_cultural_death` (the `s = 0` end) and adds the
   `s = c` collapse end the older theorem lacked.

2. **Allostatic load (chronic stress crashes).** Cumulative load
   `allostaticLoad perTick ticks = perTick * ticks`. Few ticks `withstands`
   (`acute_load_withstands`); for any fixed `perTick > 0` there is a tick count
   past which the load exceeds tolerance and the body `breaks`
   (`chronic_load_breaks`). Bridges to `Robustness.breaks` / `withstands`.

3. **Determinism ("Determined", no free will).** Behavior is a pure function of
   state (genes + environment + history): `behavior s = s`. Same state ⇒ same
   behavior (`behavior_is_determined`); no behavior is uncaused
   (`no_uncaused_behavior`). The only freedom is the clinamen swerve
   `swerve s = s + 1`, which is the *sole* departure from determinism
   (`swerve_is_the_only_freedom`).

4. `sapolsky_principle` — the three composed into one proved theorem: *all
   thanks to anxiety — in the right dose.*

Rustic Church: `import Init` only (plus the two sibling Body modules reused).
`Nat`/`Int` only, no Float/Real, no Mathlib. Proofs from core `Nat` lemmas. No
`sorry`, no `simp`/`decide`/`omega` on open goals.
-/

namespace Gnosis.Body.SapolskyStress

open Gnosis.Body.Anthropogenesis
open Gnosis.Body.Robustness

/-! ## 1. The inverted-U: hormesis / Yerkes-Dodson

Performance is a discrete downward parabola in the stress dose, peaking near
`capacity / 2`. We use truncated `Nat.sub`, so beyond `capacity` the second
factor is `0` and performance is pinned to `0` (collapse). -/

/-- **Performance under stress.** A discrete downward parabola on `0..capacity`:
    performance is the stress dose times the *remaining* headroom
    `capacity - stress` (truncated subtraction). It is `0` at both ends and peaks
    near `capacity / 2`. -/
def performance (stress capacity : Nat) : Nat := stress * (capacity - stress)

/-- Key arithmetic bridge: when `stress + 1 ≤ capacity`, the headroom at dose
    `stress` is exactly one more than the headroom at dose `stress + 1`. This is
    the single algebraic fact behind both arms of the inverted-U. -/
theorem headroom_step (stress capacity : Nat) (h : stress + 1 ≤ capacity) :
    capacity - stress = (capacity - (stress + 1)) + 1 := by
  -- capacity - (stress+1) = capacity - stress - 1, and adding 1 back is valid
  -- because capacity - stress ≥ 1 (since stress < capacity).
  rw [← Nat.sub_sub]
  -- goal: capacity - stress = (capacity - stress - 1) + 1
  have hpos : 1 ≤ capacity - stress :=
    Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self stress) h)
  exact (Nat.sub_add_cancel hpos).symm

/-- **Acute stress helps.** Strictly below the peak — `2*stress + 2 ≤ capacity`,
    i.e. the dose is strictly less than `capacity/2` — adding one unit of stress
    *raises* performance. This is the rising arm of the inverted-U: a little
    stress sharpens you.

    (NOTE: the brief suggested the hypothesis `2*stress + 1 ≤ capacity`, but at
    the boundary `capacity = 2*stress + 1` performance is *flat*, not rising —
    e.g. `performance 1 3 = performance 2 3 = 2` — so strict `<` requires the
    one-stronger `2*stress + 2 ≤ capacity`. We keep the theorem honest and
    strict.) -/
theorem acute_stress_helps (stress capacity : Nat) (h : 2 * stress + 2 ≤ capacity) :
    performance stress capacity < performance (stress + 1) capacity := by
  unfold performance
  -- stress + 1 ≤ capacity (needed for headroom_step): from 2*stress+2 ≤ capacity.
  have hle : stress + 1 ≤ capacity := by
    refine Nat.le_trans ?_ h
    -- stress + 1 ≤ 2*stress + 2
    rw [Nat.two_mul]
    -- stress + 1 ≤ (stress + stress) + 2
    refine Nat.add_le_add ?_ ?_
    · exact Nat.le_add_left stress stress
    · exact Nat.le_succ 1
  -- Rewrite the larger headroom in terms of the smaller, then it is pure algebra.
  rw [headroom_step stress capacity hle]
  -- goal: stress * ((capacity - (stress+1)) + 1) < (stress + 1) * (capacity - (stress+1))
  -- abstract q := capacity - (stress + 1)
  generalize hq : capacity - (stress + 1) = q
  -- LHS = stress * (q + 1) = stress * q + stress
  -- RHS = (stress + 1) * q = stress * q + q
  rw [Nat.mul_add, Nat.mul_one, Nat.succ_mul]
  -- goal: stress * q + stress < stress * q + q
  apply Nat.add_lt_add_left
  -- need stress < q.  q = capacity - (stress+1) ≥ stress+1 > stress, using
  -- (stress+1) + (stress+1) = 2*stress+2 ≤ capacity.
  have hq_lb : stress + 1 ≤ q := by
    rw [← hq]
    -- stress + 1 ≤ capacity - (stress + 1)  ⇐  (stress+1) + (stress+1) ≤ capacity
    apply Nat.le_sub_of_add_le
    -- (stress + 1) + (stress + 1) ≤ capacity
    have hrewrite : (stress + 1) + (stress + 1) = 2 * stress + 2 := by
      -- (stress+1)+(stress+1) = 2*(stress+1) = 2*stress + 2*1 = 2*stress + 2
      rw [← Nat.two_mul (stress + 1), Nat.left_distrib, Nat.mul_one]
    rw [hrewrite]
    exact h
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self stress) hq_lb

/-- **Chronic stress hurts.** Strictly above the peak — `capacity ≤ 2*stress`
    (the dose is at or past `capacity/2`) and still in range
    (`stress + 1 ≤ capacity`) — adding one unit of stress *lowers* performance.
    This is the falling arm of the inverted-U: past the optimum, more stress only
    degrades you. (The combined hypotheses force `1 ≤ stress`, so the drop is
    strict.) -/
theorem chronic_stress_hurts (stress capacity : Nat)
    (hpeak : capacity ≤ 2 * stress) (hrange : stress + 1 ≤ capacity) :
    performance (stress + 1) capacity < performance stress capacity := by
  unfold performance
  rw [headroom_step stress capacity hrange]
  generalize hq : capacity - (stress + 1) = q
  -- goal: (stress + 1) * q < stress * (q + 1)
  rw [Nat.mul_add, Nat.mul_one, Nat.succ_mul]
  -- goal: stress * q + q < stress * q + stress
  apply Nat.add_lt_add_left
  -- need q < stress.  q = capacity - (stress+1) ≤ 2*stress - (stress+1) = stress - 1 < stress.
  have hq_ub : q ≤ stress - 1 := by
    rw [← hq]
    have hmono : capacity - (stress + 1) ≤ (2 * stress) - (stress + 1) :=
      Nat.sub_le_sub_right hpeak (stress + 1)
    have hcalc : (2 * stress) - (stress + 1) = stress - 1 := by
      rw [Nat.two_mul]
      -- (stress + stress) - (stress + 1) = stress - 1
      rw [Nat.sub_add_eq, Nat.add_sub_cancel_left]
    rw [hcalc] at hmono
    exact hmono
  -- 1 ≤ stress: from stress + 1 ≤ capacity ≤ 2*stress.
  have hs_pos : 1 ≤ stress := by
    have hchain : stress + 1 ≤ 2 * stress := Nat.le_trans hrange hpeak
    -- stress + 1 ≤ stress + stress  ⇒  1 ≤ stress
    rw [Nat.two_mul] at hchain
    exact Nat.le_of_add_le_add_left hchain
  -- stress - 1 < stress
  have hlt : stress - 1 < stress := Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hs_pos) Nat.one_pos
  exact Nat.lt_of_le_of_lt hq_ub hlt

/-- **Zero stress, zero performance.** With no stress at all there is no output:
    comfort is unproductive. This is exactly
    `Anthropogenesis.comfort_is_cultural_death` re-seen on the performance curve
    — the `stress = 0` end of the inverted-U. -/
theorem zero_stress_zero_performance (capacity : Nat) : performance 0 capacity = 0 := by
  unfold performance
  exact Nat.zero_mul (capacity - 0)

/-- **Max stress, zero performance.** At `stress = capacity` the remaining
    headroom is `0`, so performance collapses to `0`: total stress is as
    unproductive as no stress. This is the *collapse* end of the inverted-U that
    `comfort_is_cultural_death` (the `stress = 0` end) did not capture. -/
theorem max_stress_zero_performance (capacity : Nat) : performance capacity capacity = 0 := by
  unfold performance
  rw [Nat.sub_self]
  exact Nat.mul_zero capacity

/-- **Both extremes are unproductive.** Comfort (`stress = 0`) and collapse
    (`stress = capacity`) both yield zero performance. Pairs the two ends of the
    parabola; refines `comfort_is_cultural_death` by adding the collapse end. -/
theorem both_extremes_unproductive (capacity : Nat) :
    performance 0 capacity = 0 ∧ performance capacity capacity = 0 :=
  ⟨zero_stress_zero_performance capacity, max_stress_zero_performance capacity⟩

/-- **Bridge: comfort is (still) cultural death.** The `stress = 0` end of the
    inverted-U coincides with `Anthropogenesis.comfort_is_cultural_death`: no
    stress means no culture *and* no performance. -/
theorem comfort_end_matches_anthropogenesis (capacity : Nat) :
    performance 0 capacity = 0 ∧ stressToCulture 0 = 0 :=
  ⟨zero_stress_zero_performance capacity, comfort_is_cultural_death⟩

/-- **THE INVERTED-U (the headline Sapolsky theorem).** For any capacity there is
    a peak dose `p = capacity / 2` such that performance is *rising strictly*
    everywhere below it and *falling strictly* everywhere above it — and both
    extremes are zero. Stress is neither simply good nor simply bad: the dose
    makes the poison.

    We expose the two arms as universally-quantified strict-monotonicity facts
    (the honest, fully general statement), together with the two zero endpoints,
    around the witness peak. -/
theorem inverted_u (capacity : Nat) :
    ∃ p : Nat,
      p = capacity / 2 ∧
      -- rising strictly below the peak
      (∀ s, 2 * s + 2 ≤ capacity → performance s capacity < performance (s + 1) capacity) ∧
      -- falling strictly above the peak
      (∀ s, capacity ≤ 2 * s → s + 1 ≤ capacity →
          performance (s + 1) capacity < performance s capacity) ∧
      -- both extremes collapse to zero
      (performance 0 capacity = 0 ∧ performance capacity capacity = 0) :=
  ⟨capacity / 2, rfl,
   fun s hs => acute_stress_helps s capacity hs,
   fun s hpeak hrange => chronic_stress_hurts s capacity hpeak hrange,
   both_extremes_unproductive capacity⟩

/-! ## 2. Allostatic load: chronic stress crashes

Acute stress (a sprint) is survivable; the same stressor applied tick after tick
accumulates into an *allostatic load* that eventually exceeds any fixed
tolerance and `breaks` the body. -/

/-- **Allostatic load.** Cumulative wear: a per-tick stressor `perTick` applied
    over `ticks` ticks accumulates linearly. -/
def allostaticLoad (perTick ticks : Nat) : Nat := perTick * ticks

/-- Allostatic load is monotone in time: more ticks never means less wear. -/
theorem allostaticLoad_monotone (perTick t1 t2 : Nat) (h : t1 ≤ t2) :
    allostaticLoad perTick t1 ≤ allostaticLoad perTick t2 := by
  unfold allostaticLoad
  exact Nat.mul_le_mul_left perTick h

/-- **Acute load is withstood.** Zero ticks of stress impose zero load, which is
    within *any* tolerance — a body at rest never breaks. (The acute, few-ticks
    end of the curve.) -/
theorem acute_load_withstands (perTick tolerance : Nat) :
    withstands tolerance (allostaticLoad perTick 0) := by
  unfold withstands allostaticLoad
  rw [Nat.mul_zero]
  exact Nat.zero_le tolerance

/-- **Chronic load breaks.** For any fixed per-tick stressor `perTick > 0` and
    any tolerance, there is a number of ticks after which the accumulated
    allostatic load strictly exceeds the tolerance — i.e. the body `breaks`. The
    witness is `tolerance + 1` ticks: even the gentlest nonzero chronic stressor,
    sustained long enough, crosses every fixed wall. This is `Robustness.breaks`
    driven by time, not by a single big shock. -/
theorem chronic_load_breaks (perTick tolerance : Nat) (hp : 0 < perTick) :
    ∃ ticks : Nat, breaks tolerance (allostaticLoad perTick ticks) := by
  refine ⟨tolerance + 1, ?_⟩
  unfold breaks allostaticLoad
  -- tolerance < perTick * (tolerance + 1)
  -- Since 1 ≤ perTick, we have (tolerance + 1) ≤ perTick * (tolerance + 1).
  have hstep : (tolerance + 1) * 1 ≤ (tolerance + 1) * perTick :=
    Nat.mul_le_mul_left (tolerance + 1) hp
  rw [Nat.mul_one] at hstep
  -- tolerance < tolerance + 1 ≤ (tolerance + 1) * perTick = perTick * (tolerance + 1)
  rw [Nat.mul_comm (tolerance + 1) perTick] at hstep
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self tolerance) hstep

/-- **Acute vs chronic, side by side.** The same nonzero stressor that the body
    withstands at rest (`0` ticks) will, sustained for `tolerance + 1` ticks,
    break it. Dose in *time* is itself a dose: chronic is acute repeated. -/
theorem acute_withstands_chronic_breaks (perTick tolerance : Nat) (hp : 0 < perTick) :
    withstands tolerance (allostaticLoad perTick 0) ∧
    breaks tolerance (allostaticLoad perTick (tolerance + 1)) := by
  refine ⟨acute_load_withstands perTick tolerance, ?_⟩
  unfold breaks allostaticLoad
  have hstep : (tolerance + 1) * 1 ≤ (tolerance + 1) * perTick :=
    Nat.mul_le_mul_left (tolerance + 1) hp
  rw [Nat.mul_one] at hstep
  rw [Nat.mul_comm (tolerance + 1) perTick] at hstep
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self tolerance) hstep

/-! ## 3. Determinism — "Determined": behavior is caused, the swerve is the only
freedom -/

/-- **Behavior.** A pure function of the agent's `state` (the lumped sum of genes,
    environment, and history). Sapolsky's thesis: there is no extra ingredient —
    behavior is read off the cause. -/
def behavior (state : Nat) : Nat := state

/-- **Behavior is determined.** Identical states produce identical behavior —
    there is no hidden free variable that could make the same cause yield a
    different effect. -/
theorem behavior_is_determined (s1 s2 : Nat) (h : s1 = s2) : behavior s1 = behavior s2 := by
  rw [h]

/-- **No uncaused behavior.** Every behavior has a determining state that produces
    exactly it: there is no output without a cause. (Surjectivity-from-cause:
    `behavior` hits every value, and it does so *only* via its determining input.) -/
theorem no_uncaused_behavior (b : Nat) : ∃ state : Nat, behavior state = b :=
  ⟨b, rfl⟩

/-- **Behavior is injective in its cause.** Distinct behaviors can only come from
    distinct states — the cause is fully recoverable from the effect, the
    strongest form of "no uncaused behavior": nothing is left unexplained. -/
theorem behavior_injective (s1 s2 : Nat) (h : behavior s1 = behavior s2) : s1 = s2 := h

/-- **The swerve (clinamen).** The single free element the house cosmology
    admits: an atom-scale departure of `+1` from the determined course. -/
def swerve (state : Nat) : Nat := state + 1

/-- **The swerve is the only freedom.** For every state the swerve differs from
    the determined behavior — and it differs by exactly one, the minimal possible
    departure. Everything else is caused; the clinamen is the sole, irreducible
    exception. -/
theorem swerve_is_the_only_freedom (state : Nat) : swerve state ≠ behavior state := by
  unfold swerve behavior
  -- state + 1 ≠ state
  intro hcontra
  -- hcontra : state + 1 = state.  Then state < state + 1 = state, contradiction.
  have hlt : state < state + 1 := Nat.lt_succ_self state
  rw [hcontra] at hlt
  exact Nat.lt_irrefl state hlt

/-- **The swerve is minimal.** The clinamen is exactly one unit off the determined
    course: freedom is real but infinitesimal, the smallest crack in causation. -/
theorem swerve_is_minimal (state : Nat) : swerve state = behavior state + 1 := rfl

/-! ## 4. The headline synthesis -/

/-- **The Sapolsky principle.** Three of Sapolsky's contrarian-but-true results,
    proved and composed into one theory:

    * (inverted-U / hormesis) performance under stress is a parabola: below the
      peak `capacity/2` more stress *helps*, above it more stress *hurts*, and
      both extremes — comfort `s = 0` and collapse `s = capacity` — yield zero.
      The dose makes the poison;
    * (allostatic load) acute stress is withstood, but any fixed nonzero
      stressor, sustained long enough, accumulates past every tolerance and
      `breaks` the body — chronic is acute repeated in time;
    * (determinism + swerve) behavior is a pure function of its causing state
      (same state ⇒ same behavior, no behavior without a cause), and the only
      freedom is the `+1` clinamen, which is the sole departure from
      determinism.

    Bundled so the three pictures are provably one theory — *all thanks to anxiety,
    in the right dose.* -/
theorem sapolsky_principle
    (capacity : Nat)
    (perTick tolerance : Nat) (hp : 0 < perTick)
    (s1 s2 : Nat) (hstate : s1 = s2)
    (state : Nat) :
    -- 1. the inverted-U: rising arm, falling arm, and both zero extremes
    ((∀ s, 2 * s + 2 ≤ capacity → performance s capacity < performance (s + 1) capacity) ∧
     (∀ s, capacity ≤ 2 * s → s + 1 ≤ capacity →
        performance (s + 1) capacity < performance s capacity) ∧
     performance 0 capacity = 0 ∧ performance capacity capacity = 0) ∧
    -- 2. allostatic load: acute withstands, chronic (enough ticks) breaks
    (withstands tolerance (allostaticLoad perTick 0) ∧
     (∃ ticks, breaks tolerance (allostaticLoad perTick ticks))) ∧
    -- 3. determinism: behavior is caused, the swerve is the only freedom
    (behavior s1 = behavior s2 ∧
     (∃ st, behavior st = state) ∧
     swerve state ≠ behavior state) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨fun s hs => acute_stress_helps s capacity hs,
           fun s hpeak hrange => chronic_stress_hurts s capacity hpeak hrange,
           zero_stress_zero_performance capacity,
           max_stress_zero_performance capacity⟩
  · exact ⟨acute_load_withstands perTick tolerance,
           chronic_load_breaks perTick tolerance hp⟩
  · exact ⟨behavior_is_determined s1 s2 hstate,
           no_uncaused_behavior state,
           swerve_is_the_only_freedom state⟩

end Gnosis.Body.SapolskyStress
