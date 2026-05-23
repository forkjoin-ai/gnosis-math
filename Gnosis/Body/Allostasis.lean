import Init
import Gnosis.Body.Anthropogenesis
import Gnosis.Body.Robustness

/-!
# Allostasis — Homeostasis Under Load and Allostatic Collapse

The Lean counterpart of the project's Rust `homeostasis`/`stress` modules
(`aeon-corpus/src/homeostasis.rs`, `aeon-corpus/src/stress.rs`). A living system
holds a physiological variable near its setpoint by *returning* it each step: a
homeostat closes the gap by a restorative `quota`. ACUTE stress — a one-shot
deviation the quota can absorb — resolves fully. CHRONIC stress — the same
per-tick stressor sustained over time — accumulates an *allostatic load* that
eventually exceeds any fixed tolerance and `breaks` the body
(`Gnosis.Body.Robustness`).

The recovery dynamics mirror `Gnosis.SleepDebt`: truncated `Nat.sub` recovery, a
residue that carries forward when the quota is too small. The collapse dynamics
mirror `Gnosis.Body.Robustness.breaks` and the felt-vacuum thread of
`Gnosis.Body.Anthropogenesis`.

The arc, as theorems:

1. **Acute recovery** — `full_recovery_clears_deviation`: a deviation within the
   restorative quota returns to `0` (acute stress fully resolves). Mirrors
   `SleepDebt.full_recovery_clears_residual_debt`.
2. **Overload residue** — `partial_recovery_leaves_residue`: a deviation beyond
   the quota leaves a positive residue that carries forward.
3. **Acute load is survivable** — `acute_withstands`: few ticks keep the load
   within tolerance, so the body `withstands` it.
4. **Chronic load is fatal** — `chronic_breaks`: for any nonzero per-tick
   stressor there is a tick count after which the body `breaks` (witness:
   `tolerance / perTick + 1`).
5. **The dose makes the poison** — `the_dose_makes_the_poison`: the SAME
   per-tick stressor is survivable acutely and fatal chronically; only the
   duration (dose in time) differs.
6. **Allostatic grit** — `allostatic_grit`: grit is the maximum tick count
   before breakage; it is finite and positive when `0 < perTick ≤ tolerance`.

Rustic Church: `import Init` only (plus the two sibling Body modules reused).
`Nat`/`Int` only, no Float/Real, no Mathlib. Proofs from core `Nat` lemmas. No
`sorry`, no `simp`/`decide`/`omega` on open goals.
-/

namespace Gnosis.Body.Allostasis

open Gnosis.Body.Anthropogenesis
open Gnosis.Body.Robustness

/-! ## 1. The homeostat: returning a deviation toward zero

A `Homeostat.step` in the Rust module closes the setpoint gap by a fraction; in
`Nat` we model the *restorative capacity per step* as a fixed `quota` that the
step subtracts from the current deviation. The deviation returns toward `0`
(truncated subtraction), exactly as `SleepDebt.residualDebt` saturates. -/

/-- **Recovery step.** One restoring step takes a `deviation` and removes up to
    `quota` of it (truncated at `0`): the homeostat returns the value toward its
    setpoint. With adequate quota the deviation clears; beyond the quota a residue
    remains. -/
def recover (deviation quota : Nat) : Nat := deviation - quota

/-- Recovery never increases the deviation: a restoring step only ever closes the
    gap (monotone return toward the setpoint). -/
theorem recover_le_deviation (deviation quota : Nat) : recover deviation quota ≤ deviation := by
  unfold recover
  exact Nat.sub_le deviation quota

/-- **(THM 1) Full recovery clears the deviation.** An acute deviation within the
    restorative quota returns all the way to `0`: acute stress fully resolves in
    one step. This mirrors `SleepDebt.full_recovery_clears_residual_debt` — when
    the demand is within the recovery capacity, the residual is exactly zero. -/
theorem full_recovery_clears_deviation {deviation quota : Nat}
    (hClear : deviation ≤ quota) : recover deviation quota = 0 := by
  unfold recover
  exact Nat.sub_eq_zero_of_le hClear

/-- **(THM 2) Partial recovery leaves a residue.** When the deviation overshoots
    the restorative quota, the step cannot clear it: a strictly positive residue
    remains and carries forward to the next step (the seed of accumulating
    allostatic load). Mirrors `SleepDebt.partial_recovery_leaves_positive_debt`. -/
theorem partial_recovery_leaves_residue {deviation quota : Nat}
    (hShortfall : quota < deviation) : 0 < recover deviation quota := by
  unfold recover
  exact Nat.sub_pos_of_lt hShortfall

/-! ## 2. Allostatic load: chronic stress accumulates

The same per-tick stressor applied over time accumulates linearly into an
allostatic load (`stress.rs::allostatic_load`). Past `tolerance` the body
`breaks` (`Robustness.breaks` / `stress.rs::crashes`). -/

/-- **Allostatic load.** Cumulative wear: a per-tick stressor `perTick` sustained
    over `ticks` ticks accumulates linearly (`stress.rs::allostatic_load`). -/
def load (perTick ticks : Nat) : Nat := perTick * ticks

/-- Allostatic load is monotone in time: more ticks never means less wear. -/
theorem load_monotone (perTick t₁ t₂ : Nat) (h : t₁ ≤ t₂) :
    load perTick t₁ ≤ load perTick t₂ := by
  unfold load
  exact Nat.mul_le_mul_left perTick h

/-- **(THM 3) Acute load is withstood.** When few enough ticks keep the
    accumulated load within tolerance, the body `withstands` it: an acute episode
    of stress is survivable. (Specialize `hsmall` to `ticks = 0`, or any small
    duration, to recover the Rust test `acute: fine`.) -/
theorem acute_withstands (perTick ticks tolerance : Nat)
    (hsmall : load perTick ticks ≤ tolerance) :
    withstands tolerance (load perTick ticks) := by
  unfold withstands
  exact hsmall

/-- A rest tick imposes no load, so a body at rest withstands any tolerance — the
    concrete acute endpoint (`load perTick 0 = 0`). -/
theorem rest_withstands (perTick tolerance : Nat) :
    withstands tolerance (load perTick 0) := by
  unfold withstands load
  rw [Nat.mul_zero]
  exact Nat.zero_le tolerance

/-- The single arithmetic fact behind chronic collapse: for `perTick > 0`, the
    load at `tolerance / perTick + 1` ticks strictly exceeds `tolerance`. One
    tick past the quotient floor, the linear accumulation has crossed the wall. -/
theorem load_at_witness_exceeds (perTick tolerance : Nat) (hp : 0 < perTick) :
    tolerance < load perTick (tolerance / perTick + 1) := by
  unfold load
  -- div_lt_iff_lt_mul : x / k < y ↔ x < y * k   (for k > 0)
  have hstep : tolerance / perTick < tolerance / perTick + 1 := Nat.lt_succ_self _
  have hmul : tolerance < (tolerance / perTick + 1) * perTick :=
    (Nat.div_lt_iff_lt_mul hp).mp hstep
  rw [Nat.mul_comm perTick (tolerance / perTick + 1)]
  exact hmul

/-- **(THM 4) Chronic load breaks.** For any fixed nonzero per-tick stressor and
    any tolerance, there is a number of ticks after which the accumulated
    allostatic load strictly exceeds the tolerance — the body `breaks`. The
    witness is `tolerance / perTick + 1` ticks: even the gentlest sustained
    stressor, given enough time, crosses every fixed wall. This is
    `Robustness.breaks` driven by *duration*, not by a single big shock. -/
theorem chronic_breaks (perTick tolerance : Nat) (hp : 0 < perTick) :
    ∃ ticks : Nat, breaks tolerance (load perTick ticks) := by
  refine ⟨tolerance / perTick + 1, ?_⟩
  unfold breaks
  exact load_at_witness_exceeds perTick tolerance hp

/-! ## 3. The dose makes the poison -/

/-- **(THM 5) The dose makes the poison.** The headline. The *same* per-tick
    stressor `perTick` is survivable acutely and fatal chronically — only the
    duration (the dose in time) differs. Given any acute duration `acuteTicks`
    whose load is within tolerance, the body `withstands` it; yet there exists a
    chronic duration after which the same stressor `breaks` it. Stress is neither
    simply good nor simply bad: dose (here, *time*) makes the poison. -/
theorem the_dose_makes_the_poison (perTick tolerance acuteTicks : Nat) (hp : 0 < perTick)
    (hAcute : load perTick acuteTicks ≤ tolerance) :
    withstands tolerance (load perTick acuteTicks) ∧
    ∃ chronicTicks : Nat, breaks tolerance (load perTick chronicTicks) :=
  ⟨acute_withstands perTick acuteTicks tolerance hAcute, chronic_breaks perTick tolerance hp⟩

/-- **Acute vs chronic, side by side.** The same nonzero stressor that a body at
    rest (`0` ticks) withstands will, sustained for `tolerance / perTick + 1`
    ticks, break it. The concrete two-duration instance of
    `the_dose_makes_the_poison`. -/
theorem rest_withstands_chronic_breaks (perTick tolerance : Nat) (hp : 0 < perTick) :
    withstands tolerance (load perTick 0) ∧
    breaks tolerance (load perTick (tolerance / perTick + 1)) := by
  refine ⟨rest_withstands perTick tolerance, ?_⟩
  unfold breaks
  exact load_at_witness_exceeds perTick tolerance hp

/-! ## 4. Allostatic grit: the maximum dose before collapse

Grit against chronic stress (`stress.rs::chronic_grit`) is how many ticks of a
fixed per-tick stressor the body tolerates before collapse. We define it as
`tolerance / perTick`: the largest tick count whose load stays within tolerance
(one more tick is `chronic_breaks`'s witness). -/

/-- **Allostatic grit.** The maximum number of ticks of a fixed per-tick stressor
    the body tolerates before collapse: the integer quotient `tolerance / perTick`
    (`stress.rs::chronic_grit`). One more tick is exactly the breaking witness of
    `chronic_breaks`. -/
def allostaticGrit (perTick tolerance : Nat) : Nat := tolerance / perTick

/-- **Grit is withstood.** The load sustained for exactly `allostaticGrit` ticks
    stays within tolerance: the body endures right up to its grit. -/
theorem grit_load_withstood (perTick tolerance : Nat) :
    withstands tolerance (load perTick (allostaticGrit perTick tolerance)) := by
  unfold withstands load allostaticGrit
  exact Nat.mul_div_le tolerance perTick

/-- **One tick past grit breaks.** Sustaining the stressor for one tick beyond
    `allostaticGrit` exceeds tolerance — the breaking point is sharp, exactly at
    the grit. -/
theorem grit_succ_breaks (perTick tolerance : Nat) (hp : 0 < perTick) :
    breaks tolerance (load perTick (allostaticGrit perTick tolerance + 1)) := by
  unfold breaks allostaticGrit
  exact load_at_witness_exceeds perTick tolerance hp

/-- **(THM 6) Allostatic grit is finite and positive.** For a survivable nonzero
    stressor (`0 < perTick ≤ tolerance`) the body's grit against chronic stress is
    *finite* — it never exceeds `tolerance`, so collapse is inevitable in bounded
    time — yet *positive* — the body can take at least one tick before it begins
    to crack. Mirrors `stress.rs::chronic_grit_is_finite`: the body tolerates
    some, but not unbounded, chronic stress. -/
theorem allostatic_grit (perTick tolerance : Nat) (hp : 0 < perTick) (hle : perTick ≤ tolerance) :
    0 < allostaticGrit perTick tolerance ∧ allostaticGrit perTick tolerance ≤ tolerance := by
  unfold allostaticGrit
  refine ⟨?_, Nat.div_le_self tolerance perTick⟩
  -- 0 < tolerance / perTick  ⇐  perTick * 1 ≤ tolerance  ⇐  perTick ≤ tolerance.
  refine (Nat.le_div_iff_mul_le hp).mpr ?_
  rw [Nat.one_mul]
  exact hle

/-! ## 5. The headline synthesis -/

/-- **The allostasis principle.** Homeostasis under load, proved and composed:

    * (acute recovery) a deviation within the restorative quota returns fully to
      zero — acute stress resolves; beyond the quota a positive residue carries
      forward;
    * (the dose) the same nonzero per-tick stressor is *withstood* for a small
      enough duration but *breaks* the body for a large enough one — chronic is
      acute repeated in time, and the dose (here, time) makes the poison;
    * (grit) the body's grit against chronic stress is finite (collapse is
      inevitable in bounded time) yet positive (it endures at least one tick).

    Bundled so the three pictures are provably one theory. -/
theorem allostasis_principle
    (deviation quota : Nat) (hClear : deviation ≤ quota)
    (deviation' quota' : Nat) (hShortfall : quota' < deviation')
    (perTick tolerance acuteTicks : Nat) (hp : 0 < perTick) (hle : perTick ≤ tolerance)
    (hAcute : load perTick acuteTicks ≤ tolerance) :
    -- 1. acute recovery clears; overload leaves a residue
    (recover deviation quota = 0 ∧ 0 < recover deviation' quota') ∧
    -- 2. the dose makes the poison: acute withstands, chronic breaks
    (withstands tolerance (load perTick acuteTicks) ∧
      ∃ chronicTicks, breaks tolerance (load perTick chronicTicks)) ∧
    -- 3. allostatic grit is finite and positive
    (0 < allostaticGrit perTick tolerance ∧ allostaticGrit perTick tolerance ≤ tolerance) := by
  refine ⟨⟨full_recovery_clears_deviation hClear, partial_recovery_leaves_residue hShortfall⟩,
          the_dose_makes_the_poison perTick tolerance acuteTicks hp hAcute,
          allostatic_grit perTick tolerance hp hle⟩

end Gnosis.Body.Allostasis
