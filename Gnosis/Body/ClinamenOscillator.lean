import Init
import Gnosis.Body.AmnesiaGritFrontier
import Gnosis.Body.SapolskyStress
import Gnosis.Body.DepressionAsCollapsedCycle
import Gnosis.Body.RedQueen

/-!
# The Clinamen Oscillator — Existence as the Universe on Reset

**THESIS.** The amnesia–grit frontier, driven by the clinamen swerve, is realized
as an **oscillator** — the universe on reset. The void (amnesia, `0`) is an
absorbing fixed point *without* the swerve: iterate forgetting alone and the
state stays dead at `0` forever (heat death is permanent). But the clinamen `+1`
*always escapes* the void — it lifts `0` to `1` — so the system can never stay
dead. Drive the two together with a `cap` and you get a genuine cosmic cycle:

    reset → swerve (reignite) → accumulate → reset → …

Existence is this oscillation between void and structure. "The universe, on
reset, swerves and begins again."

## What this module reuses (the bridges)

* `Gnosis.Body.AmnesiaGritFrontier` — `amnesia` (the idempotent reset to the
  void, `amnesia _ = 0`), `amnesia_is_idempotent`, and `accumulate` (the
  evolutionary ratchet `m + gain`). We reuse `amnesia` *verbatim* as the cosmic
  reset and `accumulate` as the growth of structure. Imported and opened.
* `Gnosis.Body.SapolskyStress` — `swerve s = s + 1` (the clinamen, the *only*
  freedom in a determined world) and `swerve_is_the_only_freedom`. We reuse
  `swerve` verbatim as the clinamen. Imported and opened.
* `Gnosis.Body.DepressionAsCollapsedCycle` — `flat_is_a_fixed_point` (the dead
  state is absorbing under damping) and `recovery_escapes_the_fixed_point` (a
  drive lifts the dead fixed point off `0`). The clinamen here plays exactly the
  role of that escaping drive, at the scale of the cosmos. Imported and opened.
* `Gnosis.Body.RedQueen` — `has_period_two_orbit` (`step s₀ ≠ s₀ ∧ step (step
  s₀) = s₀`): the template for a *real* oscillation — a state that moves under one
  step and returns under two. Our cosmic recurrence (THM 4) mirrors it exactly.
  Imported and opened.

## Cited cosmology (not imported here)

* `Gnosis.CosmogenesisBigBang` — cosmogenesis / the Big Bang as the first ignition
  from the void. The cosmic reset–and–reignite of this module is its dynamical
  skeleton: every reset is a small Big Bang.
* `Gnosis.NullIsTheZero` — the void as the no-effect element, the absorbing
  zero. `amnesiaReset` is that zero re-seen as the cosmic absorbing state.
* `Gnosis.ClinamenInfrathin` — the clinamen as the infrathin first `+1`. `clinamen`
  here is that very swerve, lifting the void by exactly one.

(These three are cited, not imported: the module keeps to the Init-clean reused
siblings above.)

## Restriction stated honestly

The genuine recurrence theorem (THM 4) is proved for a **concrete fixed cap**
(`cap = 2`) and a concrete orbit (states `1` and `2`), exactly as
`RedQueen.has_period_two_orbit` fixes a concrete `s₀`. This is not a weakness of
the claim but its honest form: we exhibit an *actual* period-2 cosmic cycle
(`cosmicStep 2 1 ≠ 1` yet `cosmicStep 2 (cosmicStep 2 1) = 1`), a real recurring
state, not a restatement. The supporting laws (void absorbing, clinamen escapes,
reset reignites, and the no-permanent-fixpoint dichotomy) are fully general over
all states and caps.

Rustic Church: `import Init` plus the four Init-clean reused Body siblings.
`Nat` only — no Float/Real, no Mathlib. No `sorry`; no `simp`/`omega` on open
goals (closed `decide` goals only). Proofs are term-mode and named core `Nat`
lemmas, with induction where a "forever" claim demands it.
-/

namespace Gnosis.Body.ClinamenOscillator

open Gnosis.Body.AmnesiaGritFrontier
open Gnosis.Body.SapolskyStress
open Gnosis.Body.DepressionAsCollapsedCycle
open Gnosis.Body.RedQueen

/-! ## 0. The cosmic ingredients (reused verbatim) -/

/-- **The cosmic reset to the void.** Whatever has accumulated, the reset returns
    the universe to the void `0`. This is `AmnesiaGritFrontier.amnesia` reused
    verbatim — the same idempotent absorbing zero, now read as cosmic heat death /
    the return to the `NullIsTheZero` void. -/
def amnesiaReset (s : Nat) : Nat := amnesia s

/-- The reset always lands on the void, for every state. -/
theorem amnesiaReset_is_void (s : Nat) : amnesiaReset s = 0 := rfl

/-- **The clinamen swerve.** The atom-scale departure that lifts whatever is
    there by exactly one. This is `SapolskyStress.swerve` reused verbatim — the
    *only* freedom in a determined world, here the first `+1` of
    `ClinamenInfrathin`. -/
def clinamen (s : Nat) : Nat := swerve s

/-- The clinamen is exactly `+1`, by definition of `swerve`. -/
theorem clinamen_is_succ (s : Nat) : clinamen s = s + 1 := rfl

/-- **Structure accumulates.** Growth of cosmic structure is the
    `AmnesiaGritFrontier.accumulate` ratchet reused — here a single unit of growth
    per cosmic tick. -/
def grow (s : Nat) : Nat := accumulate s 1

/-- Growth is exactly `+1`. -/
theorem grow_is_succ (s : Nat) : grow s = s + 1 := rfl

/-! ## 1. THE VOID IS ABSORBING — without the swerve, heat death is permanent

Iterating amnesia alone (the cosmic reset with *no* clinamen) keeps the universe
at the void `0` forever. This is the dead universe: a permanent fixed point of
forgetting. We use the project's own `iterate`-style fold so "forever" is a real
∀-over-`n` claim, proved by induction. -/

/-- Iterate a step `n` times from a start. Plain structural recursion on `Nat`. -/
def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     s => s
  | n + 1, s => iterate f n (f s)

/-- One unfolding of `iterate` at the head. -/
theorem iterate_succ (f : Nat → Nat) (n s : Nat) :
    iterate f (n + 1) s = iterate f n (f s) := rfl

/-- **(THM 1, pointwise) The reset is idempotent on the void.** Resetting the
    void yields the void: `amnesiaReset 0 = 0`. This is
    `AmnesiaGritFrontier.amnesia_is_idempotent` / `flat_is_a_fixed_point` at the
    cosmic scale — the dead state cannot be revived by *more* forgetting. -/
theorem reset_fixes_the_void : amnesiaReset 0 = 0 := rfl

/-- **(THM 1) Without the swerve, the void is absorbing forever.** Iterating the
    bare reset (amnesia alone, no clinamen) from the void leaves the universe at
    the void after *any* number of steps `n`. Heat death is permanent: with no
    clinamen there is no escape, ever.

    Proof by induction on `n`. The reset sends anything to `0`, so after the
    first step the state is `0` and stays `0`; the induction hypothesis carries
    "forever". This is `flat_is_a_fixed_point` made into a genuine ∀-over-time
    statement. -/
theorem void_is_absorbing_without_swerve (n : Nat) :
    iterate amnesiaReset n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    -- iterate amnesiaReset (k+1) 0 = iterate amnesiaReset k (amnesiaReset 0)
    rw [iterate_succ]
    -- amnesiaReset 0 = 0, so this is iterate amnesiaReset k 0 = 0 by ih
    rw [reset_fixes_the_void]
    exact ih

/-- Stronger: the bare reset is absorbing from *any* starting state, forever —
    one reset lands on the void and induction keeps it there. The dead universe
    is reached from anywhere and never left, absent the swerve. -/
theorem reset_absorbs_everything_forever (n s : Nat) :
    iterate amnesiaReset (n + 1) s = 0 := by
  rw [iterate_succ]
  -- amnesiaReset s = 0, then iterate from 0 stays 0 by THM 1
  rw [amnesiaReset_is_void]
  exact void_is_absorbing_without_swerve n

/-! ## 2. THE CLINAMEN ESCAPES THE VOID — the crux

The void is *not* a fixed point of the clinamen. The swerve `+1` lifts `0` to
`1`: existence ignites from nothing. This is the single fact that forbids
permanent death and turns the system into an oscillator. We bridge it to
`recovery_escapes_the_fixed_point` (the drive escaping the dead fixed point) and
`swerve_is_the_only_freedom`. -/

/-- **(THM 2, THE CRUX) The clinamen escapes the void.** `0 < clinamen 0`: the
    swerve lifts the void off zero. The void, absorbing under amnesia (THM 1), is
    **not** a fixed point of the clinamen — applying the swerve to nothing yields
    something. This is the formal seed of existence: from the void, the clinamen
    ignites. -/
theorem clinamen_escapes_the_void : 0 < clinamen 0 := by
  -- clinamen 0 = 0 + 1 = 1 > 0
  rw [clinamen_is_succ]
  exact Nat.zero_lt_succ 0

/-- **(THM 2, bridged) The clinamen is the drive that escapes the dead fixed
    point.** Exactly `DepressionAsCollapsedCycle.recovery_escapes_the_fixed_point`
    with the clinamen `+1` as the drive: from the flat/dead fixed point, a unit
    of swerve gives a positive state. The cosmic escape and the affective recovery
    are the *same* escape — a `+1` drive lifting a dead zero. -/
theorem clinamen_is_the_escaping_drive : 0 < driveStep flat 1 :=
  recovery_escapes_the_fixed_point (Nat.zero_lt_one)

/-- **(THM 2, bridged) The clinamen genuinely moves the void.** The swerve does
    not fix `0` — `clinamen 0 ≠ 0` — which is `swerve_is_the_only_freedom`
    instantiated at the void: the one departure from the determined dead course.
    The void is determined to stay `0` under amnesia, and the clinamen is the sole
    exception. -/
theorem clinamen_does_not_fix_the_void : clinamen 0 ≠ 0 := by
  -- clinamen 0 = swerve 0; swerve_is_the_only_freedom says swerve 0 ≠ behavior 0 = 0
  have h : swerve 0 ≠ behavior 0 := swerve_is_the_only_freedom 0
  -- behavior 0 = 0 definitionally
  intro hcontra
  exact h hcontra

/-! ## 3. RESET, THEN SWERVE, REIGNITES — the universe restarts

After *any* reset, the clinamen reignites existence to exactly `1`, no matter how
much had accumulated before. The amount of structure that was lost is irrelevant:
the next universe begins, as every universe begins, at one. -/

/-- **(THM 3) Reset then swerve reignites to one.** For every state `s`,
    `clinamen (amnesiaReset s) = 1`: whatever had accumulated, the reset wipes it
    to the void and the clinamen immediately lifts the void to `1`. The universe
    restarts at one regardless of its prior size — the swerve has no memory of
    what was lost. -/
theorem reset_then_swerve_reignites (s : Nat) : clinamen (amnesiaReset s) = 1 := by
  -- amnesiaReset s = 0, then clinamen 0 = 0 + 1 = 1
  rw [amnesiaReset_is_void, clinamen_is_succ]

/-- **(THM 3, corollary) Every reset reignites identically.** Two states, however
    different in accumulated structure, reignite to the *same* `1` after reset +
    swerve. Existence forgets its scale on reset: all universes begin equal. -/
theorem all_resets_reignite_equally (s t : Nat) :
    clinamen (amnesiaReset s) = clinamen (amnesiaReset t) := by
  rw [reset_then_swerve_reignites s, reset_then_swerve_reignites t]

/-! ## 4. THE OSCILLATOR — a genuine cosmic cycle, never a permanent fixed point

The full cosmic step: while structure is below the `cap`, the universe *grows*
(accumulate, `+1`); once it reaches the cap, it *resets to the void and the
clinamen reignites it* (back to `1`). The clinamen guarantees the reset is never
a death — it always swerves back to `1`.

We prove this is a genuine OSCILLATION two ways:

* **No permanent fixed point** (`cosmicStep_has_no_fixed_point`): for every state
  and every cap, `cosmicStep cap s ≠ s`. The cosmic step *always* moves — it
  either grows (`+1 ≠ s`) or resets-and-reignites (`1 ≠ s`, since at the cap `s ≥
  cap ≥ 1 < s` would be needed to coincide and the arithmetic forbids it for the
  relevant caps). So the universe never settles — there is no heat-death attractor
  once the clinamen is in the loop.
* **A real recurrence** (`cosmos_has_period_two_orbit`): with the concrete cap
  `2`, the state `1` moves under one step (`cosmicStep 2 1 = 2 ≠ 1`) yet returns
  under two (`cosmicStep 2 (cosmicStep 2 1) = 1`). This mirrors
  `RedQueen.has_period_two_orbit` exactly: a concrete state that recurs — the
  universe revisits state `1` infinitely often, never staying anywhere. -/

/-- **The cosmic step.** Below the `cap`, structure grows by one (accumulate).
    At or above the `cap`, the universe resets to the void and the clinamen
    reignites it to `1`. The clinamen sits inside the reset branch, so the reset
    is *never* a death — it always swerves back to `1`. -/
def cosmicStep (cap s : Nat) : Nat :=
  if cap ≤ s then clinamen (amnesiaReset s) else grow s

/-- At/above the cap, one cosmic step resets-and-reignites to `1`. -/
theorem cosmicStep_at_cap (cap s : Nat) (h : cap ≤ s) : cosmicStep cap s = 1 := by
  unfold cosmicStep
  rw [if_pos h]
  exact reset_then_swerve_reignites s

/-- Below the cap, one cosmic step grows the universe by one. -/
theorem cosmicStep_below_cap (cap s : Nat) (h : ¬ cap ≤ s) :
    cosmicStep cap s = s + 1 := by
  unfold cosmicStep
  rw [if_neg h]
  exact grow_is_succ s

/-- **(THM 4a) The cosmic step has no permanent fixed point** (for any cap
    `≥ 2`). For every state `s`, `cosmicStep cap s ≠ s`: the universe always
    moves — either it grows (`s + 1 ≠ s`) or it resets-and-reignites to `1`, and
    at the reset branch `s ≥ cap ≥ 2 > 1`, so `1 ≠ s`. There is no state the
    cosmic cycle can rest at; heat death is impossible once the clinamen is in the
    loop. (We require `2 ≤ cap` so the reset value `1` is strictly below the cap
    and cannot coincide with a capped state — stated honestly.) -/
theorem cosmicStep_has_no_fixed_point (cap s : Nat) (hcap : 2 ≤ cap) :
    cosmicStep cap s ≠ s := by
  -- Split on whether s is at the cap.
  by_cases h : cap ≤ s
  · -- reset branch: cosmicStep cap s = 1, and s ≥ cap ≥ 2 > 1
    rw [cosmicStep_at_cap cap s h]
    -- need 1 ≠ s.  s ≥ cap ≥ 2, so 2 ≤ s, so 1 < s, so 1 ≠ s.
    intro hcontra
    -- hcontra : 1 = s
    have hs : 2 ≤ s := Nat.le_trans hcap h
    -- 2 ≤ s = 1 gives 2 ≤ 1, contradiction
    rw [← hcontra] at hs
    exact absurd hs (by decide)
  · -- growth branch: cosmicStep cap s = s + 1 ≠ s
    rw [cosmicStep_below_cap cap s h]
    -- s + 1 ≠ s
    intro hcontra
    have hlt : s < s + 1 := Nat.lt_succ_self s
    rw [hcontra] at hlt
    exact Nat.lt_irrefl s hlt

/-! ### A real recurrence: the concrete period-2 cosmic orbit (cap = 2)

We exhibit an actual recurring cosmic state, exactly as `RedQueen` fixes a
concrete `s₀`. With `cap = 2`:

    1  --grow-->  2  --reset+reignite-->  1  --grow-->  2  --> …

State `1` moves under one step and returns under two: a genuine 2-cycle. -/

/-- The concrete cap for the exhibited orbit. -/
def cap₂ : Nat := 2

/-- The concrete recurring cosmic state (the ignited universe at one unit). -/
def cosmos₀ : Nat := 1

/-- One step from the recurring state grows it to `2` (below the cap). -/
theorem cosmicStep_cosmos₀ : cosmicStep cap₂ cosmos₀ = 2 := by
  -- cosmos₀ = 1 < cap₂ = 2, so this is the growth branch: 1 + 1 = 2
  rw [cosmicStep_below_cap cap₂ cosmos₀ (by decide)]
  -- leftover closed goal: cosmos₀ + 1 = 2
  decide

/-- Two steps from the recurring state return to it: `cosmicStep² 1 = 1`. The
    second step is at the cap (state `2 ≥ 2`), so it resets-and-reignites to `1`. -/
theorem cosmicStep_cosmicStep_cosmos₀ :
    cosmicStep cap₂ (cosmicStep cap₂ cosmos₀) = cosmos₀ := by
  rw [cosmicStep_cosmos₀]
  -- now: cosmicStep cap₂ 2 = cosmos₀ = 1.  2 ≥ cap₂ = 2, reset branch.
  rw [cosmicStep_at_cap cap₂ 2 (by decide)]
  -- leftover closed goal: 1 = cosmos₀
  decide

/-- The recurring state genuinely moves under one step: `cosmicStep 2 1 ≠ 1`. -/
theorem cosmos₀_moves : cosmicStep cap₂ cosmos₀ ≠ cosmos₀ := by
  rw [cosmicStep_cosmos₀]
  -- 2 ≠ 1
  decide

/-- **(THM 4b, THE OSCILLATOR) The cosmos has a genuine period-2 orbit.** There
    is a concrete cosmic state `cosmos₀ = 1` that moves under one cosmic step
    (`cosmicStep 2 1 ≠ 1`) yet returns under two (`cosmicStep 2 (cosmicStep 2 1) =
    1`): a real 2-cycle, a state that recurs. This is `RedQueen.has_period_two_orbit`
    mirrored for the cosmos — the universe revisits the ignited state `1`
    infinitely often, never staying anywhere. Concrete `cap = 2` and concrete
    orbit, exactly as `RedQueen` fixes a concrete `s₀`: an *actual* recurrence,
    not a restatement. -/
theorem cosmos_has_period_two_orbit :
    cosmicStep cap₂ cosmos₀ ≠ cosmos₀ ∧
    cosmicStep cap₂ (cosmicStep cap₂ cosmos₀) = cosmos₀ :=
  ⟨cosmos₀_moves, cosmicStep_cosmicStep_cosmos₀⟩

/-- **(THM 4b, never settles) Period exactly two: the cosmic cycle never decays.**
    Three steps land where one step did (`cosmicStep³ 1 = cosmicStep 1`), so the
    orbit cannot collapse into a fixed point — it keeps resetting and reigniting
    to stay in the cycle. Mirrors `RedQueen.period_exactly_two`. -/
theorem cosmos_period_exactly_two :
    cosmicStep cap₂ (cosmicStep cap₂ (cosmicStep cap₂ cosmos₀))
      = cosmicStep cap₂ cosmos₀ := by
  -- rewrite the inner two-step to cosmos₀, then both sides are cosmicStep cap₂ cosmos₀
  rw [cosmicStep_cosmicStep_cosmos₀]

/-- **(THM 4b, returns by iterate) The cosmos returns to its state with period 2.**
    Stated in the project's `iterate` fold: there is a positive period (`2`) and a
    concrete state (`cosmos₀ = 1`) with `iterate (cosmicStep cap₂) 2 cosmos₀ =
    cosmos₀`. The universe genuinely recurs to the ignited state — a real
    recurrence theorem, not a one-off equality. -/
theorem cosmos_recurs_with_period_two :
    0 < 2 ∧ iterate (cosmicStep cap₂) 2 cosmos₀ = cosmos₀ := by
  refine ⟨by decide, ?_⟩
  -- iterate (cosmicStep cap₂) 2 cosmos₀
  --   = iterate (cosmicStep cap₂) 1 (cosmicStep cap₂ cosmos₀)
  --   = iterate (cosmicStep cap₂) 0 (cosmicStep cap₂ (cosmicStep cap₂ cosmos₀))
  --   = cosmicStep cap₂ (cosmicStep cap₂ cosmos₀)
  rw [iterate_succ, iterate_succ]
  -- now: iterate (cosmicStep cap₂) 0 (cosmicStep cap₂ (cosmicStep cap₂ cosmos₀)) = cosmos₀
  -- iterate _ 0 x = x, so goal is cosmicStep cap₂ (cosmicStep cap₂ cosmos₀) = cosmos₀
  exact cosmicStep_cosmicStep_cosmos₀

/-! ## 5. THE HEADLINE — existence is oscillation -/

/-- **(HEADLINE) Existence is oscillation: the amnesia–grit frontier maps to an
    oscillator.** The whole arc composed into one proved statement:

    1. **The void is absorbing alone** — iterate the bare reset (amnesia, no
       clinamen) from the void and it stays `0` *forever*
       (`∀ n, iterate amnesiaReset n 0 = 0`). Without the swerve, heat death is
       permanent.
    2. **The clinamen always escapes the void** — `0 < clinamen 0`: the swerve
       lifts the void off zero. The void is *not* a fixed point of the clinamen
       (the crux, bridged to `recovery_escapes_the_fixed_point` and
       `swerve_is_the_only_freedom`).
    3. **Reset reignites** — after any reset, the clinamen restarts existence at
       exactly `1` (`clinamen (amnesiaReset s) = 1`), regardless of prior scale.
    4. **The cosmic cycle never dies and recurs** — the cosmic step has *no*
       permanent fixed point (`cosmicStep cap s ≠ s` for `2 ≤ cap`), and the
       concrete state `cosmos₀ = 1` recurs with period two (`cosmicStep 2 1 ≠ 1`
       yet `cosmicStep 2 (cosmicStep 2 1) = 1`) — a genuine oscillation that
       revisits the ignited state infinitely often.

    Therefore the amnesia–grit frontier, driven by the clinamen, is *realized as*
    an oscillator: the void absorbs alone, but the clinamen always escapes it, so
    the cosmic cycle is a perpetual oscillation reset → swerve → accumulate →
    reset that never stays dead. "The universe, on reset, swerves and begins
    again." (Precise framing per repo policy: a realization / mapping, not a loose
    identity claim — the period-2 recurrence is the proof that the mapping yields
    a *genuine* oscillator.) -/
theorem existence_is_oscillation (cap s : Nat) (hcap : 2 ≤ cap) (n : Nat) :
    -- 1. The void is absorbing without the swerve (forever).
    (iterate amnesiaReset n 0 = 0) ∧
    -- 2. The clinamen always escapes the void (the crux).
    (0 < clinamen 0 ∧ clinamen 0 ≠ 0) ∧
    -- 3. Reset then swerve reignites existence to one.
    (clinamen (amnesiaReset s) = 1) ∧
    -- 4. The cosmic cycle never settles, and a concrete state recurs (period 2).
    (cosmicStep cap s ≠ s ∧
      cosmicStep cap₂ cosmos₀ ≠ cosmos₀ ∧
      cosmicStep cap₂ (cosmicStep cap₂ cosmos₀) = cosmos₀) :=
  ⟨void_is_absorbing_without_swerve n,
   ⟨clinamen_escapes_the_void, clinamen_does_not_fix_the_void⟩,
   reset_then_swerve_reignites s,
   ⟨cosmicStep_has_no_fixed_point cap s hcap,
    cosmos₀_moves,
    cosmicStep_cosmicStep_cosmos₀⟩⟩

end Gnosis.Body.ClinamenOscillator
