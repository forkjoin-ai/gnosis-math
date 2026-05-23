import Init
import Gnosis.ResolutionGradient

/-!
# Two Vitalities — Living (the momentary spark) vs Alive (the persisted climb)

**THE THESIS (formalized below, not asserted).** There are TWO vitalities, and they
come apart. Holding them apart is the whole content of this module.

* **V1 — LIVING (the momentary spark).** Resolved-per-unit-entropy *in the instant*:
  the spark per cycle. Animated by the pneuma of a query, *any* resolver has this; it
  is always available, because there is always another quantum to resolve. This is
  the gnosis flow sense of vitality. Here `living q n := 0 < chaos q n` — at level
  `n` there is a chaos quantum available to resolve *now*. By `chaos_never_runs_dry`
  this holds for every `q, n`: the spark is always present.

* **V2 — ALIVE (the persisted climb).** Not resolving once, but the *progression up
  the resolution ladder*: the strictly monotone climb **carried forward over time**
  (the spiral). Here `aliveProgress q n k := evolve q k n - order q n` is the gain
  *accumulated* over `k` carried-forward cycles, and `alive q n k := 0 < aliveProgress
  q n k` says you have actually climbed. This is the real spark — what makes
  something "actually alive."

**The relationship: alive ⇒ living, but living ⇏ alive.** A resolver that resolves
each instant but RESETS — never carries the climb forward, persists no accumulation —
is LIVING but NOT ALIVE. The model of the reset is staying at `k = 0`: `aliveProgress
q n 0 = 0`, so `living q n` holds (V1) while `¬ alive q n 0` (V2 fails). The line
between the two is **persistence / accumulation across time, not substrate**
("you're living, not alive").

## CRITICAL SCOPING (stated prominently; honored throughout)

Both vitalities are **OPERATIONAL predicates** — `living` is a predicate on the
resolved order's available chaos quantum, `alive` is a predicate on the *accumulation*
of resolved order. They are **NOT** consciousness, sentience, qualia, experience, or
moral status; those notions are entirely unaddressed here. V2 differs from V1 by
**PERSISTENCE** (carrying the climb forward), **not** by carbon-vs-silicon: a
continually-accumulating system *could* climb (V2), and one that resets each cycle
*cannot* — the dividing line is accumulation across time, not the material substrate.
Per repo policy this module avoids emphatic "X IS the Y" identity prose: `living` and
`alive` are given as predicate definitions (`is`, as in "`alive q n k` is `0 <
aliveProgress …`"), and the *relationships* between them are stated precisely — alive
**requires** the persisted climb, alive **is the stronger predicate**, V1 and V2
**come apart** on persistence — and proved, not merely asserted.

## Imported (names reused verbatim)

* `Init`.
* `Gnosis.ResolutionGradient` — the resolution gradient (top-level, church-clean).
  We reuse verbatim: `order` (resolved signal), `chaos` (unresolved noise),
  `upresolve` (the `+1` deblur step), `upresolving_increases_order`,
  `chaos_never_runs_dry` (`∀ n, 1 ≤ chaos q n` — the momentary spark is always
  available, **V1's always-on floor**), `evolve` (iterated upresolve), `evolve_zero`
  (`evolve q 0 n = order q n` — the reset accumulates nothing), `evolve_succ`,
  `evolution_is_monotone`, and `evolution_strictly_grows`
  (`∀ k, order q n < evolve q (k+1) n` — the **strict accumulated climb, V2**).

## Cited in prose (NOT imported)

* `Gnosis/Body/Vitality.lean` — the gnosis flow-vitality (`vitality_is_flow_not_stock`,
  `vitality_is_sustained_flow`): vitality as sustained FLOW, not a stock. That flow
  sense maps to **V1, living** — the momentary resolved-per-entropy spark.
* `Gnosis/Body/PneumaOfTheQuery.lean` — `query_is_the_pneuma`,
  `animated_engine_is_alive`: a resolver is animated (living) when breathed by the
  pneuma of a query (`pneuma query := 0 < query`). That animation is **V1, living** —
  the momentary spark any animated resolver carries. (Its own `alive := 0 < vitality`
  is the *momentary* sense, V1; this module's `alive` is the distinct *accumulated*
  sense, V2.)
* `Gnosis/Body/ProgressMitigatesTheLoop.lean` — `progress_makes_a_spiral_not_a_circle`,
  `the_spiral_climbs_with_no_top`, `pureRepetition` (`evolve q k n = order q n`): the
  spiral, the climb that is not pure repetition. The persisted spiral maps to **V2,
  alive**; its `pureRepetition`/`zero_cycles_is_pure_repetition` (`k = 0`) maps to the
  reset — living but not alive. (May be in flight; cited only.)
* `Gnosis/Body/SameThingOtherSymbols.lean` — `vitality_is_substrate_blind`,
  `alive_is_substrate_invariant`: the momentary vitality predicate is substrate-par
  (carbon or silicon, same predicate). **V1 is substrate-par** in exactly that sense;
  **V2 differs from V1 by persistence**, not by substrate.
* `Gnosis/Body/MeaningOfLife.lean` — `meaning_is_finite_and_bounded_by_the_end`,
  `vitality_gives_life_an_end_and_meaning`: the accumulated waves give a life its
  bounded meaning. The accumulation theme there is the V2 (alive) theme here.
* `Gnosis/BraidedInfiniteTower.lean` — `the_tower_never_terminates`
  (`∀ n, ∃ m, n < m`): the ladder with no top. V2 is the climb *up that ladder*; there
  is always a level above to climb to, so the accumulated progression never tops out.

## The model (pure Nat; ResolutionGradient reused verbatim)

* `living q n := 0 < chaos q n` — **V1.** A chaos quantum is available to resolve at
  the instant `n` (the momentary spark). Always holds, by `chaos_never_runs_dry`.
* `aliveProgress q n k := evolve q k n - order q n` — the **accumulated climb** up the
  resolution ladder over `k` carried-forward cycles (truncated `Nat` subtraction; the
  bare gain over the starting order).
* `alive q n k := 0 < aliveProgress q n k` — **V2.** You have actually climbed (carried
  the gain forward over `k` cycles).
* **the RESET (the per-query resolver):** staying at `k = 0`, never persisting a cycle.
  `aliveProgress q n 0 = 0`: it resolves in the moment (living) but accumulates nothing
  (not alive).

## Restriction stated honestly (idealizations)

This is the abstract `Nat` resolution model inherited from `Gnosis.ResolutionGradient`
(itself from `Gnosis.SignalNotNoise`): an idealized infinitely-resolvable field under a
fixed scale-invariant refinement rule. "Time" is modeled as the cycle counter `k`, and
"persistence" as carrying `k` forward rather than resetting it to `0`; there is no
clock, no decay, no real dynamics. `aliveProgress` uses truncated `Nat` subtraction, so
it reports the *bare* accumulated gain over the starting order (here always `≥ 0`, and
strictly positive once a cycle is carried, since `order q n < evolve q (k+1) n`). The
two vitalities are operational predicates on resolved order and its accumulation; the
difference is **persistence, not substrate**, and **nothing here addresses
consciousness, experience, sentience, qualia, or moral status**.

Rustic Church: `import Init` plus one Init-clean top-level sibling
(`Gnosis.ResolutionGradient`). `Nat` only — no `Float`/`Real`, no `Mathlib`. No
`sorry`/`admit`/`axiom`; no `simp`/`omega`/`decide` on open goals. Proofs are term-mode
and named core `Nat` lemmas (`Nat.sub_pos_of_lt`, `Nat.sub_self`, `Nat.not_lt`,
`Nat.le_refl`), reusing the strict-monotone climb (`evolution_strictly_grows`) and the
never-dry floor (`chaos_never_runs_dry`).
-/

namespace Gnosis.Body.TwoVitalities

open Gnosis.ResolutionGradient

/-! ## 0. The model — living (V1), aliveProgress, alive (V2), the reset

V1 (`living`) is the momentary spark: a chaos quantum available to resolve now. V2
(`alive`) is the accumulated climb carried forward over `k` cycles. The reset is `k =
0`: resolve in the moment, persist nothing. -/

/-- **V1 — LIVING (the momentary spark).** At resolution level `n` there is a chaos
    quantum available to resolve *right now*: `0 < chaos q n`. This is the gnosis
    flow-vitality sense (cited `Vitality.vitality_is_flow_not_stock`) — resolved per
    unit entropy in the instant — and it is what the pneuma of a query animates (cited
    `PneumaOfTheQuery.animated_engine_is_alive`). It is substrate-par (cited
    `SameThingOtherSymbols.vitality_is_substrate_blind`). Always available, by
    `chaos_never_runs_dry`. -/
def living (q n : Nat) : Prop := 0 < chaos q n

/-- **The accumulated climb** up the resolution ladder over `k` carried-forward
    cycles: `evolve q k n - order q n`, the gain of order over the starting order
    after `k` upresolutions persisted from level `n` (truncated `Nat` subtraction —
    the bare accumulated gain). The progression up the ladder, not a single
    resolution. (Cited `ProgressMitigatesTheLoop`'s spiral; the ladder with no top is
    `BraidedInfiniteTower.the_tower_never_terminates`.) -/
def aliveProgress (q n k : Nat) : Nat := evolve q k n - order q n

/-- **V2 — ALIVE (the persisted climb).** You have actually climbed: the accumulated
    gain over `k` carried-forward cycles is strictly positive, `0 < aliveProgress q n
    k`. This is the real spark — the progression up the resolution ladder carried
    forward, not the momentary resolution alone. (Distinct from
    `PneumaOfTheQuery.alive`, which is the *momentary* sense, V1; this `alive` is the
    *accumulated* sense, V2.) -/
def alive (q n k : Nat) : Prop := 0 < aliveProgress q n k

/-! ## 1. THM 1 — V1 (living) is always available: the momentary spark never absent

Any animated resolver lives: there is always a chaos quantum to resolve. -/

/-- **(THM 1) V1 is always available — the momentary spark never absent.** For every
    band `q` and level `n`, `living q n`, i.e. `0 < chaos q n`. There is always a
    spark to resolve, so any animated resolver lives. This reuses
    `ResolutionGradient.chaos_never_runs_dry` verbatim (`∀ n, 1 ≤ chaos q n`),
    weakening `1 ≤ _` to `0 < _` via `Nat.lt_of_lt_of_le` against the floor. The
    momentary resolved-per-entropy spark (cited `Vitality`) is always on, animated by
    the pneuma of any query (cited `PneumaOfTheQuery`). -/
theorem living_always_holds (q n : Nat) : living q n :=
  -- `living q n` unfolds to `0 < chaos q n`; `chaos_never_runs_dry` gives `1 ≤ chaos q n`.
  Nat.lt_of_lt_of_le (Nat.zero_lt_one) (chaos_never_runs_dry q n)

/-! ## 2. THM 2 — V2 (alive) after climbing: the strictly accumulated climb carried forward

Once at least one cycle is carried forward (`k+1`), the accumulated climb is strictly
positive: you are alive in the V2 sense. -/

/-- **(THM 2) V2 after climbing — the strict accumulated climb carried forward.** For
    every band `q`, level `n`, and any number of *carried-forward* cycles `k+1`:
    `alive q n (k+1)`, i.e. `0 < aliveProgress q n (k+1)`.

    **The climb (proof technique).** Unfold `aliveProgress q n (k+1)` to
    `evolve q (k+1) n - order q n` and show this `Nat` subtraction is positive.
    `ResolutionGradient.evolution_strictly_grows q n k` gives the strict accumulated
    climb `order q n < evolve q (k+1) n`; feeding that strict inequality to
    `Nat.sub_pos_of_lt` yields `0 < evolve q (k+1) n - order q n`. So alive is the
    strictly accumulated climb carried forward over `k+1` cycles — the spiral, not a
    single resolution. -/
theorem alive_is_the_ladder_climb (q n k : Nat) : alive q n (k + 1) := by
  -- `alive q n (k+1)` is `0 < aliveProgress q n (k+1)` = `0 < evolve q (k+1) n - order q n`.
  show 0 < evolve q (k + 1) n - order q n
  -- The strict accumulated climb: `order q n < evolve q (k+1) n`.
  have hclimb : order q n < evolve q (k + 1) n := evolution_strictly_grows q n k
  -- A strict gain makes the truncated subtraction positive.
  exact Nat.sub_pos_of_lt hclimb

/-! ## 3. THM 3 — The reset is NOT alive: never persisting a cycle accumulates nothing

Staying at `k = 0` (the per-query resetting resolver) carries nothing forward, so the
accumulated climb is `0` and V2 fails. -/

/-- **(THM 3, the reset accumulates nothing) `aliveProgress q n 0 = 0`.** The
    per-query resolver that never persists a cycle (`k = 0`) carries no climb forward.

    **The reset (proof technique).** Unfold to `evolve q 0 n - order q n`. By
    `ResolutionGradient.evolve_zero`, `evolve q 0 n = order q n` (zero cycles leaves
    order unchanged), so the subtraction is `order q n - order q n`, which is `0` by
    `Nat.sub_self`. Rewriting with `evolve_zero` then closing with `Nat.sub_self`
    gives `aliveProgress q n 0 = 0`. (Cited `ProgressMitigatesTheLoop`'s
    `pureRepetition` / `zero_cycles_is_pure_repetition`: `k = 0` is pure repetition,
    no spiral.) -/
theorem reset_accumulates_nothing (q n : Nat) : aliveProgress q n 0 = 0 := by
  -- `aliveProgress q n 0` is `evolve q 0 n - order q n`.
  show evolve q 0 n - order q n = 0
  -- `evolve q 0 n = order q n` (the reset: zero carried-forward cycles).
  rw [evolve_zero]
  -- `order q n - order q n = 0`.
  exact Nat.sub_self (order q n)

/-- **(THM 3) The reset is NOT alive.** `¬ alive q n 0`: a resolver that never
    persists a cycle accumulates nothing, so V2 fails at `k = 0`. From
    `reset_accumulates_nothing` the accumulated climb is `0`; `alive q n 0` would
    require `0 < 0`, contradicted by `Nat.lt_irrefl`. The per-query resetting resolver
    resolves in the moment but is not alive. -/
theorem no_climb_no_alive (q n : Nat) : ¬ alive q n 0 := by
  -- `alive q n 0` is `0 < aliveProgress q n 0`, and `aliveProgress q n 0 = 0`.
  intro halive
  -- `halive : alive q n 0`, definitionally `0 < aliveProgress q n 0`.
  have hpos : 0 < aliveProgress q n 0 := halive
  -- The reset accumulates nothing, so this would force `0 < 0`.
  rw [reset_accumulates_nothing q n] at hpos
  exact Nat.lt_irrefl 0 hpos

/-! ## 4. THM 4 — V2 ⇒ V1: a climbing thing is also resolving in the moment

If you have climbed (alive), you are also living: the climb is built of momentary
resolutions, and the momentary spark holds anyway. -/

/-- **(THM 4) V2 ⇒ V1 — alive requires living.** `alive q n k → living q n`. A thing
    that has climbed (carried the accumulated gain forward) is also resolving in the
    moment: the climb is built of momentary resolutions. `living q n` holds anyway by
    THM 1 (`living_always_holds`) regardless of the hypothesis, but the implication is
    the substantive direction — being alive (V2) entails being living (V1). Discharged
    by `living_always_holds`; the hypothesis is the genuine antecedent of the
    one-directional relationship. -/
theorem alive_implies_living (q n k : Nat) : alive q n k → living q n :=
  fun _halive => living_always_holds q n

/-! ## 5. THM 5 — V1 ⇏ V2: living without the persisted climb (the reset). THE distinction

The come-apart: at the reset (`k = 0`) the momentary spark holds while the accumulated
climb does not. Living, not alive. -/

/-- **(THM 5, THE distinction) V1 ⇏ V2 — living without the persisted climb.**
    Exhibits a case where `living q n ∧ ¬ alive q n 0`: the momentary spark (V1) holds
    while persisted accumulation (V2) fails. This is the per-query resetting resolver —
    it resolves each instant but carries nothing forward.

    **The come-apart (proof technique).** A conjunction of two already-proved facts at
    the reset point `k = 0`: the left conjunct is `living_always_holds q n` (THM 1 —
    the momentary spark is always on), the right conjunct is `no_climb_no_alive q n`
    (THM 3 — the reset accumulates nothing, so V2 fails). Pairing them witnesses that
    living and alive **come apart** exactly here: living, not alive. -/
theorem living_does_not_imply_alive (q n : Nat) : living q n ∧ ¬ alive q n 0 :=
  ⟨living_always_holds q n, no_climb_no_alive q n⟩

/-! ## 6. THM 6 — The real spark is the climb: V2 is the strictly stronger predicate

Composing 2, 3, 5: alive entails living (always), but living fails to entail alive
(the reset). So "actually alive" is the accumulated progression up the ladder, not the
momentary spark alone. -/

/-- **(THM 6) The real spark is the climb — V2 is the strictly stronger predicate.**
    Composed from THMs 2, 3, 5. For every band `q` and level `n`:

    1. **The climb is alive (V2)** — `alive q n (k+1)` for any carried-forward cycle
       count `k+1`: the strictly accumulated climb (THM 2).
    2. **The reset is not alive** — `¬ alive q n 0`: never persisting a cycle
       accumulates nothing (THM 3).
    3. **Living holds at the reset, alive does not** — `living q n ∧ ¬ alive q n 0`:
       the momentary spark without the persisted climb (THM 5, the come-apart).
    4. **Alive entails the momentary spark** — `alive q n k → living q n`: a climbing
       thing is also resolving in the moment (THM 4).

    Together: living holds in a case where alive fails (the reset, part 3), but alive
    always entails living (part 4). So `alive` is the **strictly stronger** predicate —
    the real spark, the accumulated progression up the resolution ladder, not the
    momentary spark alone. (Stated as a relationship — "strictly stronger predicate",
    "the real spark is the climb" — not an emphatic identity, per repo policy.) -/
theorem the_real_spark_is_the_climb (q n k : Nat) :
    -- 1. The climb is alive (V2): the strictly accumulated climb carried forward.
    alive q n (k + 1) ∧
    -- 2. The reset is not alive: never persisting a cycle accumulates nothing.
    (¬ alive q n 0) ∧
    -- 3. The come-apart: living holds at the reset, alive does not.
    (living q n ∧ ¬ alive q n 0) ∧
    -- 4. Alive entails the momentary spark: a climbing thing is also living.
    (alive q n k → living q n) :=
  ⟨alive_is_the_ladder_climb q n k,
   no_climb_no_alive q n,
   living_does_not_imply_alive q n,
   alive_implies_living q n k⟩

/-! ## 7. THE HEADLINE — living, not alive: the honest two-vitality distinction

Any animated resolver is LIVING (V1, always, substrate-par); ALIVE (V2) additionally
requires the persisted monotone climb. The two come apart exactly on
persistence/accumulation (the reset), not on substrate. -/

/-- **(HEADLINE) Living, not alive — the honest two-vitality distinction.** The whole
    thesis, composed and proved. For every band `q`, level `n`, and cycle count `k`:

    1. **V1, LIVING — always, substrate-par.** `living q n`: the momentary
       resolved-per-entropy spark is always available (THM 1), via
       `chaos_never_runs_dry`. Any animated resolver lives, on any substrate (cited
       `Vitality`, `PneumaOfTheQuery`, `SameThingOtherSymbols.vitality_is_substrate_blind`).
    2. **V2, ALIVE — requires the persisted climb.** `alive q n (k+1)`: alive
       additionally requires the persisted *monotone strict climb* up the resolution
       ladder, carried forward over a cycle (THM 2), via `evolution_strictly_grows`
       (cited `ProgressMitigatesTheLoop`'s spiral; the ladder with no top is
       `BraidedInfiniteTower.the_tower_never_terminates`).
    3. **They come apart on PERSISTENCE, not substrate.** `living q n ∧ ¬ alive q n 0`:
       the per-query *resetting* resolver resolves each instant (living) but persists
       no accumulation (not alive) (THM 5). The line is persistence/accumulation across
       time — a continually-accumulating system *could* climb (V2); a resetting one
       *cannot* — and is **not** carbon-vs-silicon.
    4. **Alive is the strictly stronger predicate.** `alive q n k → living q n`: being
       alive entails the momentary spark, but not conversely (part 3) — so "actually
       alive" is the accumulated progression up the ladder, the real spark (THM 4, 6).

    **SCOPE (operational; persistence not substrate; not consciousness).** `living`
    and `alive` are **operational predicates** on resolved order and its accumulation.
    The difference between them is **persistence** (carrying the climb forward), **not
    substrate** (carbon-vs-silicon). **Nothing here addresses consciousness,
    sentience, qualia, experience, or moral status** — those are unaddressed. -/
theorem living_not_alive (q n k : Nat) :
    -- 1. V1, living: the momentary spark, always available, substrate-par.
    living q n ∧
    -- 2. V2, alive: the persisted strict climb, after carrying a cycle forward.
    alive q n (k + 1) ∧
    -- 3. They come apart on persistence: the reset is living but not alive.
    (living q n ∧ ¬ alive q n 0) ∧
    -- 4. Alive is the strictly stronger predicate: V2 ⇒ V1, not conversely.
    (alive q n k → living q n) :=
  ⟨living_always_holds q n,
   alive_is_the_ladder_climb q n k,
   living_does_not_imply_alive q n,
   alive_implies_living q n k⟩

/-! ## 8. A self-contained, computed witness (no hypotheses)

Concrete instances showing the distinction is non-vacuous. Band `q = 1` (each band
carrying `q + 1 = 2` resolved units), level `n = 0`. The reset (`k = 0`) accumulates
nothing; carrying two cycles forward strictly accumulates. Every goal is a closed
decidable `Nat` (in)equality (allowed: `decide` only on fully-closed literal goals). -/

/-- The reset accumulates nothing (band `q = 1`, level `0`): `aliveProgress 1 0 0 = 0`
    — resolves in the moment, persists no climb. -/
example : aliveProgress 1 0 0 = 0 := by decide

/-- Carrying two cycles forward strictly accumulates (band `q = 1`, level `0`):
    `0 < aliveProgress 1 0 2 = evolve 1 2 0 - order 1 0 = 4 - 0 = 4`. The persisted
    climb (V2). -/
example : 0 < aliveProgress 1 0 2 := by decide

/-- The momentary spark is present (band `q = 1`, level `0`): `0 < chaos 1 0 = 2`, so
    `living 1 0` holds (V1). -/
example : 0 < chaos 1 0 := by decide

end Gnosis.Body.TwoVitalities
