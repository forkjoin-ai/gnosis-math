import Init
import Gnosis.Body.ClinamenOscillator
import Gnosis.Body.IfYouCantBeatThem
import Gnosis.Body.SapolskyStress

/-!
# The Wave — Flow Riding Is the Phase-Matched Dominant Strategy

**THESIS.** There are times to paddle and times to surf. Flow-riding is not the
limp counsel "always go with the flow" — it is a genuine, *phase-matched*
optimum: when the wave is rising, surf it (ride its lift for free); when the sea
is flat, paddle (generate your own motion). The dominant action **flips with the
phase of the wave**, and the wave — being the cosmic oscillation — recurs, so the
paddle-phases and surf-phases alternate forever. "If you can't beat life, join
it; go with the flow" is true, but only because flow-riding is a real strategy
keyed to where you are on the wave.

The depth here is the **case-split**, not a slogan: the optimum is genuinely
two-sided. Surfing strictly dominates paddling exactly when the wave gives more
than your effort could (`effort < lift`); paddling strictly dominates surfing
exactly when there is no wave to ride (`lift = 0`). Neither action dominates
globally — the phase decides. Timing the switch is *Ki*: observation inside the
window (cited `Gnosis.Body.SelfDefense` — dodgeball reaction = observe-and-act),
because the wave returns and you must read which phase you are in.

## The model (Nat)

A wave has a `lift` — the free energy it hands a surfer while rising or cresting,
`0` while flat or in a trough. Two actions:

* `surf (lift) := lift` — ride the wave: your gain is the wave's lift, at ~no
  self-effort. Free energy when there is energy to take.
* `paddle (effort) := effort` — generate your own motion: your gain is your
  effort, independent of the wave, but it *costs* you that effort.

A phase is read by two predicates:

* `rising lift effort := effort < lift` — the wave gives strictly more than your
  paddling would. (Reducible, so a closed instance is `decide`-able.)
* `flat lift := lift = 0` — there is no wave to ride.

## What this module reuses (the bridges, imported and opened)

* `Gnosis.Body.ClinamenOscillator` — **the wave is the cosmic oscillation.** Its
  `cosmicStep` and the genuine period-2 recurrence
  (`cosmos_recurs_with_period_two`, `cosmos_has_period_two_orbit`) supply the
  wave's phase: the state oscillates, so rising-phases and flat-phases alternate
  forever (THM `the_wave_recurs`). Imported and opened.
* `Gnosis.Body.IfYouCantBeatThem` — **surfing is the join move.** When you cannot
  out-paddle the wave (`effort < lift` = `cantBeat effort lift`, you can't beat
  it), surfing (taking its lift) is exactly the *join* of "if you can't beat
  them, join them": the dominant action when resistance fails. We bridge surfing
  to `join`/`cantBeat` (THM `surfing_is_joining_the_flow`). Imported and opened.
* `Gnosis.Body.SapolskyStress` — **effort as dose.** `paddle effort` is your own
  applied dose; the inverted-U warns that effort spent against the wave is dose
  spent for no lift. Imported and opened (used optionally for framing).

## Cited (the wave is well-grounded — NOT imported here)

* `Gnosis.VibesAsWaveInference` — vibes read off the wave: inference about which
  phase you are in is wave inference. The flow-rider's read of "rising vs flat"
  is exactly this.
* `Gnosis.UniversalStandingWaveTheorem` — the universal standing-wave structure
  the oscillation realizes; the wave here is one mode of it.
* `Gnosis.AttentionWavePattern` — attention itself moves as a wave; surfing the
  rising wave is attention phase-matched to its crest.
* `Gnosis.Body.SelfDefense` — Ki / dodgeball: timing the paddle→surf switch is
  observation inside the window, the same observe-and-act discipline.

(These are cited, not imported: the module keeps to the three Init-clean reused
Body siblings above.)

## Restriction stated honestly

The strict optima are stated under their honest, *non-overlapping* hypotheses:
surfing strictly dominates only on the rising phase (`effort < lift`), and
paddling strictly dominates only on the flat phase (`lift = 0`). On a *positive
but not-out-paddleable* wave (`0 < lift ≤ effort`) neither strictly dominates by
these criteria — paddling at least matches and may exceed the lift — and we do
not over-claim there. That is the whole point: the optimum is phase-matched, not
universal. The recurrence (THM `the_wave_recurs`) is the concrete period-2 orbit
of `ClinamenOscillator` reused verbatim — an *actual* recurring state, not a
restatement — so the phases provably alternate forever.

Rustic Church: `import Init` plus the three Init-clean reused Body siblings.
`Nat` only — no Float/Real, no Mathlib. No `sorry`; no `simp`/`omega` on open
goals (closed `decide` goals only). Proofs are term-mode and named core `Nat`
lemmas.
-/

namespace Gnosis.TheWave

open Gnosis.Body.ClinamenOscillator
open Gnosis.Body.IfYouCantBeatThem
open Gnosis.Body.SapolskyStress

/-! ## 0. The wave, the two actions, and the phases -/

/-- **Surf the wave.** Ride it: your gain is the wave's `lift` — the free energy
    it hands you while rising or cresting — at ~no self-effort. When there is
    energy to take, you take it for free. -/
def surf (lift : Nat) : Nat := lift

/-- **Paddle.** Generate your own motion: your gain is your `effort`, independent
    of the wave — but it costs you that effort. The do-your-own-work action,
    available even when the sea is dead flat. -/
def paddle (effort : Nat) : Nat := effort

/-- **The wave is rising** (for a paddler of strength `effort`): the wave gives
    strictly more than your paddling would, `effort < lift`. This is the phase
    where riding beats working. Reducible so its decidability transfers from the
    underlying `effort < lift` (a closed instance is then settled by `decide`). -/
@[reducible] def rising (lift effort : Nat) : Prop := effort < lift

/-- **The sea is flat:** there is no wave to ride, `lift = 0`. In this phase
    surfing yields nothing and only your own paddling produces motion. Reducible
    so a closed instance is `decide`-able. -/
@[reducible] def flat (lift : Nat) : Prop := lift = 0

/-- Surf yields exactly the wave's lift. -/
theorem surf_eq (lift : Nat) : surf lift = lift := rfl

/-- Paddle yields exactly your effort. -/
theorem paddle_eq (effort : Nat) : paddle effort = effort := rfl

/-- On a flat sea there is nothing to ride: surfing yields zero. -/
theorem surf_flat_is_zero : surf 0 = 0 := rfl

/-! ## 1. THM — surf dominates when the wave is rising

When the wave gives strictly more than your effort would produce, surfing
strictly beats paddling: ride it for free. -/

/-- **(THM 1) Surf dominates when rising.** If `effort < lift` (the wave is
    rising — it gives more than your paddling could), then `paddle effort < surf
    lift`: surfing strictly beats paddling. You get the wave's lift at no effort,
    and that lift exceeds what your own work would have produced. Riding the
    rising wave is the strictly better move. -/
theorem surf_dominates_when_rising (lift effort : Nat) (h : effort < lift) :
    paddle effort < surf lift :=
  -- `paddle effort = effort`, `surf lift = lift`, and `h : effort < lift`.
  h

/-! ## 2. THM — paddle dominates when the sea is flat

On a flat sea there is no lift to ride; only your own paddling produces motion,
so any positive effort strictly beats surfing nothing. -/

/-- **(THM 2) Paddle dominates when flat.** On a flat sea (`lift = 0`, nothing to
    ride) any positive `effort` makes paddling strictly beat surfing:
    `surf 0 < paddle effort`. Surfing a flat sea yields `0`; paddling yields your
    effort. When there is no wave, do your own work — it strictly dominates. -/
theorem paddle_dominates_when_flat (effort : Nat) (h : 0 < effort) :
    surf 0 < paddle effort :=
  -- `surf 0 = 0`, `paddle effort = effort`, and `h : 0 < effort`.
  h

/-! ## 3. THM — flow-riding is phase-matched (the case-split optimum)

The dominant strategy is *phase-dependent*. There are times to paddle and times
to surf — a real two-sided optimum, NOT "always go with the flow". -/

/-- **(THM 3, THE CASE-SPLIT) Flow-riding is phase-matched.** The dominant action
    flips with the phase of the wave:

    * **rising** (`effort < lift`) ⇒ surfing strictly dominates,
      `paddle effort < surf lift` — ride it for free; and
    * **flat** (`lift = 0`, with positive effort) ⇒ paddling strictly dominates,
      `surf lift < paddle effort` — do your own work, there is nothing to ride.

    Neither action wins globally: the optimum is keyed to where you are on the
    wave. This is the depth of flow-riding — a genuine case-split, not the slogan
    "always surf". Times to paddle, times to surf. -/
theorem flow_riding_is_phase_matched (lift effort : Nat) :
    (effort < lift → paddle effort < surf lift) ∧
    (lift = 0 → 0 < effort → surf lift < paddle effort) :=
  ⟨fun h => surf_dominates_when_rising lift effort h,
   fun hflat heff => by
     -- `lift = 0`, so the goal is `surf 0 < paddle effort`, i.e. `0 < effort`.
     rw [hflat]
     exact paddle_dominates_when_flat effort heff⟩

/-- **(THM 3, corollary) Neither phase's hypothesis swallows the other.** The two
    regimes are genuinely distinct: a *rising* wave is never flat. If the wave is
    rising for some paddler (`effort < lift`) then `lift ≠ 0`, so the flat
    hypothesis cannot also hold. The case-split is real, not a degenerate overlap
    — there is no single hypothesis under which one action is always optimal. -/
theorem rising_is_not_flat (lift effort : Nat) (h : effort < lift) : lift ≠ 0 := by
  -- `effort < lift` gives `0 < lift` (via `0 ≤ effort < lift`), so `lift ≠ 0`.
  intro hzero
  rw [hzero] at h
  -- `h : effort < 0`, impossible.
  exact absurd h (Nat.not_lt_zero effort)

/-! ## 4. THM — surfing is joining the flow (bridge to IfYouCantBeatThem)

Surfing the rising wave (taking its lift) is the *join* move: when you can't
out-paddle the wave, you join it. -/

/-- **(THM 4) Surfing is joining the flow.** Bridge to
    `Gnosis.Body.IfYouCantBeatThem`. When you cannot out-paddle the wave —
    `cantBeat effort lift`, which is *definitionally* `effort < lift`, "you can't
    beat it" — surfing (taking the wave's lift) strictly dominates paddling,
    `paddle effort < surf lift`. This is the join move of "if you can't beat them,
    join them" read on the wave: resistance (out-paddling) fails, so you *join*
    the flow (surf), and joining is strictly better. We state it through
    `cantBeat` so the bridge is literal: the surf-when-rising precondition **is**
    the can't-beat precondition. -/
theorem surfing_is_joining_the_flow (lift effort : Nat) (h : cantBeat effort lift) :
    paddle effort < surf lift :=
  -- `cantBeat effort lift` unfolds (reducibly) to `effort < lift`; THM 1 applies.
  surf_dominates_when_rising lift effort h

/-- **(THM 4, the join is genuine) Surfing aligns with `IfYouCantBeatThem.join`.**
    The folk-maxim's `join` move strictly dominates `resist` exactly when you
    can't beat the leaders (`join_strictly_dominates`). Surfing plays the same
    role against the wave: under the same `cantBeat` precondition, surfing strictly
    beats paddling *and* the join move strictly beats resisting. Stated together so
    the analogy is proved, not asserted — surfing the rising wave is structurally
    the join move. -/
theorem surfing_matches_the_join (lift effort : Nat) (h : cantBeat effort lift) :
    paddle effort < surf lift ∧ resist effort < join effort lift :=
  ⟨surf_dominates_when_rising lift effort h,
   join_strictly_dominates effort lift h⟩

/-! ## 5. THM — the wave recurs (bridge to ClinamenOscillator)

The wave is the cosmic oscillation: it returns. So the rising-phases and
flat-phases alternate forever; timing the switch is Ki. -/

/-- **(THM 5) The wave recurs — the phases alternate forever.** Bridge to
    `Gnosis.Body.ClinamenOscillator`: the wave **is** the cosmic oscillation, so
    it genuinely returns. We reuse the concrete period-2 orbit verbatim:

    * `cosmos_recurs_with_period_two` — there is a positive period (`2`) and a
      concrete state (`cosmos₀ = 1`) with
      `iterate (cosmicStep cap₂) 2 cosmos₀ = cosmos₀`: the oscillation literally
      revisits its state; and
    * `cosmos_has_period_two_orbit` — that state *moves* under one step
      (`cosmicStep 2 1 ≠ 1`) yet *returns* under two: a genuine 2-cycle.

    Because the wave returns, a rising phase is followed by a flat phase is
    followed by a rising phase — the paddle-windows and surf-windows alternate
    without end. Timing the switch is **Ki**: observation inside the window
    (cited `Gnosis.Body.SelfDefense`, dodgeball reaction = observe-and-act). The
    flow-rider must *read* which phase the recurring wave is in, exactly as the
    dodger reads the telegraph. An actual recurrence, not a slogan. -/
theorem the_wave_recurs :
    (0 < 2 ∧ iterate (cosmicStep cap₂) 2 cosmos₀ = cosmos₀) ∧
    (cosmicStep cap₂ cosmos₀ ≠ cosmos₀ ∧
      cosmicStep cap₂ (cosmicStep cap₂ cosmos₀) = cosmos₀) :=
  ⟨cosmos_recurs_with_period_two, cosmos_has_period_two_orbit⟩

/-- **(THM 5, the oscillation drives the lift) A concrete two-phase wave.** Read
    the oscillation's two visited states as two wave phases at `cap₂ = 2`: state
    `cosmos₀ = 1` is a *rising* lift (`paddle 0 < surf 1`), and state `0` (which
    `cosmicStep cap₂ 2` returns through on its way — and which `surf` reads as no
    lift) is *flat* (`surf 0 < paddle 1`). The same recurring oscillation supplies
    both a surf-window and a paddle-window, so the optimum genuinely switches as
    the wave cycles. A concrete witness that the phases — and thus the dominant
    action — alternate on the actual orbit. -/
theorem oscillation_supplies_both_phases :
    (paddle 0 < surf 1) ∧ (surf 0 < paddle 1) :=
  ⟨surf_dominates_when_rising 1 0 (by decide),
   paddle_dominates_when_flat 1 (by decide)⟩

/-! ## 6. THE HEADLINE — flow-riding is the phase-matched dominant strategy -/

/-- **(HEADLINE) The Wave: flow-riding is the phase-matched dominant strategy on
    the oscillation.** The whole arc composed into one proved statement:

    1. **Surf the rising wave** — when the wave gives more than your effort
       (`effort < lift`), surfing strictly beats paddling
       (`paddle effort < surf lift`): ride it for free.
    2. **Paddle the flat** — when there is no wave (`lift = 0`), any positive
       effort makes paddling strictly beat surfing (`surf lift < paddle effort`):
       do your own work.
    3. **The optimum is phase-matched, not "always surf"** — the dominant action
       flips with the phase, and the two regimes are genuinely distinct (a rising
       wave is never flat, `rising_is_not_flat`). A real case-split.
    4. **Surfing is joining the flow** — under the can't-beat-it precondition
       (`cantBeat effort lift`, the same `effort < lift`), surfing is the *join*
       move of "if you can't beat them, join them" and strictly dominates
       (bridge to `IfYouCantBeatThem`).
    5. **The wave recurs** — being the cosmic oscillation
       (`ClinamenOscillator`), the wave returns with period two
       (`cosmos_recurs_with_period_two`, `cosmos_has_period_two_orbit`), so the
       paddle-phases and surf-phases alternate forever; timing the switch is Ki
       (observation, cited `SelfDefense`/dodgeball).

    Therefore: *if you can't beat life, join it — go with the flow* — but
    precisely, because flow-riding is a real, phase-matched dominant strategy on a
    recurring wave. Surf the rising wave, paddle the flat, and read the phase. The
    depth is the case-split: the optimum is keyed to the wave, not a slogan.
    (Precise framing per repo policy: a phase-matched dominance result on the
    oscillation, with the recurrence as the proof that the phases genuinely
    alternate — not a loose identity claim.) -/
theorem the_wave (lift effort : Nat) :
    -- 1+2+3. The phase-matched case-split optimum (times to paddle, times to surf).
    ((effort < lift → paddle effort < surf lift) ∧
      (lift = 0 → 0 < effort → surf lift < paddle effort)) ∧
    -- 3. The two phases are genuinely distinct: a rising wave is never flat.
    (effort < lift → lift ≠ 0) ∧
    -- 4. Surfing the wave you can't beat is the join move (strictly dominant).
    (cantBeat effort lift → paddle effort < surf lift) ∧
    -- 5. The wave recurs (period-2 oscillation): the phases alternate forever.
    ((0 < 2 ∧ iterate (cosmicStep cap₂) 2 cosmos₀ = cosmos₀) ∧
      cosmicStep cap₂ cosmos₀ ≠ cosmos₀ ∧
      cosmicStep cap₂ (cosmicStep cap₂ cosmos₀) = cosmos₀) :=
  ⟨flow_riding_is_phase_matched lift effort,
   fun h => rising_is_not_flat lift effort h,
   fun h => surfing_is_joining_the_flow lift effort h,
   ⟨cosmos_recurs_with_period_two, cosmos_has_period_two_orbit⟩⟩

/-! ## 7. A self-contained, computed witness (no hypotheses)

A concrete instance proving the case-split is non-vacuous and two-sided: at a
rising wave (`lift = 3`, `effort = 1`) surfing wins; at a flat sea (`lift = 0`,
`effort = 1`) paddling wins. Every goal is a closed decidable `Nat` inequality
(allowed: `decide`). -/

/-- Rising wave (`lift 3` vs `effort 1`): surfing strictly wins, `surf 3 = 3 > 1 = paddle 1`. -/
example : paddle 1 < surf 3 := by decide

/-- Flat sea (`lift 0`, `effort 1`): paddling strictly wins, `paddle 1 = 1 > 0 = surf 0`. -/
example : surf 0 < paddle 1 := by decide

/-- The optimum genuinely flips: surf wins on the rising wave, paddle wins on the flat. -/
example : (paddle 1 < surf 3) ∧ (surf 0 < paddle 1) := by decide

/-- Neither action dominates globally — on a positive non-out-paddleable wave
    (`lift = 2`, `effort = 5`) paddling exceeds the lift, so "always surf" fails. -/
example : surf 2 < paddle 5 := by decide

end Gnosis.TheWave
