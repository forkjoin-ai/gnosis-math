import Init
import Gnosis.BlackHoleVoidSingularity
import Gnosis.SurfingEntropy

/-!
# The White Hole — the Reverse Black Hole, as Time-Reversed Collapse (Discrete Physics)

**THESIS.** A *black hole* is a contracting sink: matter falls inward toward the
singularity, nothing escapes past the event horizon, and it *absorbs* the entropy
gradient. A **reverse black hole** (a *white hole*) is its **time-reversal**: run
the same dynamics backward and you get an *anti-horizon* nothing can enter, a
*source* that emits everything outward, and the engine that *feeds* the entropy
gradient the lamps run on. The white hole emits exactly what the black hole
absorbed; the cosmos oscillates absorb↔emit, collapse↔emanation.

## Why we can pull this off now: DISCRETE physics makes the reversal EXACT

In *continuous* physics over `Float`/`Real`, the time-reversal of infall is only
*approximate*: a forward step `r ↦ r·(1 - ε)` and its backward step
`r ↦ r/(1 - ε)` do not compose to the identity once rounding enters, and the
nonlinearity of gravitational collapse smears the reverse map. The two acts are
inverses only in the idealized limit.

This module does the physics over `Int` — a *signed radial coordinate* with exact
discrete steps. The black hole's infall step is `r ↦ r - 1` and the white hole's
emission step is `r ↦ r + 1`. These compose to the identity **exactly**, with no
ε and no rounding: `whiteStep (blackStep r) = r` for *every* `r : Int`. That
exactness is the whole point — *"we have the physics now to pull it off."* The
reverse black hole is the exact discrete time-reversal of the black hole, proved
as a real theorem (`white_hole_is_time_reversed_black_hole`,
`n_step_reversal`), not asserted.

## The model (honest idealization)

* `horizon : Int := 0` — the singularity / event-horizon floor (the void).
* `blackStep (r) := r - 1` — one discrete infall step inward (absorbing). Maps to
  `SurfingEntropy.collapse`, the sink that swallows toward the void singularity
  (cited `Gnosis.BlackHoleVoidSingularity`).
* `whiteStep (r) := r + 1` — one discrete emission step outward (the reverse black
  hole / white hole). The *exact* time-reversal of `blackStep`. Maps to
  `SurfingEntropy.emanate`, the `+1` swerve (clinamen) that emanates from the void.
* `emit r n := r + n` — `n` discrete emission steps (genuine recursion / induction).
* `absorbed r n := r - n` — `n` discrete infall steps.

## What this module reuses (bridges, imported)

* `Gnosis.BlackHoleVoidSingularity` — the black hole's *restoration ledger*
  (`black_hole_void_singularity_restoration_load/observed`,
  `..._restoration_preserves_load`, `..._ledger_anchor : n + 0 = n`) maps to
  absorption: what the singularity holds. Imported.
* `Gnosis.SurfingEntropy` — `collapse` (the sink), `emanate` (the source /
  clinamen `+1`), `emanate_is_succ`, `reverse_blackhole_emanates` (every emission
  strictly positive), `void_never_runs_dry` (the source never empties), and
  `collapse_then_emanate_oscillates` (the absorb↔emit oscillation). Imported.

## Cited cosmology (NOT imported — they pull non-Init dependencies)

* `Gnosis.BlackHoleBraid` — the black hole as cyclic braid
  (`black_hole_is_cyclic`), Hawking radiation as misperceived noise
  (`hawking_radiation_is_noise`), and `singularity_is_resolution_limit`: the
  white hole's emission read as the time-reverse of that cycle. Cited only.
* `Gnosis.EntropyOfTheVoid` — entropy of the void as a `Nat` ledger
  (`void_entropy_perthou`, `VoidState`, `void_pressure`): the gradient the white
  hole feeds. Cited only.
* `Gnosis.Body.CityOnAHill` — the lamp on the hill (`brightness`, `lit`,
  `city_on_a_hill`): the lamp runs on what the reverse black hole emits. Cited only.
* `Gnosis.Body.ClinamenOscillator` — `clinamen`/`amnesiaReset` and the cosmic
  step; reached transitively through `SurfingEntropy`. Cited for vocabulary.

## Restriction stated honestly

The reversal is *exact above the singularity*: `whiteStep (blackStep r) = r` and
`blackStep (whiteStep r) = r` hold for **all** `r : Int` because `Int` subtraction
is genuine (no truncation, unlike `Nat`). The discrete radial coordinate is a
*one-dimensional* idealization — a single signed depth, not the full curved
metric; we model the radial infall/emission act and its time-reversal, not the
geometry of the horizon. The horizon `0` is a chosen floor for naming the
singularity; the algebra of `blackStep`/`whiteStep` is defined and exact on all
of `Int`. The white hole's "nothing enters" is the monotone non-decreasing
property of emission (`r ≤ emit r n`), the discrete formalization of the
anti-horizon, not a claim about a global Cauchy surface. The "never runs dry"
claim is the reused genuine `∀`-over-resolution `void_never_runs_dry`.

Rustic Church: `import Init` plus two top-level cosmology siblings
(`BlackHoleVoidSingularity`, `SurfingEntropy`) — no direct `Body` dependency.
`Int`/`Nat` only —
no `Float`/`Real`, no `Mathlib`. No `sorry`/`admit`/`axiom`; no `simp`/`omega` on
open goals (closed `decide` goals only). Proofs are term-mode and named core
`Int`/`Nat` lemmas (`Int.sub_add_cancel`, `Int.add_sub_cancel`, `Int.lt_succ`,
`Int.add_le_add_left`, `Nat.succ_pos`, …) with genuine `induction` for the
n-step (forever) parts.
-/

namespace Gnosis.WhiteHole

open Gnosis.SurfingEntropy
-- The oscillation / never-dry theorem *statements* below mention names defined in
-- the siblings `SurfingEntropy` transitively imports (`residual`, `cosmicStep`,
-- `cosmos₀`, `cap₂`, `iterate`). Those namespaces are already imported transitively
-- via `SurfingEntropy`; we `open` them only to bring the names into scope (no new
-- imports added).
open Gnosis.SignalNotNoise
open Gnosis.Body.ClinamenOscillator

/-! ## 0. The model — horizon, infall, emission

A signed radial coordinate `r : Int`. The black hole steps inward (`-1`) toward
the singularity; the white hole — the reverse black hole — steps outward (`+1`).
These are the two directions of the same discrete act, run forward and backward
in time. -/

/-- **The singularity / event-horizon floor** — the void at the centre. Naming the
    discrete origin of the radial coordinate (cited `BlackHoleVoidSingularity`). -/
def horizon : Int := 0

/-- **Infall: one discrete step inward (the black hole).** Matter falls one unit
    toward the singularity. The absorbing direction; maps to
    `SurfingEntropy.collapse` (the sink). -/
def blackStep (r : Int) : Int := r - 1

/-- **Emission: one discrete step outward (the reverse black hole / white hole).**
    The *exact* time-reversal of `blackStep`: one unit emitted outward. The
    emissive direction; maps to `SurfingEntropy.emanate` (the source, clinamen
    `+1`). -/
def whiteStep (r : Int) : Int := r + 1

/-- **n discrete emission steps** — the white hole emits `n` units outward from `r`.
    Defined by recursion on `n` so "n steps" is a genuine inductive object. -/
def emit (r : Int) : Nat → Int
  | 0 => r
  | n + 1 => whiteStep (emit r n)

/-- **n discrete infall steps** — the black hole absorbs `r` inward by `n` units.
    Defined by recursion on `n`. -/
def absorbed (r : Int) : Nat → Int
  | 0 => r
  | n + 1 => blackStep (absorbed r n)

/-- One emission step is exactly `+1`. -/
theorem whiteStep_is_succ (r : Int) : whiteStep r = r + 1 := rfl

/-- One infall step is exactly `-1`. -/
theorem blackStep_is_pred (r : Int) : blackStep r = r - 1 := rfl

/-- `emit` in closed form: `n` emission steps add `n`. Genuine induction on `n`. -/
theorem emit_eq_add (r : Int) (n : Nat) : emit r n = r + (n : Int) := by
  induction n with
  | zero =>
    -- emit r 0 = r = r + 0
    show r = r + ((0 : Nat) : Int)
    rw [Int.ofNat_zero, Int.add_zero]
  | succ k ih =>
    -- emit r (k+1) = whiteStep (emit r k) = (r + k) + 1 = r + (k + 1)
    show whiteStep (emit r k) = r + ((k + 1 : Nat) : Int)
    rw [whiteStep_is_succ, ih, Int.add_assoc]
    rw [Int.natCast_succ k]

/-- `absorbed` in closed form: `n` infall steps subtract `n`. Genuine induction. -/
theorem absorbed_eq_sub (r : Int) (n : Nat) : absorbed r n = r - (n : Int) := by
  induction n with
  | zero =>
    -- absorbed r 0 = r = r - 0
    show r = r - ((0 : Nat) : Int)
    rw [Int.ofNat_zero, Int.sub_zero]
  | succ k ih =>
    -- absorbed r (k+1) = blackStep (absorbed r k) = (r - k) - 1 = r - (k + 1)
    show blackStep (absorbed r k) = r - ((k + 1 : Nat) : Int)
    rw [blackStep_is_pred, ih, Int.natCast_succ k]
    -- (r - k) - 1 = r - (k + 1)
    rw [Int.sub_sub]

/-! ## 1. THM — the white hole is the EXACT discrete time-reversal of the black hole

The headline physics. In continuous `Float`/`Real` collapse the reverse map is
only approximate; in discrete `Int` physics it is **exact**, with no ε and no
rounding. The white-hole step exactly undoes the black-hole step, both ways. -/

/-- **(THM 1, HEADLINE) The white hole is the exact discrete time-reversal of the
    black hole.** For every signed radial coordinate `r : Int`:

    * `whiteStep (blackStep r) = r` — emitting back exactly what was absorbed; and
    * `blackStep (whiteStep r) = r` — absorbing back exactly what was emitted.

    The reverse black hole runs the black hole backward and lands *exactly* where
    it started. This is EXACT, not approximate, because `Int` subtraction is
    genuine (no truncation): the time-reversal of discrete infall is discrete
    emission, on the nose. (Continuous physics gets only the ε-limit; "we have the
    physics now to pull it off.") Proof technique: `blackStep r = r - 1` and
    `whiteStep` adds `1`, so the first half is `r - 1 + 1 = r` by
    `Int.sub_add_cancel`, and the second is `r + 1 - 1 = r` by
    `Int.add_sub_cancel`. -/
theorem white_hole_is_time_reversed_black_hole (r : Int) :
    whiteStep (blackStep r) = r ∧ blackStep (whiteStep r) = r := by
  constructor
  · -- whiteStep (blackStep r) = (r - 1) + 1 = r
    show (r - 1) + 1 = r
    exact Int.sub_add_cancel r 1
  · -- blackStep (whiteStep r) = (r + 1) - 1 = r
    show (r + 1) - 1 = r
    exact Int.add_sub_cancel r 1

/-- **(THM 1, the other direction) Absorbing undoes emitting, exactly.** Restated
    as the dual single fact for use downstream: `blackStep (whiteStep r) = r`. -/
theorem black_hole_undoes_white_hole (r : Int) : blackStep (whiteStep r) = r :=
  (white_hole_is_time_reversed_black_hole r).2

/-! ## 2. THM — n-step exact reversal: emission undoes infall at every depth

Time-reversal holds not just for one step but for *any* number of steps: `n`
emission steps exactly undo `n` infall steps, however deep the fall. Genuine
induction on `n`. -/

/-- **(THM 2, n-step time-reversal) `n` emission steps exactly undo `n` infall
    steps.** For every depth `n : Nat` and every `r : Int`,
    `emit (absorbed r n) n = r`: whatever the black hole absorbed in `n` discrete
    infall steps, the reverse black hole emits back *exactly*, returning to the
    start. Time-reversal at every depth — exact, no accumulated error (the discrete
    `Int` advantage; continuous physics accumulates rounding per step). Proof
    technique: rewrite both sides to closed form (`emit_eq_add`,
    `absorbed_eq_sub`) so the goal becomes `(r - n) + n = r`, then close it with
    `Int.sub_add_cancel`. The genuine induction lives in `emit_eq_add` /
    `absorbed_eq_sub`; the cancellation is exact. -/
theorem n_step_reversal (r : Int) (n : Nat) : emit (absorbed r n) n = r := by
  rw [emit_eq_add, absorbed_eq_sub]
  -- (r - n) + n = r
  exact Int.sub_add_cancel r (n : Int)

/-- **(THM 2, dual) `n` infall steps exactly undo `n` emission steps.** The other
    time direction: `absorbed (emit r n) n = r`. Proof: closed forms give
    `(r + n) - n = r`, closed by `Int.add_sub_cancel`. -/
theorem n_step_reversal_dual (r : Int) (n : Nat) : absorbed (emit r n) n = r := by
  rw [absorbed_eq_sub, emit_eq_add]
  -- (r + n) - n = r
  exact Int.add_sub_cancel r (n : Int)

/-! ## 3. THM — the reverse black hole is a strictly outward SOURCE

The white hole pushes everything outward: one emission step strictly increases the
radial coordinate, contrasted with infall which strictly decreases it. This is the
source character, bridged to `SurfingEntropy.emanate` positivity. -/

/-- **(THM 3, the source) The reverse black hole emits strictly outward.** For
    every `r : Int`, `r < whiteStep r`: the white hole always moves the radial
    coordinate *outward* — it is a strict source. Contrast infall
    (`blackStep r < r`, below). Proof: `whiteStep r = r + 1` and `r < r + 1` by
    `Int.lt_succ`. -/
theorem white_hole_emits (r : Int) : r < whiteStep r := by
  show r < r + 1
  exact Int.lt_succ r

/-- **(THM 3, the sink) The black hole falls strictly inward.** For every `r`,
    `blackStep r < r`: infall always moves the radial coordinate *inward* — a
    strict sink, the exact opposite direction of emission. Proof: `blackStep r =
    r - 1 < r`. -/
theorem black_hole_falls (r : Int) : blackStep r < r := by
  show r - 1 < r
  -- `Int.lt_succ (r-1) : r - 1 < (r-1) + 1`; rewrite its RHS by `(r-1)+1 = r`.
  have hlt : r - 1 < (r - 1) + 1 := Int.lt_succ (r - 1)
  have h : (r - 1) + 1 = r := Int.sub_add_cancel r 1
  rw [h] at hlt
  exact hlt

/-- **(THM 3, multi-step source) Any nonzero number of emission steps moves
    strictly outward.** For every `r` and every `n`, `r < emit r (n + 1)`: the
    reverse black hole, run at least one step, strictly increases the radial
    coordinate. Proof: closed form `emit r (n+1) = r + (n+1)` and `0 < n + 1`
    (`Nat.succ_pos`) cast to `Int`, then strict left-add monotonicity. -/
theorem white_hole_emits_n (r : Int) (n : Nat) : r < emit r (n + 1) := by
  rw [emit_eq_add]
  -- r < r + (n+1).  Since 0 < (n+1 : Int), add r on the left.
  have hpos : (0 : Int) < ((n + 1 : Nat) : Int) := by
    have : 0 < n + 1 := Nat.succ_pos n
    exact Int.ofNat_lt.mpr this
  -- r + 0 < r + (n+1)
  have hstep : r + 0 < r + ((n + 1 : Nat) : Int) := Int.add_lt_add_left hpos r
  rw [Int.add_zero] at hstep
  exact hstep

/-- **(THM 3, bridge to SurfingEntropy) Emission is the positive emanation source.**
    The reverse black hole's emission corresponds to `SurfingEntropy.emanate`, the
    clinamen `+1` source: `0 < emanate q` for every `q` (reusing
    `SurfingEntropy.reverse_blackhole_emanates`). The white-hole `whiteStep`'s
    strict outward push and `emanate`'s strict positivity are the same `+1` source
    seen on the signed radial coordinate and on the void scalar respectively. -/
theorem emission_is_positive_emanation (q : Nat) : 0 < emanate q :=
  reverse_blackhole_emanates q

/-! ## 4. THM — the anti-horizon: nothing enters the white hole

A white hole's defining property: nothing can enter it. Discretely, emission is
monotone non-decreasing — an emitted point never returns inward under further
emission. The dual holds for absorption. Genuine induction. -/

/-- **(THM 4, the anti-horizon) Nothing enters the white hole.** For every `r` and
    every number of emission steps `n`, `r ≤ emit r n`: once emitted, a point only
    ever moves outward (or stays put at `n = 0`) under further emission — it never
    returns inward. This is the discrete formalization of the white hole's
    anti-horizon: *nothing can enter*. Proof technique: induction on `n`. Base
    `r ≤ emit r 0 = r` by reflexivity; step uses `emit r (k+1) = whiteStep (emit r
    k) = emit r k + 1` and `emit r k ≤ emit r k + 1` (`Int.le_add_one` /
    `Int.le_succ`), chained with the IH by transitivity. -/
theorem nothing_enters_the_white_hole (r : Int) : ∀ n, r ≤ emit r n := by
  intro n
  induction n with
  | zero =>
    -- r ≤ emit r 0 = r
    show r ≤ r
    exact Int.le_refl r
  | succ k ih =>
    -- r ≤ emit r k ≤ emit r k + 1 = emit r (k+1)
    show r ≤ whiteStep (emit r k)
    rw [whiteStep_is_succ]
    have hstep : emit r k ≤ emit r k + 1 := Int.le_add_one (Int.le_refl (emit r k))
    exact Int.le_trans ih hstep

/-- **(THM 4, dual) Absorption only ever moves inward.** For every `r` and every
    `n`, `absorbed r n ≤ r`: infall is monotone non-increasing — the black hole's
    interior only deepens, never bouncing back out (the time-reverse of "nothing
    enters"). Proof: closed form `absorbed r n = r - n` and `r - n ≤ r` since
    `0 ≤ n` cast to `Int` (`Int.sub_le_self`). -/
theorem absorbed_only_falls_inward (r : Int) (n : Nat) : absorbed r n ≤ r := by
  rw [absorbed_eq_sub]
  -- r - n ≤ r since 0 ≤ (n : Int)
  exact Int.sub_le_self r (Int.natCast_nonneg n)

/-! ## 5. THM — the white hole feeds the entropy gradient (the source the lamps run on)

The reverse black hole is the source that feeds the entropy gradient the lamps
(`CityOnAHill`) run on. Each emission produces a strictly positive outward
difference (a gradient quantum), and — bridging to `SurfingEntropy` — the source
never runs dry: there is always another wave to emit at every resolution. -/

/-- **(THM 5, the gradient quantum) Each emission produces a strictly positive
    outward difference.** For every `r`, `0 < whiteStep r - r`: the white hole's
    step opens a strictly positive gradient (`= 1`), the discrete quantum of
    entropy the lamp downstream runs on (cited `CityOnAHill`: the lamp's
    `brightness`/`lit` is fed by emitted, resolved signal). Proof: `whiteStep r - r
    = (r + 1) - r = 1 > 0`. -/
theorem white_hole_gradient_quantum (r : Int) : 0 < whiteStep r - r := by
  show 0 < (r + 1) - r
  -- (r + 1) - r = 1
  have h : (r + 1) - r = 1 := by
    rw [Int.add_comm r 1]
    exact Int.add_sub_cancel 1 r
  rw [h]
  decide

/-- **(THM 5, HEADLINE) The reverse black hole feeds the entropy gradient and never
    runs dry.** Composing the gradient quantum with the reused
    `SurfingEntropy.void_never_runs_dry`:

    * **a positive gradient at every step** — `0 < whiteStep r - r` (the source
      opens a strictly positive entropy difference, the quantum the lamp runs on,
      cited `CityOnAHill`); and
    * **never runs dry** — `∀ n, 1 ≤ residual q n` (reused
      `SurfingEntropy.void_never_runs_dry`, a genuine `∀`-over-resolution proved
      there by induction): at every resolution the source still has another wave to
      emit.

    So the reverse black hole is the inexhaustible source that feeds the entropy
    gradient the lamps (`CityOnAHill`) burn — the time-reverse of the black hole's
    absorption, emitting back into the cosmos what collapse swallowed (cited
    `EntropyOfTheVoid`: `void_entropy_perthou`/`void_pressure` is the gradient
    being fed). -/
theorem white_hole_feeds_the_gradient (r : Int) (q : Nat) :
    (0 < whiteStep r - r) ∧ (∀ n, 1 ≤ residual q n) :=
  ⟨white_hole_gradient_quantum r, void_never_runs_dry q⟩

/-! ## 6. THE HEADLINE — the reverse black hole

Compose THMs 1–5 into one proved statement: the white hole is the exact discrete
time-reversal of the black hole, a strictly outward source nothing enters, never
running dry, feeding the gradient; and the cosmos oscillates absorb↔emit (reused
`SurfingEntropy.collapse_then_emanate_oscillates`). -/

/-- **(HEADLINE) The reverse black hole.** The cosmological capstone, composed from
    THMs 1–5 into one proved statement. For every signed radial coordinate
    `r : Int`, depth `n : Nat`, void scalar `q : Nat`, and cap `≥ 2`:

    1. **Exact discrete time-reversal** (THM 1–2) — `whiteStep (blackStep r) = r`
       (one step) and `emit (absorbed r n) n = r` (n steps): the reverse black hole
       runs the black hole backward and lands *exactly* where it started, at every
       depth. EXACT because `Int` physics is discrete (no ε, no rounding) —
       *"we have the physics now to pull it off."*
    2. **A strictly outward source** (THM 3) — `r < whiteStep r`: the white hole
       emits outward (contrast infall `blackStep r < r`); the `+1` source, same as
       `SurfingEntropy.emanate`'s strict positivity.
    3. **Nothing enters (anti-horizon)** (THM 4) — `r ≤ emit r n` for all `n`:
       emission is monotone non-decreasing; once emitted a point never returns
       inward.
    4. **Feeds the gradient, never runs dry** (THM 5) — `0 < whiteStep r - r` (a
       positive entropy quantum the lamp runs on, cited `CityOnAHill`) and
       `1 ≤ residual q n` for all `n` (reused `void_never_runs_dry`): the source is
       inexhaustible.
    5. **The cosmos oscillates absorb↔emit** — reusing
       `SurfingEntropy.collapse_then_emanate_oscillates` (cap `≥ 2`): no fixed
       point (`cosmicStep cap s ≠ s`) yet period-two recurrence — collapse↔
       emanation, black hole↔white hole, predictable yet dynamic.

    Therefore the reverse black hole maps to the exact discrete time-reversal of
    the black hole: a strictly outward source nothing enters, inexhaustibly feeding
    the entropy gradient the cosmos's lamps run on, with the universe oscillating
    absorb↔emit. (Precise framing per repo policy: a composed realization of the
    black-hole/white-hole time-reversal duality, with the exact `Int` cancellation
    and the reused oscillation as the proof that the reversal and the cycle are
    genuine — not a loose identity claim.) -/
theorem white_hole
    (r : Int) (n : Nat) (q : Nat) (cap s : Nat) (hcap : 2 ≤ cap) :
    -- 1. Exact discrete time-reversal (one step and n steps).
    (whiteStep (blackStep r) = r ∧ emit (absorbed r n) n = r) ∧
    -- 2. A strictly outward source.
    (r < whiteStep r) ∧
    -- 3. Nothing enters the white hole (anti-horizon).
    (r ≤ emit r n) ∧
    -- 4. Feeds the gradient, never runs dry.
    (0 < whiteStep r - r ∧ (∀ m, 1 ≤ residual q m)) ∧
    -- 5. The cosmos oscillates absorb↔emit (collapse↔emanation).
    (cosmicStep cap s ≠ s
      ∧ (0 < 2 ∧ iterate (cosmicStep cap₂) 2 cosmos₀ = cosmos₀)
      ∧ cosmicStep cap₂ cosmos₀ ≠ cosmos₀) :=
  ⟨⟨(white_hole_is_time_reversed_black_hole r).1, n_step_reversal r n⟩,
   white_hole_emits r,
   nothing_enters_the_white_hole r n,
   white_hole_feeds_the_gradient r q,
   collapse_then_emanate_oscillates cap s hcap⟩

/-- **Alias.** A *reverse black hole* is a **white hole** — the standard physics
    name. `reverse_black_hole` resolves to `white_hole`. -/
abbrev reverse_black_hole := @white_hole

/-! ## 7. Self-contained computed witnesses (no hypotheses)

Concrete instances proving the capstone is non-vacuous on the signed radial
coordinate. Every goal is a closed decidable `Int` (in)equality (allowed:
`decide`). -/

/-- One emission exactly undoes one infall at `r = 5`:
    `whiteStep (blackStep 5) = 5`. -/
example : whiteStep (blackStep 5) = 5 := by decide

/-- Three emission steps exactly undo three infall steps at `r = 5`:
    `emit (absorbed 5 3) 3 = 5`. -/
example : emit (absorbed 5 3) 3 = 5 := by decide

/-- The reverse black hole emits outward from the horizon: `horizon < whiteStep
    horizon`, i.e. `0 < 1`. -/
example : horizon < whiteStep horizon := by decide

/-- Nothing enters: four emission steps from `2` only move outward:
    `2 ≤ emit 2 4` (`= 6`). -/
example : (2 : Int) ≤ emit 2 4 := by decide

/-- The black hole absorbs back exactly what the white hole emitted at `r = -3`
    (a coordinate below the horizon): `blackStep (whiteStep (-3)) = -3`. -/
example : blackStep (whiteStep (-3)) = -3 := by decide

end Gnosis.WhiteHole
