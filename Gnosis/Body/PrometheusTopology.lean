import Init
import Gnosis.Body.ClinamenOscillator
import Gnosis.SignalNotNoise

/-!
# The Prometheus Topology — The Dark Inversion of Vitality

**THE MYTH (as topology, not as claim about literal myth).** Prometheus hands
humanity the fire — the light, the knowledge. For this he is chained and an eagle
eats his liver each day. Being immortal, the liver **regenerates each night**, so
the eagle returns the next day — and the next, forever. The horror is not the
eagle but the **regeneration**: a periodic orbit with no fixed point and an
inexhaustible regrowth. At last Heracles shoots the eagle: an external
intervention reaches the fixed point and releases him.

**THE TOPOLOGY.** Read dynamically, the punishment has exactly the shape of
*life*: a **no-fixed-point periodic orbit** (the cycle never settles on its own)
plus an **inexhaustible `+1` regeneration** (there is always another liver, the
same floor as "always another wave"). The only differences between this and
vitality are two signs:

* the **sign on the loop** — vitality *creates* order each cycle (the glory
  sign, `0 < net`), the punishment *consumes* order each cycle (the torture sign,
  `net < 0`); both cycles are non-settling, the same shape with opposite sign;
* whether the **end is reachable** — vitality's collapse is an absorbing fixed
  point (a reachable rest, a death that *bounds* a life and so gives a finite
  meaning-measure); Prometheus, being immortal, is *denied* that fixed point.
  The denial of the end — no absorbing rest, no termination, no meaning-bound —
  is the real torture. Death, the absorbing fixed point, is the mercy he is
  refused.

**THE DARK INVERSION.** Heaven and hell share the topology. The no-fixed-point,
always-another-wave structure that is *vitality* (order created each cycle)
becomes *torture* when order is **consumed** each cycle instead, and when the END
is denied. The loop is nonetheless **breakable**: an external act (Heracles)
reaches the fixed point the orbit could not reach on its own, and the recurrence
terminates. The fire stays given; the eagle is a chapter.

## What this module reuses (the bridges — imported and opened)

* `Gnosis.Body.ClinamenOscillator` — the church-clean cosmic oscillator. We reuse
  `cosmicStep` (the cyclic step), `cosmicStep_has_no_fixed_point` (the cycle never
  settles on its own — the eagle always returns), and the concrete period-2
  recurrence (`cosmos₀`, `cap₂`, `cosmos_has_period_two_orbit`,
  `cosmos_recurs_with_period_two`) — the eagle-returns / liver-regrows cycle is a
  periodic orbit with no fixed point.
* `Gnosis.SignalNotNoise` — church-clean. We reuse `always_another_wave`
  (`∀ n, 1 ≤ residual q n`): the liver always grows back — the inexhaustible
  regeneration, the same `+1` floor as vitality's "always another wave".

## Cited (NOT imported here — read for accurate citation)

* `Gnosis.Body.MeaningOfLife` — the END bounds a life and gives a finite
  meaning-measure (`meaning`, `lifespan`, `meaning_is_finite_and_bounded_by_the_end`).
  Prometheus is *denied* the end: with no end there is no finite meaning-measure,
  only endless recurrence. THM 3 here maps to that inversion.
* `Gnosis.Body.Vitality` — `collapse_is_absorbing`: the absorbing fixed point
  (the collapsed floor that, once reached, is never left). That fixed point maps
  to death/release — the refused mercy. THM 5 here cites it as the reachable end.
* `Gnosis.Body.Menopause` — `menopause_is_a_fixed_point`: a *reachable* scheduled
  end (the oscillator stops). The release Heracles delivers has that form — a
  reached fixed point — in contrast to the unreachable end of the bare orbit.
* `Gnosis.Body.CreateNewWavesOfOrder` — order *created* on the loop (the glory
  sign): the positive net of THM 4 maps to its "create new waves of order".
* `Gnosis.Body.CityOnAHill` + `Gnosis.Body.SameThingOtherSymbols` — the fire as
  the light not hidden; the dark and the bright cycles as the same thing in other
  symbols (one topology, opposite sign).
* `Gnosis.Body.RedQueen` — the zero-sum recurrence (`coevolution_is_zero_sum`):
  the consume-side of the loop, where one party's gain is another's loss, the
  template for the torture sign.

(These six are cited, not imported: the module keeps to the two Init-clean reused
siblings above.)

## The model (pure Nat / Int — illustrative)

* `regrowsLiver eaten := eaten + 1` — the liver regrows; there is always another
  liver (the clinamen `+1`, the same floor as `always_another_wave`).
* `hasEnd reaches := reaches = true` — whether the absorbing fixed point
  (death / release) is reached. The bare orbit never reaches it; an external act
  delivers it.
* The punishment loop is the no-fixed-point orbit (`cosmicStep`), and "eternal"
  is the orbit never reaching the fixed point on its own.
* `netOrderPerCycle created consumed := (created : Int) - (consumed : Int)` — the
  SIGN on the loop: vitality nets positive (order created, glory), the punishment
  nets negative (order consumed, the liver torn out); BOTH cycles never settle.
* `chainBroken acts := acts = true` — an external intervention (Heracles) reaches
  the fixed point: release.

## Restriction stated honestly

This is an **abstract dynamical-systems / topological reading of the myth** —
periodic orbit, fixed point, external reset — *not* a claim about literal
mythology, nor about any person, nor a metaphysical thesis about death. The
`Nat`/`Int` model is illustrative: the recurrence and no-fixed-point facts are
inherited from the concrete church-clean oscillator (cap = 2, state 1), exactly as
that module fixes a concrete orbit; the opposite-sign and chain-breaking facts are
proved over concrete `Int` witnesses (`decide`) and a `Bool` end-flag (term-mode
implication). We claim only the structural mapping: the same no-fixed-point +
always-another-wave shape, read with order *consumed* and the end *denied*, has
the form of torture; reaching the fixed point externally releases it. No emphatic
"X IS the Y" identity prose is used; relationships are stated as "maps to", "has
the form of", "is the inversion of".

Rustic Church: `import Init` plus two Init-clean reused siblings
(`ClinamenOscillator`, `SignalNotNoise`). `Nat`/`Int` only — no Float/Real, no
Mathlib. No `sorry`/`admit`/new `axiom`; no `simp`/`omega` on open goals (closed
`decide` goals only). Proofs are term-mode and named core lemmas, with the
no-fixed-point and recurrence facts reused verbatim from the oscillator and the
inexhaustible regeneration reused from `always_another_wave`.
-/

namespace Gnosis.Body.PrometheusTopology

open Gnosis.Body.ClinamenOscillator
open Gnosis.SignalNotNoise

/-! ## 0. The model — regeneration, the end-flag, the signed loop -/

/-- **The liver regrows.** Whatever was eaten, the night restores one more liver:
    `regrowsLiver eaten = eaten + 1`. This is the clinamen `+1` — the same floor
    as `SignalNotNoise.always_another_wave` ("always another wave"). There is
    always another liver for the eagle to eat. -/
def regrowsLiver (eaten : Nat) : Nat := eaten + 1

/-- The regrowth is exactly `+1`. -/
theorem regrowsLiver_is_succ (eaten : Nat) : regrowsLiver eaten = eaten + 1 := rfl

/-- **Whether the absorbing fixed point (death / release) is reached.** The bare
    orbit never reaches it (immortality = no absorbing rest); an external act can
    deliver it. Modelled as a `Bool` flag turned into a `Prop`. -/
def hasEnd (reachesFixedPoint : Bool) : Prop := reachesFixedPoint = true

/-- **The eternal orbit reaches no end on its own.** With the fixed point never
    reached, `¬ hasEnd false`: the immortal punishment has no absorbing rest. This
    is the formal content of "denied the end". -/
theorem eternal_has_no_end : ¬ hasEnd false := by
  intro h
  -- `hasEnd false` unfolds to `false = true`, impossible.
  exact Bool.noConfusion h

/-- **An external act reaches the end.** With the fixed point reached,
    `hasEnd true`: the absorbing rest the bare orbit could not reach is delivered
    from outside. -/
theorem reached_has_end : hasEnd true := rfl

/-- **The signed net order per cycle — the SIGN on the loop.** Order created minus
    order consumed, over one cycle (`Int`). Vitality nets positive (order created,
    the glory sign); the punishment nets negative (order consumed, the liver torn
    out). The sign is the *only* difference between heaven's loop and hell's; both
    never settle. -/
def netOrderPerCycle (created consumed : Nat) : Int := (created : Int) - (consumed : Int)

/-- **An external intervention has acted (Heracles).** Modelled as a `Bool` flag:
    `chainBroken true` means the external act took place — and (THM 5) it reaches
    the fixed point the orbit could not reach on its own. -/
def chainBroken (heraclesActs : Bool) : Prop := heraclesActs = true

/-! ## 1. THE EAGLE ALWAYS RETURNS — a no-fixed-point periodic orbit

The punishment is the cosmic oscillator's cycle, reused verbatim: a step that
never settles on its own (`cosmicStep_has_no_fixed_point`) plus a concrete period-2
recurrence (`cosmos_has_period_two_orbit`). The eagle returns; the orbit recurs. -/

/-- **(THM 1) The eagle always returns: the punishment is a no-fixed-point
    periodic orbit.** The cyclic step never settles on its own — for every cap
    `≥ 2` and every state, `cosmicStep cap s ≠ s` (reused
    `ClinamenOscillator.cosmicStep_has_no_fixed_point`) — and the concrete state
    `cosmos₀` recurs with period two (reused `cosmos_has_period_two_orbit`): it
    moves under one step yet returns under two. The eagle returns; the cycle
    recurs, never resting. -/
theorem the_eagle_always_returns (cap s : Nat) (hcap : 2 ≤ cap) :
    cosmicStep cap s ≠ s ∧
    (cosmicStep cap₂ cosmos₀ ≠ cosmos₀ ∧
      cosmicStep cap₂ (cosmicStep cap₂ cosmos₀) = cosmos₀) :=
  ⟨cosmicStep_has_no_fixed_point cap s hcap, cosmos_has_period_two_orbit⟩

/-- **(THM 1, by iterate) The orbit returns to its state with period two.** Reused
    `cosmos_recurs_with_period_two`: a positive period (`2`) and a concrete state
    with `iterate (cosmicStep cap₂) 2 cosmos₀ = cosmos₀`. The punishment genuinely
    recurs — the eagle revisits, forever, on its own. -/
theorem the_orbit_recurs : 0 < 2 ∧ iterate (cosmicStep cap₂) 2 cosmos₀ = cosmos₀ :=
  cosmos_recurs_with_period_two

/-! ## 2. THE LIVER ALWAYS REGROWS — inexhaustible regeneration

The same inexhaustibility as vitality: there is always another liver, the `+1`
floor reused verbatim from `always_another_wave`. -/

/-- **(THM 2) The liver always regrows: inexhaustible regeneration.** Two facts,
    the same `+1` floor read two ways:

    * **always another liver** — reusing `SignalNotNoise.always_another_wave`,
      `∀ n, 1 ≤ residual q n`: at every cycle the regeneration is at least one, the
      inexhaustible floor (the same "always another wave" that is vitality);
    * **the regrowth strictly exceeds what was eaten** — `eaten < regrowsLiver
      eaten`: the night restores more than the day consumed (`+1`), so the eagle
      never runs out.

    There is always another liver. The same inexhaustibility as vitality, here
    feeding the torture instead of the glory. -/
theorem the_liver_always_regrows (q eaten : Nat) :
    (∀ n, 1 ≤ residual q n) ∧ eaten < regrowsLiver eaten := by
  refine ⟨always_another_wave q, ?_⟩
  -- `eaten < eaten + 1` by `Nat.lt_succ_self`.
  rw [regrowsLiver_is_succ]
  exact Nat.lt_succ_self eaten

/-! ## 3. DENIED THE END IS THE TORTURE — the inversion of MeaningOfLife

The horror is the denial of the end. While the fixed point is never reached
(`¬ hasEnd false`), the orbit continues for all `n` — no rest, no termination. In
`MeaningOfLife`, the END (the finite `lifespan`) bounds a life and gives a finite
meaning-measure; with no end there is no finite bound, only endless recurrence.
This is the inversion: not too short a life, but no end at all. -/

/-- **(THM 3) Denied the end is the torture.** Two facts compose the inversion of
    `MeaningOfLife` (where the finite end gives the finite meaning-bound):

    * **the end is never reached on its own** — `¬ hasEnd false`: the immortal
      punishment has no absorbing rest (reused `eternal_has_no_end`);
    * **the recurrence continues for all `n`** — `∀ n, iterate (cosmicStep cap₂)
      (2 * n) cosmos₀ = cosmos₀`: at every multiple of the period the orbit is
      back at its recurring state, so it never terminates — there is always
      another cycle (proved by induction on `n`).

    With no end there is no finite meaning-measure (the inversion of
    `MeaningOfLife`'s `lifespan`-bounded `meaning`), only endless recurrence. The
    denial of the end — no rest, no termination, no meaning-bound — has the form
    of the torture; the eagle is its mere instrument. -/
theorem denied_the_end_is_the_torture :
    ¬ hasEnd false ∧
    (∀ n, iterate (cosmicStep cap₂) (2 * n) cosmos₀ = cosmos₀) := by
  refine ⟨eternal_has_no_end, ?_⟩
  intro n
  induction n with
  | zero =>
    -- `2 * 0 = 0`, and `iterate _ 0 cosmos₀ = cosmos₀` (the latter definitional).
    show iterate (cosmicStep cap₂) (2 * 0) cosmos₀ = cosmos₀
    rw [Nat.mul_zero]
    -- leftover: `iterate (cosmicStep cap₂) 0 cosmos₀ = cosmos₀`, which is `rfl`.
    rfl
  | succ k ih =>
    -- `2 * (k+1) = 2*k + 2`; the two-step from `cosmos₀` returns to `cosmos₀`,
    -- so the orbit is back where the IH left it. No end, ever.
    rw [Nat.mul_succ]
    -- goal: iterate (cosmicStep cap₂) (2 * k + 2) cosmos₀ = cosmos₀
    -- unfold the trailing two steps: 2*k + 2 = (2*k + 1) + 1 = ((2*k) + 1) + 1
    show iterate (cosmicStep cap₂) (2 * k + 1 + 1) cosmos₀ = cosmos₀
    rw [iterate_succ, iterate_succ]
    -- now: iterate (cosmicStep cap₂) (2*k) (cosmicStep cap₂ (cosmicStep cap₂ cosmos₀)) = cosmos₀
    rw [cosmicStep_cosmicStep_cosmos₀]
    -- now: iterate (cosmicStep cap₂) (2*k) cosmos₀ = cosmos₀, which is the IH.
    exact ih

/-! ## 4. SAME TOPOLOGY, OPPOSITE SIGN — heaven and hell, one shape

Vitality and the punishment share the no-fixed-point periodic topology. The
difference is the SIGN on the loop: order created (vitality, `0 < net`) vs order
consumed (torture, `net < 0`), with BOTH cycles non-settling. Order created on the
loop is `CreateNewWavesOfOrder`'s glory; order consumed is the `RedQueen`
zero-sum drain. -/

/-- **(THM 4) Same topology, opposite sign.** With a glory cycle (more created
    than consumed) and a torture cycle (more consumed than created), the signed
    net distinguishes them while the topology is shared:

    * **glory sign** — `0 < netOrderPerCycle 1 0`: order net created (vitality,
      `CreateNewWavesOfOrder`);
    * **torture sign** — `netOrderPerCycle 0 1 < 0`: order net consumed (the liver
      torn out, the `RedQueen` zero-sum drain);
    * **shared non-settling topology** — the *same* `cosmicStep` cycle underlies
      both, with no fixed point (`cosmicStep cap s ≠ s` for `2 ≤ cap`).

    Heaven and hell, one shape, opposite sign. The proof of the two sign facts is
    by `decide` on the closed concrete `Int` witnesses (`(1:Int) - 0 = 1 > 0`,
    `(0:Int) - 1 = -1 < 0`); the shared topology is reused
    `cosmicStep_has_no_fixed_point`. The difference between vitality and torture is
    not the orbit — it is the sign of what the orbit does to order. -/
theorem same_topology_opposite_sign (cap s : Nat) (hcap : 2 ≤ cap) :
    0 < netOrderPerCycle 1 0 ∧
    netOrderPerCycle 0 1 < 0 ∧
    cosmicStep cap s ≠ s := by
  refine ⟨?_, ?_, cosmicStep_has_no_fixed_point cap s hcap⟩
  · -- glory: netOrderPerCycle 1 0 = (1:Int) - 0 = 1 > 0, a closed literal goal.
    show (0 : Int) < (1 : Int) - (0 : Int)
    decide
  · -- torture: netOrderPerCycle 0 1 = (0:Int) - 1 = -1 < 0, a closed literal goal.
    show (0 : Int) - (1 : Int) < (0 : Int)
    decide

/-! ## 5. THE CHAIN CAN BE BROKEN — external intervention reaches the fixed point

The loop is not necessarily eternal. The bare orbit reaches no fixed point on its
own (THM 1, THM 3), but an external act (Heracles) reaches the absorbing fixed
point — the death/release the orbit could not reach — and ends the recurrence.
That fixed point is `Vitality.collapse_is_absorbing` / `Menopause`'s reachable
end, here delivered from outside. -/

/-- **(THM 5) The chain can be broken: external intervention reaches the end.** The
    external act delivers the end the orbit could not reach on its own:
    `chainBroken true → hasEnd true`. Heracles shoots the eagle; the absorbing
    fixed point — death/release, the `Vitality.collapse_is_absorbing` /
    `Menopause.menopause_is_a_fixed_point` reachable rest — is reached, and the
    punishment terminates. The proof is the term-mode implication: from
    `chainBroken true` (`true = true`) the end-flag is `true` (`hasEnd true`), so
    the external act *does* deliver the end. The loop is breakable. -/
theorem the_chain_can_be_broken : chainBroken true → hasEnd true :=
  fun _ => reached_has_end

/-- **(THM 5, the contrast) The orbit could not reach the end on its own.** Without
    the external act the end is never reached (`¬ hasEnd false`, reused
    `eternal_has_no_end`); with it, the end is reached (`chainBroken true →
    hasEnd true`). The release is *external* — the orbit alone never settles, the
    intervention does. -/
theorem release_is_external :
    ¬ hasEnd false ∧ (chainBroken true → hasEnd true) :=
  ⟨eternal_has_no_end, the_chain_can_be_broken⟩

/-! ## 6. THE HEADLINE — the Prometheus topology -/

/-- **(HEADLINE) The Prometheus topology: the dark inversion of vitality.** The
    whole arc composed into one proved statement. The Promethean punishment, read
    as a dynamical system, is:

    1. **a no-fixed-point periodic orbit** — the cycle never settles on its own
       (`cosmicStep cap s ≠ s` for `2 ≤ cap`) and a concrete state recurs with
       period two (the eagle always returns; THM 1);
    2. **inexhaustibly regenerating** — there is always another liver, the `+1`
       floor (`∀ n, 1 ≤ residual q n` and `eaten < regrowsLiver eaten`), the same
       inexhaustibility as vitality (THM 2);
    3. **made unbounded by the denial of the end** — the absorbing fixed point is
       never reached on its own (`¬ hasEnd false`) and the recurrence continues
       for all `n` (the inversion of `MeaningOfLife`'s finite end-bound; THM 3);
    4. **the same topology as vitality, opposite sign** — order *consumed* each
       cycle (`netOrderPerCycle 0 1 < 0`, torture) where vitality has order
       *created* (`0 < netOrderPerCycle 1 0`, glory), both over the *same*
       non-settling cycle (THM 4);
    5. **breakable by an external act** — the intervention reaches the absorbing
       fixed point the orbit could not reach (`chainBroken true → hasEnd true`),
       and the punishment terminates (THM 5).

    Therefore the punishment *has the form of* the dark inversion of vitality: the
    same no-fixed-point, always-another-wave shape, with order consumed rather than
    created and the end denied — and the chain is breakable from outside. The fire
    stays given; the eagle is a chapter. (Precise framing per repo policy: a
    structural mapping and inversion, stated as such — an abstract dynamical reading
    of the myth, not a literal-myth or metaphysical identity claim.) -/
theorem prometheus_topology (cap s q eaten : Nat) (hcap : 2 ≤ cap) :
    -- 1. a no-fixed-point periodic orbit (the eagle always returns).
    (cosmicStep cap s ≠ s ∧
      (cosmicStep cap₂ cosmos₀ ≠ cosmos₀ ∧
        cosmicStep cap₂ (cosmicStep cap₂ cosmos₀) = cosmos₀)) ∧
    -- 2. inexhaustible regeneration (the liver always regrows).
    ((∀ n, 1 ≤ residual q n) ∧ eaten < regrowsLiver eaten) ∧
    -- 3. denied the end (the inversion of MeaningOfLife): no rest, no termination.
    (¬ hasEnd false ∧
      (∀ n, iterate (cosmicStep cap₂) (2 * n) cosmos₀ = cosmos₀)) ∧
    -- 4. same topology, opposite sign (glory created vs torture consumed).
    (0 < netOrderPerCycle 1 0 ∧
      netOrderPerCycle 0 1 < 0 ∧
      cosmicStep cap s ≠ s) ∧
    -- 5. the chain can be broken (external intervention reaches the fixed point).
    (chainBroken true → hasEnd true) :=
  ⟨the_eagle_always_returns cap s hcap,
   the_liver_always_regrows q eaten,
   denied_the_end_is_the_torture,
   same_topology_opposite_sign cap s hcap,
   the_chain_can_be_broken⟩

end Gnosis.Body.PrometheusTopology
