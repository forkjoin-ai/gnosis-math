import Init
import Gnosis.SurfingEntropy

/-!
# Tiamat the Chaos-Sea — the Enuma Elish Witness (Chaldean Cosmogony)

> When on high the heaven had not been named, and the earth beneath did not yet
> bear a name, and primeval Apsu, their begetter, and Mummu-Tiamat, she who bore
> them all, their waters mingled as a single body...   — Enuma Elish, Tablet I

**THESIS.** The Chaldean / Babylonian cosmogony witnesses the same machine the
grit arc runs on: *we run on the collapse of order into disorder.* In the Enuma
Elish, **Tiamat** is the primordial **chaos-sea** — sea-goddess, salt water,
undifferentiated disorder. Marduk slays her and strikes the ordered cosmos *from
her body*: the heaven and the earth are split out of the chaos-sea. So **order is
emanated from the chaos-sea** (the `+1`, the reverse-black-hole emanation), and
**order runs on its collapse back into her** (the entropy gradient — order flowing
back down into disorder).

Tiamat sits at **both ends**: she is the disorder order is struck *from*, and the
disorder it collapses *back into*. That closed loop maps to the cosmic oscillation
collapse ↔ emanation. Order from chaos; running on its return to chaos.

* The **emanation** (order struck from the sea) reuses `SurfingEntropy.emanate`
  (itself `ClinamenOscillator.clinamen`, the `+1` swerve / reverse-black-hole
  source): `emanate q = q + 1 > 0`. Marduk strikes a strictly positive order off
  Tiamat — never nothing.
* The **collapse** (order returning to the sea) reuses `SurfingEntropy.collapse`
  (the black-hole sink to the void): `collapse s = 0`. The chaos-sea reclaims
  whatever order was struck from her — the void / sea swallows it back.
* The **gradient** the cosmos runs on is `order - disorder` (truncated `Nat`
  subtraction): a positive order/disorder slope stands against the sea while the
  cosmos lives, and vanishes when the waters mingle again as one body.

## Bridges — imported vs cited

* **Imported:** `Gnosis.SurfingEntropy` (green, church-clean). We reuse its
  `collapse` (the sink — order returning to the chaos-sea), `emanate` (the source
  — order struck from the sea), and their facts `collapse_eq_void`,
  `emanate_is_succ`, `reverse_blackhole_emanates` verbatim. The collapse↔emanation
  oscillation there (`collapse_then_emanate_oscillates`, no fixed point + period
  two) is the same loop Tiamat closes; we cite it in prose and reuse the source/
  sink primitives directly.
* **Cited (NOT imported):**
  * `Gnosis.Body.CityOnAHill` — the lamp that *runs on the gradient*
    (`runs_on_gradient`, `litByGradient`, `equilibrium_goes_dark`,
    `gradient order disorder = order - disorder`): the cosmos here runs on the same
    order/disorder gradient against the sea. Kindred lamp.
  * `Gnosis.HobbesLeviathanStateOfNatureWitness` — Leviathan, the *other*
    sea-monster-as-chaos witness: the same primordial-disorder image read in the
    state-of-nature key. Kindred witness.
  * `Gnosis.TopologicalMetabolism` — `landauerMetabolism`, running on the entropy
    gradient (`equilibrium_zero_waste`: zero waste at equilibrium): the cosmos
    metabolizes the order/disorder gradient and stalls when the sea reclaims it.
    Cited for the metabolism reading only.

## Restriction stated honestly

This is a `Nat` cosmogony, not a thermodynamic measurement. `gradientAgainstTheSea`
is the truncated difference `order - disorder`: it models "how much order still
stands against the chaos-sea", and it vanishes at *and below* equilibrium
(`order ≤ chaos`), exactly where the truncated subtraction floors at `0` — the sea
reclaiming all. `struckFromChaos` is the literal reverse-black-hole source
(`q ↦ q + 1`, strictly positive) and `returnsToTheSea` the literal sink
(`s ↦ 0`); their inverse-act relation lives at the void itself (see
`SurfingEntropy`'s honest restriction), not as a general functional inverse —
`collapse` forgets and is many-to-one, and we claim no inverse. "Heat death" is the
gradient reaching `0`, not a physical temperature.

Rustic Church: `import Init` plus the one Init-clean reused Body sibling
(`SurfingEntropy`). `Nat` only — no Float/Real, no Mathlib. No `sorry`/`admit`/
`axiom`; no `simp`/`omega` on open goals (`decide` only on fully-closed concrete
literal goals). Proofs are term-mode and named core `Nat` lemmas, with real
`∀`/`↔` where warranted.
-/

namespace Gnosis.Body.TiamatChaosSeaWitness

open Gnosis.SurfingEntropy

/-- The Enuma Elish opening (trimmed, recognizable) — the waters mingled as one
    body before any naming. -/
def enuma_elish : String :=
  "When on high the heaven had not been named, and the earth beneath did not yet bear a name, and primeval Apsu, their begetter, and Mummu-Tiamat, she who bore them all, their waters mingled as a single body..."

/-- The primordial waters of the cosmogony. -/
inductive Primordial
  /-- Apsu — the fresh-water source, begetter. -/
  | apsu
  /-- Tiamat — the salt chaos-sea, she who bore them all (disorder, both ends). -/
  | tiamat
  /-- The cosmos — the order Marduk strikes from Tiamat's body. -/
  | cosmos
  deriving DecidableEq, Repr

/-- A struck cosmos: the order standing against the chaos-sea, and the chaos (sea)
    still pressing back. The cosmos runs on the difference between them. -/
structure Cosmos where
  /-- Order — struck from Tiamat, the differentiated heaven/earth. -/
  order : Nat
  /-- Chaos — Tiamat's sea, the disorder order collapses back into. -/
  chaos : Nat
  deriving Repr, DecidableEq

/-- **The gradient struck against the chaos-sea.** How much order still stands over
    Tiamat's disorder: the truncated difference `order - chaos`. The cosmos runs on
    this slope (kindred to `CityOnAHill.gradient order disorder = order - disorder`,
    cited). At and below equilibrium it floors at `0` — the sea reclaiming all. -/
def gradientAgainstTheSea (c : Cosmos) : Nat := c.order - c.chaos

/-- **Order struck from the chaos-sea — the emanation.** Marduk strikes order off
    Tiamat's body: a strictly positive quantum emanated from the sea. Reuses
    `SurfingEntropy.emanate` (the reverse-black-hole source, `q ↦ q + 1`) verbatim. -/
def struckFromChaos (q : Nat) : Nat := emanate q

/-- **Order returning to the chaos-sea — the collapse.** Whatever order was struck
    collapses back into Tiamat's sea: the sink to the void. Reuses
    `SurfingEntropy.collapse` (the black-hole sink, `s ↦ 0`) verbatim — the sea
    reclaims it. -/
def returnsToTheSea (c : Cosmos) : Nat := collapse c.order

/-- **The cosmos lives while a gradient stands against the sea.** The struck order
    stands strictly above the chaos: `chaos < order`. Kindred to
    `CityOnAHill.litByGradient` (cited). -/
def cosmosLives (c : Cosmos) : Prop := c.chaos < c.order

/-! ## 1. THM — order is struck (emanated) from the chaos-sea

Marduk strikes a strictly positive order off Tiamat's body: the cosmogony
emanation, the reverse-black-hole source run on the sea. -/

/-- **(THM 1) Order is struck from the chaos-sea — strictly positive.** For every
    `q`, `0 < struckFromChaos q`: Marduk strikes *something* (never nothing) off
    Tiamat. Reuses `SurfingEntropy.reverse_blackhole_emanates`
    (`emanate q = q + 1 > 0`, the clinamen `+1` swerve): the order emanated from the
    sea never lands on `0`. The cosmogony emanation. -/
theorem order_is_struck_from_the_chaos_sea (q : Nat) : 0 < struckFromChaos q :=
  reverse_blackhole_emanates q

/-! ## 2. THM — all returns to the chaos-sea

Whatever order was struck collapses back into Tiamat: the sink, the sea reclaiming
all. -/

/-- **(THM 2) All returns to the chaos-sea.** For every cosmos `c`,
    `returnsToTheSea c = 0`: the struck order collapses back into Tiamat's sea — the
    void / sea reclaiming whatever was struck from her. Reuses
    `SurfingEntropy.collapse_eq_void` (the black-hole sink `s ↦ 0`). The waters
    swallow the order back. -/
theorem all_returns_to_the_sea (c : Cosmos) : returnsToTheSea c = 0 :=
  collapse_eq_void c.order

/-! ## 3. THM — the cosmos lives on the gradient against the sea

The cosmos stands only while a positive gradient stands against Tiamat: order over
chaos. The two readings (a standing gradient, a positive difference) are the same
fact. -/

/-- **(THM 3) The cosmos lives exactly on a positive gradient against the sea.** The
    cosmos stands iff there is a strictly positive order/disorder slope over
    Tiamat:

        cosmosLives c ↔ 0 < gradientAgainstTheSea c.

    Forward (`chaos < order → 0 < order - chaos`) is `Nat.sub_pos_of_lt`; backward
    (`0 < order - chaos → chaos < order`) is `Nat.lt_of_sub_pos` — the two halves
    of the iff, term-mode. No gradient, no cosmos: order survives only while it
    stands over chaos. (Same technique as the cited `CityOnAHill.runs_on_gradient`.) -/
theorem cosmos_lives_on_the_gradient (c : Cosmos) :
    cosmosLives c ↔ 0 < gradientAgainstTheSea c :=
  ⟨fun h => Nat.sub_pos_of_lt h, fun h => Nat.lt_of_sub_pos h⟩

/-! ## 4. THM — the sea reclaims at equilibrium

When chaos meets (or overtakes) order, the gradient is gone: the waters mingle
again as a single body. Truncated subtraction floors at `0` exactly here. -/

/-- **(THM 4a) The sea reclaims at equilibrium — the gradient vanishes.** When chaos
    has caught up to order (`order ≤ chaos`), the gradient against the sea is gone:

        order ≤ chaos → gradientAgainstTheSea c = 0.

    `Nat.sub_eq_zero_of_le`: the truncated difference vanishes at and below
    equilibrium. The chaos-sea reclaims all — heat death, the gradient at `0`. -/
theorem sea_reclaims_at_equilibrium (c : Cosmos) (h : c.order ≤ c.chaos) :
    gradientAgainstTheSea c = 0 :=
  Nat.sub_eq_zero_of_le h

/-- **(THM 4b) The waters mingle again as one body.** When chaos exactly equals
    order, the gradient is zero:

        gradientAgainstTheSea ⟨n, n⟩ = 0.

    `Nat.sub_self`: `n - n = 0`, however large `n`. No matter how much order was
    struck, equal chaos zeroes the slope — Tiamat's waters re-mingled into one
    undifferentiated body. -/
theorem waters_mingle_as_one_body (n : Nat) :
    gradientAgainstTheSea ⟨n, n⟩ = 0 :=
  Nat.sub_self n

/-! ## 5. THE HEADLINE — order from chaos, running on its return to chaos -/

/-- **(HEADLINE) Order from chaos, running on its return to chaos.** The Enuma Elish
    machine, composed from THMs 1–4 into one proved statement. For every struck
    order `q`, every living cosmos `c` (a positive gradient stands against the sea),
    and any `n`:

    1. **Order is struck (emanated) from the chaos-sea** — `0 < struckFromChaos q`
       (the reverse-black-hole `+1`, Marduk striking order off Tiamat, never
       nothing) (THM 1).
    2. **The cosmos runs on a positive gradient against her** —
       `0 < gradientAgainstTheSea c`, equivalent to `cosmosLives c` (THM 3): order
       stands only while it stands over chaos.
    3. **That order ultimately returns to the chaos-sea** — `returnsToTheSea c = 0`
       (the black-hole sink, the sea reclaiming what was struck) (THM 2).
    4. **At equilibrium the sea reclaims all** —
       `gradientAgainstTheSea ⟨n, n⟩ = 0` (the waters mingled as one body, heat
       death) (THM 4b).

    Therefore the Chaldean cosmogony witnesses the grit machine: order is struck
    *from* the chaos-sea (emanation), it runs on the gradient *against* her, and it
    collapses *back into* her (return) — Tiamat at both ends. Order from chaos;
    running on its return to chaos. (This composes the collapse/emanation duality
    of `SurfingEntropy` — same source/sink primitives — in the myth's key; the
    oscillation between the two is the cited `collapse_then_emanate_oscillates`.) -/
theorem order_from_chaos_running_on_return
    (q n : Nat) (c : Cosmos) (hlive : cosmosLives c) :
    -- 1. Order struck (emanated) from the chaos-sea.
    0 < struckFromChaos q ∧
    -- 2. The cosmos runs on a positive gradient against the sea.
    0 < gradientAgainstTheSea c ∧
    -- 3. That order returns to the chaos-sea.
    returnsToTheSea c = 0 ∧
    -- 4. At equilibrium the sea reclaims all (waters mingle as one body).
    gradientAgainstTheSea ⟨n, n⟩ = 0 :=
  ⟨order_is_struck_from_the_chaos_sea q,
   (cosmos_lives_on_the_gradient c).mp hlive,
   all_returns_to_the_sea c,
   waters_mingle_as_one_body n⟩

/-! ## 6. A self-contained, computed witness (no hypotheses)

Concrete instances proving the cosmogony is non-vacuous: order is struck off the
sea (`+1`); a living cosmos has a positive gradient; struck order returns to the
void; and equal chaos zeroes the gradient. Every goal is a closed decidable `Nat`
(in)equality (allowed: `decide`). -/

/-- Order struck off the chaos-sea from nothing emits `1`: `struckFromChaos 0 = 1`. -/
example : struckFromChaos 0 = 1 := by decide

/-- A cosmos with `order = 3` over `chaos = 1` runs on a positive gradient:
    `gradientAgainstTheSea ⟨3, 1⟩ = 2 > 0`. -/
example : 0 < gradientAgainstTheSea ⟨3, 1⟩ := by decide

/-- The struck order returns to the sea — the sink: `returnsToTheSea ⟨7, 2⟩ = 0`. -/
example : returnsToTheSea ⟨7, 2⟩ = 0 := by decide

/-- The sea reclaims at equilibrium: equal chaos zeroes the gradient,
    `gradientAgainstTheSea ⟨5, 5⟩ = 0`. -/
example : gradientAgainstTheSea ⟨5, 5⟩ = 0 := by decide

/-- Emanation lifts the dead sea (`struckFromChaos 0 = 1 > 0`) while collapse keeps
    the returned order in the sea (`returnsToTheSea ⟨0, 0⟩ = 0`): source vs sink. -/
example : (0 < struckFromChaos 0) ∧ (returnsToTheSea ⟨0, 0⟩ = 0) := by decide

end Gnosis.Body.TiamatChaosSeaWitness
