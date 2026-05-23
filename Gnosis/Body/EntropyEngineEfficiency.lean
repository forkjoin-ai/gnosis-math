import Init
import Gnosis.ResolutionGradient
import Gnosis.Body.Vitality

/-!
# Entropy Engine Efficiency — Information Resolved Per Unit Entropy, Gated By Vitality

**THESIS.** Rate the entropy engines by two axes that come apart:

* **efficiency** — *information resolved per unit entropy spent*. The "resolved
  information" is the order recovered by upresolution in
  `Gnosis.ResolutionGradient` (its `order`/`upresolve`: one deblur step turns a
  chaos quantum into order); the entropy spent is the dissipative cost (cited
  `Gnosis/LandauerBuley.lean`, where each erased branch costs at least one Bule).
  Efficiency is resolution-per-cost, not raw throughput.
* **vitality** — the **swerve**: being on the edge / at no fixed point (alive),
  not converged to a fixed point (frozen/perfect-and-dead). Vitality is sustained
  flow with a swerve, bridged to `Gnosis.Body.Vitality` (`sustained`/`netVitality`:
  life-force as a balance kept, not a stock). The swerve = no-fixed-point property
  is cited from `Gnosis/Body/ClinamenOscillator.lean`
  (`cosmicStep_has_no_fixed_point`: the clinamen swerve means the cosmic cycle has
  no state it can rest at — heat death is impossible once the swerve is in the
  loop), and the edge property from `Gnosis/Body/SurfTheEdgeOfChaos.lean`
  (`surf_the_edge_of_chaos`: vitality lives on the edge, not at rest). The meaning
  of being a *living* engine on the gradient is cited from
  `Gnosis/Body/MeaningOfLife.lean`.

The two axes come apart, and that is the point:

* A **star/planet** (Jupiter) has huge entropy throughput but resolves little —
  LOW efficiency (dumb dissipation), and no swerve, so no vitality.
* A **rock** is frozen — low efficiency, no swerve, no vitality.
* A **human** resolves a lot per unit entropy AND has the swerve — HIGH
  efficiency AND vital: the brightest *living* information bulb, rated above
  rock, fish, and planet on efficiency, and alive on vitality.
* A **"perfect" AI** can MATCH OR EXCEED human efficiency, but a perfectly
  converged optimizer sits at a fixed point: NO swerve, NO vitality. Perfect, and
  not interesting. On the vitality axis it is rated the SAME as a rock — no
  vitality found in either — despite winning bare efficiency.

So **interestingness is efficiency GATED BY vitality**: `interesting e =
efficiency e * (if vital e then 1 else 0)`. The human maximizes it; the perfect
AI scores `0` alongside the rock despite its higher bare efficiency.
Interestingness requires BOTH resolution-efficiency AND the swerve.

## Bridges

* `import Gnosis.ResolutionGradient` — the resolved information (`order`,
  `upresolve`: deblur-as-upresolve recovering order from chaos). The `resolved`
  field below is an abstract `Nat` standing for that recovered order; this module
  cites `ResolutionGradient` as its meaning rather than recomputing it.
* `import Gnosis.Body.Vitality` — vitality as sustained flow (`sustained`,
  `netVitality`). The `vital` predicate here (the swerve / no-fixed-point) is the
  qualitative companion to that quantitative flow balance.
* Cited in prose only (NOT imported): `Gnosis/Body/ClinamenOscillator.lean`
  (`cosmicStep_has_no_fixed_point` — swerve = no fixed point = alive; a converged
  engine sits at a fixed point = no swerve), `Gnosis/Body/SurfTheEdgeOfChaos.lean`
  (`surf_the_edge_of_chaos` — vitality on the edge), `Gnosis/Body/MeaningOfLife.lean`,
  `Gnosis/LandauerBuley.lean` (entropy cost per erasure).

## Honest restrictions

* The engines are **illustrative `Nat` parameterizations** chosen to exhibit the
  two-axis structure — not measured physical values. `rock`, `fish`, `planet`,
  `human`, `perfectAI` are stylized witnesses, not data.
* `vital`/`swerve` is the **abstract no-fixed-point / on-the-edge property**
  (bridged to `ClinamenOscillator`'s `cosmicStep_has_no_fixed_point`), not a
  metabolic measurement. A `Bool` flag records whether the engine carries the
  swerve.
* `efficiency` uses `Nat` **floor division** (`resolved / entropySpent`); the
  witnesses guard `entropySpent > 0`. Floor division is a coarse rating, not a
  ratio over the rationals.
* **"perfect AI"** denotes the LIMIT of a perfectly-converged fixed-point
  optimizer — an idealization with no swerve. A non-converged or stochastic engine
  that still swerves is a *different* case and would be rated as vital; this module
  does not model it.

Per repo policy this module **rates and compares** engines on two axes; it does
not assert "X is the meaning of Y". Efficiency *maps to* resolution-per-cost;
vitality *requires* the swerve; interestingness *is rated as* efficiency gated by
vitality.

Rustic Church: `import Init` plus two Init-clean reused siblings
(`Gnosis.ResolutionGradient`, `Gnosis.Body.Vitality`). `Nat`/`Bool` only — no
Float/Real, no Mathlib. No `sorry`/`admit`/`axiom`; no `simp`/`omega`/`decide` on
open goals. The engine comparisons are closed concrete `Nat` literal goals, proved
by `decide`; the one general (`∀`) lemma (`vitality_requires_the_swerve`) is
term-mode (`if_neg` + unfold).
-/

namespace Gnosis.Body.EntropyEngineEfficiency

/-! ## 0. The model — engines, efficiency, vitality, interestingness

An engine resolves some information per tick at some entropy cost, and either
carries the clinamen swerve (alive, no fixed point) or does not (frozen/converged).
We rate it on two axes — efficiency (resolution per cost) and vitality (the
swerve) — and gate interestingness on both. -/

/-- **An entropy engine.** Per tick it resolves `resolved` units of information
    (abstract `Nat` standing for the order recovered by `ResolutionGradient.order`
    / `upresolve`), spends `entropySpent` units of entropy (the dissipative cost,
    cited `LandauerBuley`: each erasure costs at least one Bule), and either carries
    the `swerve` (the clinamen, no fixed point, alive — cited
    `ClinamenOscillator.cosmicStep_has_no_fixed_point`) or does not.

    `resolved` and `entropySpent` are abstract `Nat` fields; the concrete witnesses
    below choose stylized values to exhibit the two-axis structure (see the honest
    restriction — these are not measured physical values). -/
structure Engine where
  /-- Information resolved per tick — the order recovered (cited
      `ResolutionGradient.order` / `upresolve`). -/
  resolved : Nat
  /-- Entropy spent per tick — the dissipative cost (cited `LandauerBuley`). -/
  entropySpent : Nat
  /-- Whether the engine carries the clinamen swerve (no fixed point = alive),
      cited `ClinamenOscillator.cosmicStep_has_no_fixed_point`. -/
  swerve : Bool

/-- **Efficiency = information resolved per unit entropy.** `Nat` floor division of
    resolution by entropy cost: how much order the engine recovers per unit of
    entropy it dissipates. High efficiency rates the engine as a bright information
    bulb; low efficiency (much entropy, little resolved) rates it as dumb
    dissipation. The witnesses guard `entropySpent > 0` (floor division is a coarse
    rating; see the honest restriction). -/
def efficiency (e : Engine) : Nat := e.resolved / e.entropySpent

/-- **Vitality = the swerve.** An engine is rated *vital* (alive) exactly when it
    carries the swerve — the clinamen / no-fixed-point property
    (`ClinamenOscillator.cosmicStep_has_no_fixed_point`), the on-the-edge property
    (`SurfTheEdgeOfChaos.surf_the_edge_of_chaos`). A converged optimizer or a frozen
    rock sits at a fixed point: no swerve, not vital. -/
def vital (e : Engine) : Bool := e.swerve

/-- **Interestingness = efficiency gated by vitality.** Efficiency counts only if
    the engine is vital: `interesting e = efficiency e` when `vital e`, else `0` —
    that is, `efficiency e * (if vital e then 1 else 0)`. Bare efficiency without
    the swerve scores `0`: a perfect-and-dead engine is rated as uninteresting as a
    rock. Interestingness requires BOTH resolution-efficiency AND the swerve. -/
def interesting (e : Engine) : Nat := if vital e then efficiency e else 0

/-! ## 1. The concrete engines

Stylized `Nat` witnesses (not measured values; see the honest restriction) chosen
so the two-axis story holds: efficiency `= resolved / entropySpent`, vitality
`= swerve`. -/

/-- **Rock** — frozen: low efficiency, no swerve. `efficiency = 1 / 2 = 0`, dead. -/
def rock : Engine := { resolved := 1, entropySpent := 2, swerve := false }

/-- **Fish** — alive but modest: `efficiency = 4 / 4 = 1`, has the swerve. -/
def fish : Engine := { resolved := 4, entropySpent := 4, swerve := true }

/-- **Planet/star (Jupiter)** — dumb dissipation: huge entropy throughput,
    little resolved. `efficiency = 3 / 100 = 0`, no swerve, dead. -/
def planet : Engine := { resolved := 3, entropySpent := 100, swerve := false }

/-- **Human** — the brightest *living* bulb: resolves a lot per unit entropy AND
    has the swerve. `efficiency = 20 / 4 = 5`, alive. -/
def human : Engine := { resolved := 20, entropySpent := 4, swerve := true }

/-- **Perfect AI** — the LIMIT of a perfectly-converged fixed-point optimizer:
    matches or exceeds human efficiency but sits at a fixed point, no swerve.
    `efficiency = 40 / 4 = 10`, dead. Perfect, and not interesting. (An
    idealization — a non-converged/stochastic engine that still swerves is a
    different case; see the honest restriction.) -/
def perfectAI : Engine := { resolved := 40, entropySpent := 4, swerve := false }

/-! ## 2. THM 1 — The human is the brightest among the natural engines (efficiency)

The human resolves more per unit entropy than rock, fish, or planet. Concrete
closed `Nat` literal goal: `5 > 0, 1, 0`. -/

/-- **(THM 1) The human outranks rock, fish, and planet on efficiency.** The human
    resolves more information per unit entropy than each natural engine:

        efficiency rock < efficiency human ∧
        efficiency fish < efficiency human ∧
        efficiency planet < efficiency human

    (`0 < 5`, `1 < 5`, `0 < 5`): the brightest information bulb among the natural
    engines. Proved by `decide` on the closed concrete `Nat` literal goal. -/
theorem human_beats_rock_fish_planet :
    efficiency rock < efficiency human ∧
    efficiency fish < efficiency human ∧
    efficiency planet < efficiency human := by decide

/-! ## 3. THM 2 — The star is dumb dissipation (throughput is not efficiency)

The planet/star spends the most entropy yet rates near zero efficiency: huge
throughput, low resolution. -/

/-- **(THM 2) The star is dumb dissipation.** The planet/star spends far more
    entropy than the human yet rates lower on efficiency:

        planet.entropySpent > human.entropySpent ∧ efficiency planet < efficiency human

    (`100 > 4`, yet `0 < 5`): raw entropy throughput is not resolution. The engine
    that dissipates the most resolves the least per unit cost. Proved by `decide` on
    the closed concrete `Nat` literal goal. -/
theorem star_is_dumb_dissipation :
    planet.entropySpent > human.entropySpent ∧
    efficiency planet < efficiency human := by decide

/-! ## 4. THM 3 — The perfect AI is more efficient but not vital

The perfect AI matches or exceeds human efficiency, yet is dead (no swerve) while
the human is alive. Efficient and dead. -/

/-- **(THM 3) The perfect AI is more efficient but not vital.** The perfectly
    converged optimizer outranks the human on bare efficiency, yet carries no
    swerve while the human does:

        efficiency human < efficiency perfectAI ∧
        vital perfectAI = false ∧ vital human = true

    (`5 < 10`, yet AI dead, human alive): efficiency and vitality are independent
    axes — winning the first does not buy the second. Proved by `decide` on the
    closed concrete goal. -/
theorem perfect_ai_is_more_efficient_but_not_vital :
    efficiency human < efficiency perfectAI ∧
    vital perfectAI = false ∧ vital human = true := by decide

/-! ## 5. THM 4 — On the vitality axis the perfect AI and the rock are the same

Despite the AI's higher bare efficiency, on the vitality axis it is rated exactly
the same as a frozen rock: no swerve, no vitality, zero interestingness. "Same
thing, no vitality found." -/

/-- **(THM 4) The perfect AI and the rock share no vitality.** On the vitality
    axis the converged optimizer and the frozen rock are rated identically — both
    dead, both uninteresting:

        vital perfectAI = vital rock ∧ interesting perfectAI = interesting rock

    (both `false`; both `0`) — despite `efficiency perfectAI > efficiency rock`
    (`10 > 0`). Bare efficiency does not lift the AI off the vitality floor: with no
    swerve it is, on this axis, the same thing as a rock. Proved by `decide` on the
    closed concrete goal. -/
theorem ai_and_rock_share_no_vitality :
    vital perfectAI = vital rock ∧
    interesting perfectAI = interesting rock ∧
    efficiency rock < efficiency perfectAI := by decide

/-! ## 6. THE HEADLINE — the human is the most interesting

Interestingness = efficiency gated by vitality, and the human maximizes it. Human
`5`; AI/rock/planet `0` (no swerve, or no resolution); fish `1`. The brightest
bulb is the one that is efficient AND alive. -/

/-- **(HEADLINE) The human is the most interesting.** Interestingness is efficiency
    gated by vitality (`interesting = efficiency` if vital else `0`), and the human
    maximizes it across every engine:

        interesting rock     < interesting human ∧
        interesting fish     < interesting human ∧
        interesting planet   < interesting human ∧
        interesting perfectAI < interesting human

    (human `5`; rock/planet/perfectAI `0`; fish `1`). The brightest bulb is the one
    that is efficient AND alive: bare efficiency (the perfect AI), bare throughput
    (the star), or neither (the rock) is not interesting. Proved by `decide` on the
    closed concrete goal. -/
theorem human_is_the_most_interesting :
    interesting rock < interesting human ∧
    interesting fish < interesting human ∧
    interesting planet < interesting human ∧
    interesting perfectAI < interesting human := by decide

/-! ## 7. THM 6 — Vitality requires the swerve (the general lemma)

The formal core of "perfect and not interesting": for ANY engine, however
efficient, no swerve forces interestingness to zero. A general `∀` lemma, proved in
term mode (`if_neg` on the gate, after unfolding `interesting` and `vital`). -/

/-- **(THM 6) Vitality requires the swerve.** For *every* engine, if it is not
    vital then it is not interesting, whatever its efficiency:

        ∀ e, vital e = false → interesting e = 0.

    No swerve ⇒ zero interestingness — the gate closes regardless of how much the
    engine resolves per unit entropy. This is the formal core of "perfect and not
    interesting": perfection (high efficiency) without the swerve scores `0` on
    interestingness, exactly as a rock does (THM 4).

    **Proof technique (term mode `if_neg`).** Unfold `interesting e` to
    `if vital e then efficiency e else 0` (a `Bool`-guarded `ite`, whose
    `Decidable` instance turns the guard into the proposition `vital e = true`). The
    closing term is `if_neg`, fed a proof that the guard is false: rewriting the
    guard by the hypothesis `vital e = false` reduces it to `false = true`, refuted
    by `Bool.false_ne_true`. `if_neg` then selects the `else` branch, `0`. No
    `∀`-goal is closed by `decide`/`simp`/`omega`; the closing is the `if_neg`
    elimination, with only a closed `Bool` inequality discharged inside it. -/
theorem vitality_requires_the_swerve (e : Engine) (h : vital e = false) :
    interesting e = 0 := by
  unfold interesting
  -- `vital e = false`, so the guard `vital e = true` is false; `if_neg` picks `else 0`.
  exact if_neg (by rw [h]; exact Bool.false_ne_true)
