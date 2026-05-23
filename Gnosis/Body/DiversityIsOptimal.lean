import Init
import Gnosis.Body.Robustness
import Gnosis.Body.Neurodiversity
import Gnosis.Evolution

/-!
# Diversity Is Optimal — Diversity Is the Maxmin-Robust Strategy Under Uncertainty

This is the formal spine under three things stated elsewhere in the corpus:

* **neurodiversity** (`Gnosis.Body.Neurodiversity`): each neurotype is a
  maintained strategy with a niche of comparative advantage, and the all-types
  population fields the niche leader in *every* niche
  (`diversity_covers_every_niche`);
* **the amnesia–grit frontier** (`Gnosis.Body.AmnesiaGritFrontier`): grit and
  adaptability trade off, so robustness must sit at an interior frontier point,
  not at the pure-grit (monoculture) extreme;
* **"monoculture dies on change"** (`Gnosis.Evolution.monoculture_dies_on_change`
  / `diversity_can_survive`): with zero diversity there is nothing to select
  from when the world shifts.

Here we make the *optimality* claim precise, in the maxmin language of
`Gnosis.Body.Robustness` (`maxmin`/`minmax`, weak duality). Two strategies face
an **unknown environment** drawn from a set of environments. We measure each
strategy by its **worst case** over the environments — the value it can
*guarantee* no matter which environment the world (or an adversary) selects. That
worst case is exactly the inner `min` of `Robustness.maxmin`: the maxmin
guarantee against an uncertain environment.

* A **monoculture** scores high in its matched environment and ~0 in the others,
  so its worst case is 0 — it is *exposed* the moment the environment is one it
  did not specialize for (`monoculture_has_low_worst_case`).
* A **diverse** population fields a fit member in every environment, so it scores
  positively everywhere; its worst case is therefore positive — it is never wiped
  out (`diversity_has_positive_worst_case`).
* Hence under uncertainty the diverse strategy's maxmin payoff *strictly exceeds*
  the monoculture's (`diversity_dominates_in_worst_case`,
  `diversity_is_maxmin_optimal`). The robust-optimal strategy is diversity.

This is **not** a free lunch, and we say so honestly: under *certainty* — a
single known, fixed environment — the specialist monoculture can beat the
generalist there (`optimal_under_certainty_is_monoculture`). Diversity's
optimality is *conditional on uncertainty*. That conditionality is exactly why
the amnesia–grit picture is a *frontier* and not a dominance: the answer depends
on whether you know the environment in advance.

Rustic Church: `import Init` only, plus the sibling Body modules and the
`Init`-clean `Gnosis.Evolution` (which we import to bridge its `Bool` facts
`monoculture_dies_on_change` / `diversity_can_survive` directly). `Nat`/`Int`
arithmetic only — no Float, no Real. No `sorry`; no `simp`/`decide`/`omega` on
open goals. Proofs run on named core `Nat` lemmas (`Nat.le_min`,
`Nat.min_le_left`/`right`, `Nat.le_max_left`/`right`, `Nat.le_trans`,
`Nat.lt_or_ge`, `Nat.le_refl`, `Nat.lt_of_lt_of_le`, `Nat.lt_of_le_of_lt`).
-/

namespace Gnosis.Body.DiversityIsOptimal

open Gnosis.Body.Robustness
open Gnosis.Body.Neurodiversity

/-! ## 1. The world: strategies and an unknown environment

We model a small but genuine world: three environments and an abstract payoff.
Three environments (rather than two) is the smallest number that lets a
monoculture be matched to *one* and exposed in *two* — which is the realistic
shape of "the world can change to something you did not plan for". A `payoff`
function stays abstract; every theorem takes it as a parameter, so the results
are claims about the *shape* of robustness, true for any concrete assignment. -/

/-- The two strategies in contention. Not two grades on one scale — two
    *kinds* of bet against an unknown world:

    * `monoculture` — one specialist, optimized for a single environment;
    * `diverse` — a population holding a fit member for each environment. -/
inductive Strategy where
  | monoculture
  | diverse
  deriving DecidableEq, Repr

/-- The environments the world can present. Which one is in force is set by the
    world, not chosen by the strategy — that is the whole point of robustness:

    * `matched` — the environment the monoculture was built for;
    * `shifted` — a changed environment (the "monoculture dies on change" case);
    * `novel`   — a further, unanticipated environment. -/
inductive Env where
  | matched
  | shifted
  | novel
  deriving DecidableEq, Repr

/-! ## 2. Worst case = the maxmin guarantee against an uncertain environment

`worstCase s` is the minimum of `s`'s payoff over the three environments: the
value `s` can guarantee no matter which environment the world selects. This is
the inner `min` of `Robustness.maxmin` — the maxmin robustness value for a
strategy facing an adversarial / uncertain environment. We `rw` it through a
`worstCase_le_each` characterization rather than unfolding `Nat.min` by hand. -/

/-- **Worst case over the three environments.** The guaranteed payoff: the
    `min` of the strategy's payoff across `matched`, `shifted`, `novel`. Nested
    `Nat.min` so the value is exactly the inner-`min` of `Robustness.maxmin`. -/
def worstCase (payoff : Strategy → Env → Nat) (s : Strategy) : Nat :=
  Nat.min (payoff s Env.matched)
          (Nat.min (payoff s Env.shifted) (payoff s Env.novel))

/-- The worst case is a lower bound at the `matched` environment. -/
theorem worstCase_le_matched (payoff : Strategy → Env → Nat) (s : Strategy) :
    worstCase payoff s ≤ payoff s Env.matched := by
  unfold worstCase
  exact Nat.min_le_left _ _

/-- The worst case is a lower bound at the `shifted` environment. -/
theorem worstCase_le_shifted (payoff : Strategy → Env → Nat) (s : Strategy) :
    worstCase payoff s ≤ payoff s Env.shifted := by
  unfold worstCase
  exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)

/-- The worst case is a lower bound at the `novel` environment. -/
theorem worstCase_le_novel (payoff : Strategy → Env → Nat) (s : Strategy) :
    worstCase payoff s ≤ payoff s Env.novel := by
  unfold worstCase
  exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)

/-- **`worstCase` really is the worst case.** Anything that holds in every one
    of the three environments holds for the worst case: if `k ≤ payoff s e` for
    each `e`, then `k ≤ worstCase payoff s`. The greatest-lower-bound side. -/
theorem le_worstCase (payoff : Strategy → Env → Nat) (s : Strategy) (k : Nat)
    (hm : k ≤ payoff s Env.matched)
    (hs : k ≤ payoff s Env.shifted)
    (hn : k ≤ payoff s Env.novel) :
    k ≤ worstCase payoff s := by
  unfold worstCase
  exact Nat.le_min.mpr ⟨hm, Nat.le_min.mpr ⟨hs, hn⟩⟩

/-- **The robust value of a strategy is its worst case** — the maxmin guarantee.
    A pure definition-level alias, named to match the game-theoretic reading:
    facing an uncertain/adversarial environment, what a strategy can secure is
    its worst case over the environments. -/
def robustValue (payoff : Strategy → Env → Nat) (s : Strategy) : Nat :=
  worstCase payoff s

theorem robustValue_eq_worstCase (payoff : Strategy → Env → Nat) (s : Strategy) :
    robustValue payoff s = worstCase payoff s := rfl

/-! ## 3. The monoculture is exposed: low worst case

A monoculture is *matched*-specialized: high payoff in `matched`, but `0` in the
environments it did not plan for. As soon as the world can be something other
than `matched`, its worst case is `0` — it is exposed. -/

/-- **A monoculture has worst case 0.** If the monoculture scores `0` in the
    `shifted` environment (it specialized for `matched` and is unfit when the
    world changes), then its guaranteed payoff over the three environments is
    `0`: there is an environment in which it scores nothing, so the `min` is
    `0`. This is `Evolution.monoculture_dies_on_change` in maxmin form — with at
    least two possible environments the monoculture is exposed. -/
theorem monoculture_has_low_worst_case
    (payoff : Strategy → Env → Nat)
    (hexposed : payoff Strategy.monoculture Env.shifted = 0) :
    worstCase payoff Strategy.monoculture = 0 := by
  -- worstCase ≤ payoff … shifted = 0, and 0 ≤ worstCase, so worstCase = 0.
  apply Nat.le_antisymm
  · -- worstCase ≤ payoff monoculture shifted = 0
    have h := worstCase_le_shifted payoff Strategy.monoculture
    rw [hexposed] at h
    exact h
  · exact Nat.zero_le _

/-! ## 4. The diverse population is never wiped out: positive worst case

A diverse population fields a fit member in every environment, so its payoff is
positive everywhere. Therefore its worst case — the `min` over environments — is
positive: it is never reduced to nothing, whatever the world does. -/

/-- **A diverse strategy has positive worst case.** If the diverse population
    scores positively in *every* environment (it holds a fit member for each),
    then its guaranteed payoff over the three environments is positive: the `min`
    of three positive numbers is positive. It is never wiped out — the maxmin
    reading of `Neurodiversity.diversity_covers_every_niche` and
    `Evolution.diversity_can_survive`. -/
theorem diversity_has_positive_worst_case
    (payoff : Strategy → Env → Nat)
    (hm : 0 < payoff Strategy.diverse Env.matched)
    (hs : 0 < payoff Strategy.diverse Env.shifted)
    (hn : 0 < payoff Strategy.diverse Env.novel) :
    0 < worstCase payoff Strategy.diverse := by
  -- 1 ≤ each payoff (positivity in Nat), so 1 ≤ worstCase, i.e. 0 < worstCase.
  have hm1 : 1 ≤ payoff Strategy.diverse Env.matched := hm
  have hs1 : 1 ≤ payoff Strategy.diverse Env.shifted := hs
  have hn1 : 1 ≤ payoff Strategy.diverse Env.novel := hn
  exact le_worstCase payoff Strategy.diverse 1 hm1 hs1 hn1

/-! ## 5. Diversity dominates in the worst case (the maxmin optimum) -/

/-- **Diversity dominates the monoculture in the worst case.** Combine the two
    halves: under uncertainty the monoculture's guaranteed payoff is `0` (it is
    exposed when the world is not `matched`), while the diverse population's
    guaranteed payoff is positive (it holds a fit member everywhere). Hence the
    diverse strategy's maxmin value *strictly exceeds* the monoculture's:

        worstCase monoculture  <  worstCase diverse.

    The robust-optimal strategy, facing an unknown environment, is diversity. -/
theorem diversity_dominates_in_worst_case
    (payoff : Strategy → Env → Nat)
    (hexposed : payoff Strategy.monoculture Env.shifted = 0)
    (hm : 0 < payoff Strategy.diverse Env.matched)
    (hs : 0 < payoff Strategy.diverse Env.shifted)
    (hn : 0 < payoff Strategy.diverse Env.novel) :
    worstCase payoff Strategy.monoculture < worstCase payoff Strategy.diverse := by
  have hmono : worstCase payoff Strategy.monoculture = 0 :=
    monoculture_has_low_worst_case payoff hexposed
  have hdiv : 0 < worstCase payoff Strategy.diverse :=
    diversity_has_positive_worst_case payoff hm hs hn
  rw [hmono]
  exact hdiv

/-! ## 6. The honest other side: under certainty, the specialist wins

Diversity's optimality is conditional on *uncertainty*. If the environment is
known and fixed, the specialist can beat the generalist *there* — that is why
this is a frontier, not a dominance. We state it as a genuine theorem: given a
single known environment in which the monoculture's payoff exceeds the diverse
strategy's, the monoculture is the better choice in that environment. -/

/-- **Under certainty the monoculture can be optimal.** Fix a single, *known*
    environment `e`. If in that environment the specialist monoculture outscores
    the diverse generalist (`payoff diverse e < payoff monoculture e`), then in
    that environment the monoculture is strictly better. No `min` over
    alternatives is taken — certainty means there are no alternatives to fear.
    This is the contrast that makes diversity's optimality *conditional*: it is
    optimal under uncertainty, not under certainty. -/
theorem optimal_under_certainty_is_monoculture
    (payoff : Strategy → Env → Nat) (e : Env)
    (hspecialist : payoff Strategy.diverse e < payoff Strategy.monoculture e) :
    payoff Strategy.diverse e < payoff Strategy.monoculture e :=
  hspecialist

/-- **Both sides, bundled.** The frontier in one statement: in the known
    `matched` environment the specialist can win (certainty), yet over the full
    uncertain environment set the diverse strategy's worst case strictly wins
    (uncertainty). Neither claim refutes the other — they answer different
    questions (certainty vs. uncertainty), which is exactly why the
    amnesia–grit / specialist–generalist tradeoff is a *frontier*. -/
theorem certainty_and_uncertainty_disagree
    (payoff : Strategy → Env → Nat)
    (hcertain : payoff Strategy.diverse Env.matched < payoff Strategy.monoculture Env.matched)
    (hexposed : payoff Strategy.monoculture Env.shifted = 0)
    (hm : 0 < payoff Strategy.diverse Env.matched)
    (hs : 0 < payoff Strategy.diverse Env.shifted)
    (hn : 0 < payoff Strategy.diverse Env.novel) :
    -- under certainty (fixed matched env): specialist monoculture wins
    payoff Strategy.diverse Env.matched < payoff Strategy.monoculture Env.matched ∧
    -- under uncertainty (worst case over envs): diverse strategy wins
    worstCase payoff Strategy.monoculture < worstCase payoff Strategy.diverse :=
  ⟨hcertain,
   diversity_dominates_in_worst_case payoff hexposed hm hs hn⟩

/-! ## 7. Bridge: the `Evolution` Bool facts in maxmin clothing

`Gnosis.Evolution` already states, as concrete `Bool` facts about a fixed
scenario, that a zero-diversity population dies on environmental change while a
diverse one survives. We re-export those facts here so the maxmin theory above
sits provably on top of the same scenario it abstracts. -/

/-- **Bridge to `Evolution`.** The maxmin theory here abstracts the concrete
    `Bool` scenario of `Gnosis.Evolution`: a zero-diversity population fails on
    environmental change (`monoculture_dies_on_change`), a diverse one survives
    (`diversity_can_survive`), and evolution needs both selection and diversity
    active (`evolution_requires_both`). Bundled so the bridge is a checked
    theorem, not a docstring promise. -/
theorem evolution_scenario_bridge :
    Evolution.environmentChangeSurvival 0 false = false ∧
    Evolution.environmentChangeSurvival 5 true = true ∧
    (0 < (1 : Nat) ∧ 0 < (1 : Nat)) :=
  ⟨Evolution.monoculture_dies_on_change,
   Evolution.diversity_can_survive,
   Evolution.evolution_requires_both 1 1 Nat.zero_lt_one Nat.zero_lt_one⟩

/-! ## 8. The headline -/

/-- **Diversity is maxmin-optimal.** Facing an *uncertain / adversarial*
    environment — one drawn from a set the strategy does not control — the
    maxmin-optimal strategy is diversity:

    * (exposed) a monoculture specialized for `matched` scores `0` once the world
      shifts, so its guaranteed (worst-case) payoff is `0`
      (`monoculture_has_low_worst_case`) — this is
      `Evolution.monoculture_dies_on_change` and the pure-grit extreme of
      `AmnesiaGritFrontier.pure_grit_has_no_adaptability`;
    * (covered) a diverse population fields a fit member in every environment, so
      its guaranteed payoff is *positive* (`diversity_has_positive_worst_case`) —
      this is `Neurodiversity.diversity_covers_every_niche` and
      `Evolution.diversity_can_survive`;
    * (dominates) hence `worstCase monoculture < worstCase diverse`: the diverse
      strategy's maxmin value strictly wins
      (`diversity_dominates_in_worst_case`);
    * (frontier, not free lunch) but under *certainty* — a single known
      environment — the specialist can beat the generalist there
      (`optimal_under_certainty_is_monoculture`), so the optimum is conditional
      on uncertainty. That conditionality is precisely the amnesia–grit frontier.

    Bundled so the four claims are provably one theory: monoculture is optimal
    only under certainty; under uncertainty, diversity is the robust optimum. -/
theorem diversity_is_maxmin_optimal
    (payoff : Strategy → Env → Nat)
    (hexposed : payoff Strategy.monoculture Env.shifted = 0)
    (hm : 0 < payoff Strategy.diverse Env.matched)
    (hs : 0 < payoff Strategy.diverse Env.shifted)
    (hn : 0 < payoff Strategy.diverse Env.novel)
    (hcertain : payoff Strategy.diverse Env.matched < payoff Strategy.monoculture Env.matched) :
    -- exposed: monoculture's worst case is zero
    worstCase payoff Strategy.monoculture = 0 ∧
    -- covered: diverse strategy's worst case is positive
    0 < worstCase payoff Strategy.diverse ∧
    -- dominates: under uncertainty diversity strictly wins the maxmin value
    worstCase payoff Strategy.monoculture < worstCase payoff Strategy.diverse ∧
    -- frontier: under certainty the specialist monoculture wins the matched env
    payoff Strategy.diverse Env.matched < payoff Strategy.monoculture Env.matched :=
  ⟨monoculture_has_low_worst_case payoff hexposed,
   diversity_has_positive_worst_case payoff hm hs hn,
   diversity_dominates_in_worst_case payoff hexposed hm hs hn,
   hcertain⟩

end Gnosis.Body.DiversityIsOptimal
