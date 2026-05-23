import Init
import Gnosis.Body.ConservationOfVitality

/-!
# Gender as Budget-Diversity (r/K life-history) — the Lean mirror

The energy-budget theory of `aeon-corpus/src/gender_budget.rs`, proved. From
`Gnosis/Body/ConservationOfVitality.lean` each agent has a conserved vitality
budget `V = burn_rate × lifespan`. A **gender** is a specialized allocation of that
*same* fixed budget:

* **fast / r-strategy** — high rate, short life (men-leaning, `RateOfLiving.lean`),
* **slow / K-strategy** — low rate, long life (women-leaning),
* **pan / the `0`** — the balanced generalist, non-breeding.

A volatile (high-mortality) world rewards output *rate*; a stable world rewards
*lifespan*. A population that **splits into complementary specialists** (genders)
then maxmin-beats both the best single-gender monoculture and a uniform population
of generalists — the gender split is the resilient partition of the conserved
budget (`Gnosis/Body/DiversityIsOptimal.lean`; the general `maxmin ≤ minmax` weak
duality lives in `Gnosis/Body/Robustness.lean`). So gender emerges *by* category
budget: a diversity partition of the one conserved vitality budget.

## Scope (honored)

A life-history (r/K) model of why budget-diversity is adaptive — suggestive of a
role for gender in maintaining metabolic diversity, NOT a claim about why sex
evolved (recombination/anisogamy). Concrete `Nat` model; `decide` on fully-closed
literal goals only. The general weak-duality is cited, not re-proved here.
-/

namespace Gnosis.Body.GenderBudget

open Gnosis.Body.ConservationOfVitality

/-- The conserved vitality budget every gender carries. -/
def budgetTarget : Nat := 2400

/-- A life-history: an allocation of the budget into rate and lifespan. -/
structure LifeHistory where
  burnRate : Nat
  lifespan : Nat
  deriving Repr, DecidableEq

/-- Budget spent over a life = rate × lifespan (reuses `totalVitality`). -/
def budget (lh : LifeHistory) : Nat := totalVitality lh.burnRate lh.lifespan

/-- The genders, as conserved allocations of the one budget. -/
def fast : LifeHistory := ⟨60, 40⟩    -- r-strategy: high rate, short life
def slow : LifeHistory := ⟨24, 100⟩   -- K-strategy: low rate, long life
def pan  : LifeHistory := ⟨40, 60⟩    -- the 0: the balanced generalist

/-- An environment: high or low extrinsic mortality. -/
inductive Env
  | volatile  -- rewards output rate (reproduce before extrinsic death)
  | stable    -- rewards lifespan (sustained presence)
  deriving DecidableEq, Repr

/-- Fitness: the volatile world pays for rate, the stable world for lifespan.
    Same conserved budget, opposite payoffs. -/
def fitness (lh : LifeHistory) : Env → Nat
  | .volatile => lh.burnRate
  | .stable => lh.lifespan

/-- Worst case of a single-gender monoculture across the two environments. -/
def monocultureWorst (lh : LifeHistory) : Nat :=
  Nat.min (fitness lh .volatile) (fitness lh .stable)

/-- Best guaranteed by committing to one gender (maxmin over the two specialists). -/
def bestMonoculture (g1 g2 : LifeHistory) : Nat :=
  Nat.max (monocultureWorst g1) (monocultureWorst g2)

/-- The diverse population answers each environment with its best-suited member;
    its guarantee is the worst of those (minmax). -/
def diversePopulation (g1 g2 : LifeHistory) : Nat :=
  Nat.min (Nat.max (fitness g1 .volatile) (fitness g2 .volatile))
          (Nat.max (fitness g1 .stable) (fitness g2 .stable))

/-- **Every gender conserves the budget** — same `V`, different gradient. -/
theorem genders_conserve :
    budget fast = budgetTarget ∧ budget slow = budgetTarget ∧ budget pan = budgetTarget := by
  decide

/-- **Specialists are complementary** — fast wins the volatile world, slow the
    stable one. No single allocation dominates both. -/
theorem specialists_complementary :
    fitness slow .volatile < fitness fast .volatile
      ∧ fitness fast .stable < fitness slow .stable := by
  decide

/-- **Diversity beats monoculture** — the diverse population (minmax `= 60`)
    strictly exceeds the best single gender (maxmin `= 40`). `DiversityIsOptimal`. -/
theorem diversity_beats_monoculture :
    bestMonoculture fast slow < diversePopulation fast slow := by
  decide

/-- **The split beats the generalist** — two budget-specialists (`60`) out-hedge a
    uniform population of generalists (`pan`, `40`). The evolutionary case for the
    gender split: differentiate the conserved budget rather than average it. -/
theorem split_beats_generalist :
    monocultureWorst pan < diversePopulation fast slow := by
  decide

/-- **Gender is budget-diversity** (headline). All genders carry the same conserved
    budget; the specialists are complementary; the diverse split maxmin-beats both
    the best monoculture and the generalist. Gender emerges *by* category budget —
    the resilient diversity partition of the one conserved vitality budget. -/
theorem gender_is_budget_diversity :
    (budget fast = budgetTarget ∧ budget slow = budgetTarget ∧ budget pan = budgetTarget)
      ∧ (fitness slow .volatile < fitness fast .volatile
          ∧ fitness fast .stable < fitness slow .stable)
      ∧ bestMonoculture fast slow < diversePopulation fast slow
      ∧ monocultureWorst pan < diversePopulation fast slow := by
  decide

end Gnosis.Body.GenderBudget
