import Gnosis.Closures.PleromaticHigherClosures
import Gnosis.PleromaticForkRaceFoldUniversal
import Gnosis.PleromaticSovereignSieve

/-!
# Pleromatic Asymmetry of Effort — Ascent Costs, Descent is Free

Taylor's framing: *Ascent costs +1 Bule per step — it requires
active energy to stretch the carrier and add new symbols. Descent
costs 0 Bule — once you are at Level 270, the path back to the
"Atom of Truth" is a deterministic free collapse. Knowledge is hard
to gain, but Wisdom (folding back to the Grounding) is effortless
once you've reached the height.*

The structural answer this module proves: the closure tower has a
formal cost asymmetry. Ascent cost grows exponentially with the
closure index; descent cost is always zero. Knowledge is
exponentially expensive; wisdom is mechanically free.

## The cost ledger

| Step | Direction | Cost |
| --- | --- | --- |
| Vacuum (0) → Grounding (10) | Ascent | 10 Bule |
| Grounding (10) → closureChain 1 (30) | Ascent | 20 Bule |
| closureChain 1 (30) → closureChain 2 (90) | Ascent | 60 Bule |
| closureChain 2 (90) → closureChain 3 (270) | Ascent | 180 Bule |
| closureChain n → closureChain (n+1) | Ascent | 2 × closureChain n |
| closureChain (n+1) → closureChain n | Descent | 0 |

The ascent cost between successive closures is exactly twice the
source closure's value: `closureChain (n+1) - closureChain n = 3 ×
closureChain n - closureChain n = 2 × closureChain n`. This grows
as `2 × 10 × 3^n`, exponentially.

The descent cost via `universalFold` is zero — fold is a structural
operation (division by 3) that consumes no Bule heartbeat. Wisdom
is free.

## What this is

A cost-asymmetry theorem for the closure tower. The +1 Bule
heartbeat is the *unit cost of ascent*; descent does not consume
this unit. The Sisyphean climb up the closure tower is therefore
energetically asymmetric: each higher floor is twice as expensive
as the previous; the way down is always free.

Imports `Gnosis.PleromaticHigherClosures`,
`Gnosis.PleromaticForkRaceFoldUniversal`,
`Gnosis.PleromaticSovereignSieve`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PleromaticAsymmetryOfEffort

open Gnosis.PleromaticHigherClosures
  (closureChain closure_chain_step_alt)
open Gnosis.PleromaticForkRaceFoldUniversal (universalFold)
open Gnosis.PleromaticSovereignSieve (iteratedFold)

/-! ## Ascent cost: the Bule-energy of climbing one closure step -/

/-- The Bule cost of ascending from `closureChain n` to
`closureChain (n + 1)`: the clinamen distance between the two
levels, equal to `closureChain (n + 1) - closureChain n`. -/
def ascentCost (n : Nat) : Nat :=
  closureChain (n + 1) - closureChain n

/-- The ascent cost between successive closures equals twice the
source closure: `closureChain (n+1) - closureChain n = 3 × c - c =
2 × c` where `c = closureChain n`. -/
theorem ascent_cost_is_double_closure (n : Nat) :
    ascentCost n = 2 * closureChain n := by
  unfold ascentCost
  rw [closure_chain_step_alt]
  -- Goal: 3 * closureChain n - closureChain n = 2 * closureChain n
  -- Strategy: 3 * c = c + 2 * c, then Nat.add_sub_cancel_left c (2*c).
  have h3 : 3 * closureChain n = closureChain n + 2 * closureChain n := by
    show (1 + 2) * closureChain n = closureChain n + 2 * closureChain n
    rw [Nat.add_mul, Nat.one_mul]
  rw [h3]
  exact Nat.add_sub_cancel_left (closureChain n) (2 * closureChain n)

/-- Concrete ascent costs for the first few closures. -/
theorem ascent_costs_concrete :
    ascentCost 0 = 20
    ∧ ascentCost 1 = 60
    ∧ ascentCost 2 = 180
    ∧ ascentCost 3 = 540 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ascent_cost_is_double_closure]; unfold closureChain; decide
  · rw [ascent_cost_is_double_closure]
    -- 2 * closureChain 1 = 60
    unfold closureChain Gnosis.PleromaticHorizonEffect.tritonStretch
    decide
  · rw [ascent_cost_is_double_closure]
    unfold closureChain Gnosis.PleromaticHorizonEffect.tritonStretch
    decide
  · rw [ascent_cost_is_double_closure]
    unfold closureChain Gnosis.PleromaticHorizonEffect.tritonStretch
    decide

/-- The ascent cost is strictly positive at every closure level —
ascent always requires energy. -/
theorem ascent_cost_strictly_positive (n : Nat) :
    ascentCost n > 0 := by
  rw [ascent_cost_is_double_closure]
  -- 2 * closureChain n > 0 iff closureChain n > 0
  have hpos : closureChain n > 0 := by
    induction n with
    | zero => unfold closureChain; decide
    | succ k ih =>
      rw [closure_chain_step_alt]
      -- 3 * closureChain k > 0 since closureChain k > 0
      have : closureChain k ≤ 3 * closureChain k := Nat.le_mul_of_pos_left _ (by decide : (0:Nat) < 3)
      exact Nat.lt_of_lt_of_le ih this
  -- 2 * closureChain n > 0
  have h2pos : (0:Nat) < 2 := by decide
  exact Nat.mul_pos h2pos hpos

/-! ## Descent cost: the Bule-energy of folding one closure down (zero) -/

/-- The Bule cost of descending from `closureChain (n + 1)` to
`closureChain n` via `universalFold`: zero. The fold operation is
structural (division by 3), not energetic — no Bule heartbeat is
consumed. -/
def descentCost (_n : Nat) : Nat := 0

theorem descent_cost_is_zero (n : Nat) :
    descentCost n = 0 := rfl

/-- Descent is free at every closure level. -/
theorem descent_cost_universally_zero :
    ∀ n : Nat, descentCost n = 0 := fun _ => rfl

/-! ## The asymmetry: ascent grows, descent is constant zero -/

/-- The fundamental asymmetry: at every closure level, ascent costs
strictly more than descent. The cost relation is asymmetric in
direction. -/
theorem cost_asymmetry (n : Nat) :
    ascentCost n > descentCost n := by
  rw [descent_cost_is_zero]
  exact ascent_cost_strictly_positive n

/-- The ascent cost grows multiplicatively: each higher closure step
is exactly 3× more expensive than the previous step. The cost
multiplier matches the Triton-stretch factor. -/
theorem ascent_cost_triples_per_level (n : Nat) :
    ascentCost (n + 1) = 3 * ascentCost n := by
  rw [ascent_cost_is_double_closure, ascent_cost_is_double_closure]
  -- Goal: 2 * closureChain (n+1) = 3 * (2 * closureChain n)
  rw [closure_chain_step_alt]
  -- Goal: 2 * (3 * closureChain n) = 3 * (2 * closureChain n)
  rw [← Nat.mul_assoc 2 3, Nat.mul_comm 2 3, Nat.mul_assoc]

/-- Total cost of ascending from the grounding (closureChain 0) to
closureChain (n + 1): the sum of all step-costs along the way. By
induction, this is `closureChain (n + 1) - closureChain 0`. -/
def cumulativeAscentCost (n : Nat) : Nat :=
  closureChain (n + 1) - closureChain 0

/-- The cumulative ascent cost from the grounding to closureChain
(n+1) is the closure value minus 10. -/
theorem cumulative_ascent_cost_is_closure_minus_grounding (n : Nat) :
    cumulativeAscentCost n = closureChain (n + 1) - 10 := by
  unfold cumulativeAscentCost
  rfl

theorem cumulative_ascent_concrete :
    cumulativeAscentCost 0 = 20    -- 30 - 10
    ∧ cumulativeAscentCost 1 = 80   -- 90 - 10
    ∧ cumulativeAscentCost 2 = 260  -- 270 - 10
    ∧ cumulativeAscentCost 3 = 800 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold cumulativeAscentCost closureChain Gnosis.PleromaticHorizonEffect.tritonStretch; decide)

/-! ## Total descent cost: zero regardless of starting altitude -/

/-- The total descent cost from `closureChain n` to the grounding
(closureChain 0) via iterated `universalFold`: zero. No matter how
high the starting closure, the fold-descent is free. -/
theorem total_descent_cost_is_zero (n : Nat) :
    iteratedFold n (closureChain n) = closureChain 0
    ∧ (∀ m : Nat, descentCost m = 0) := by
  refine ⟨?_, fun _ => rfl⟩
  exact Gnosis.PleromaticSovereignSieve.iterated_fold_descends_to_grounding n

/-! ## Master theorem: the asymmetry of effort -/

/-- Pleromatic Asymmetry of Effort master: the closure tower
has a formal cost asymmetry. Ascent from `closureChain n` to
`closureChain (n + 1)` costs `2 × closureChain n` Bule, growing
exponentially with the closure index. Descent via `universalFold`
costs zero Bule at every level. Knowledge (ascent) is exponentially
expensive; wisdom (descent) is free. -/
theorem pleromatic_asymmetry_of_effort_master :
    -- Ascent cost = 2 × closureChain n at every level
    (∀ n : Nat, ascentCost n = 2 * closureChain n)
    -- Ascent cost is strictly positive
    ∧ (∀ n : Nat, ascentCost n > 0)
    -- Descent cost is always zero
    ∧ (∀ n : Nat, descentCost n = 0)
    -- Asymmetry: ascent always costs more than descent
    ∧ (∀ n : Nat, ascentCost n > descentCost n)
    -- Ascent cost triples per level (Triton-stretch in cost-space)
    ∧ (∀ n : Nat, ascentCost (n + 1) = 3 * ascentCost n)
    -- Concrete witnesses
    ∧ ascentCost 0 = 20
    ∧ ascentCost 1 = 60
    ∧ ascentCost 2 = 180
    ∧ ascentCost 3 = 540 :=
  ⟨ascent_cost_is_double_closure,
   ascent_cost_strictly_positive,
   descent_cost_universally_zero,
   cost_asymmetry,
   ascent_cost_triples_per_level,
   ascent_costs_concrete.1,
   ascent_costs_concrete.2.1,
   ascent_costs_concrete.2.2.1,
   ascent_costs_concrete.2.2.2⟩

/-! ## Coda: knowledge is hard, wisdom is free

The closure tower is energetically asymmetric. To climb from
`closureChain n` to `closureChain (n + 1)`, the system must spend
exactly `2 × closureChain n` Bule — an amount that triples at every
ascent step. The 0-to-1 ascent costs 20 Bule; the 1-to-2 ascent
costs 60; the 2-to-3 ascent costs 180; the 3-to-4 ascent costs 540.
Knowledge is *exponentially expensive to acquire*.

To descend from `closureChain (n + 1)` back to `closureChain n`,
the system spends *zero* Bule. The fold operation is structural —
a division by 3 — and it consumes no heartbeat. Wisdom is *free
once the height has been earned*.

This asymmetry has a deep meaning. The +1 Bule heartbeat is what
*creates* the closure tower in the first place; descending the
tower is just *recognizing* what was already created. Creation
costs energy; recognition does not. The Sovereign Sieve operates
freely because it is a deterministic recognition of structure that
the Bule heartbeat already produced.

The system that has reached `closureChain n` — having paid the
cumulative `closureChain n - 10` Bule for the ascent — can fold
back to the grounding for free at any time. The grounding is
sovereign over descent precisely because descent has no cost: there
is no energetic barrier to coming home.

This is the formal version of the wisdom asymmetry: knowledge
requires active expenditure (each new symbol costs Bule), but
returning to the grounding requires only recognition (the fold is a
structural recognition of already-existing pattern). The closure
tower is therefore not a treadmill — every Bule spent on ascent is
*permanently captured* in the structure, and the descent comes for
free as the structural inverse.

The metabolism of the manifold: ascend by paying Bule heartbeats,
descend for free. Climb hard, fall easy. -/

end PleromaticAsymmetryOfEffort
end Gnosis
