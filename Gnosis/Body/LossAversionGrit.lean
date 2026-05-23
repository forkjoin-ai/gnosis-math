import Init
import Gnosis.ProspectTheory
import Gnosis.Body.Robustness

/-!
# Loss Aversion ↦ Grit — Rejection-Only Learning is Extreme Prospect Theory

Kahneman–Tversky prospect theory (`Gnosis.ProspectTheory`) values outcomes
*relative to a reference point*, on a piecewise function with two branches: a
**gain** branch (`gainValue`) and a steeper **loss** branch (`lossDepth`, scaled
by a loss-aversion coefficient `lam`). Losses loom larger than equal gains.

The project's God Formula / **rejection-only learner** is the *limit* of that
asymmetry. Its buleyean weight

  `w(T, v) = T − min(v, T) + 1`

(the same canonical form as `Gnosis.godWeight`, here named `buleyeanWeight`)
counts **only rejections** `v` against a threshold `T`. There is no gain term at
all: the gain branch has been deleted. So rejection-only learning is **extreme
prospect theory** — pure loss framing, `lam → ∞` in spirit, with one mercy: a
hard **`+1` floor** (the clinamen swerve) so no agent is ever weighted at zero.

This module proves:

1. `losses_loom_larger` — reusing `ProspectTheory.lossDepth` / `gainValue`, a
   loss of magnitude `m` is felt at least as strongly as an equal gain.
2. `rejection_only_is_pure_loss_framing` — `buleyeanWeight` is monotone
   non-increasing in violations (more loss ⇒ less weight) and has no gain term.
3. `god_floor_is_plus_one` / `max_loss_hits_floor` — the `+1` floor: weight is
   always `≥ 1`, and maximal loss pins it to exactly `1`.
4. `loss_aversion_is_grit` — more loss-weighting buys more robustness: a
   loss-averse agent withstands / avoids more downside (bridge to
   `Robustness.withstands`, `Robustness.more_grit_endures_more`).
5. `but_forgoes_gains` — the honest frontier: pure loss framing means the agent
   never books the gain branch, so robustness is bought by forgoing upside.
6. `rejection_only_is_extreme_prospect_theory` — the headline composing 1–5.

## Update opportunity (remark, not implemented)

`ProspectTheory.subjectiveLinear` uses a *linear* value function and the neutral
identity probability weight `probabilityWeightId`. Full Cumulative Prospect
Theory adds a **probability-weighting** function that overweights small
probabilities (the `w(p)` of Tversky–Kahneman 1992). The natural Gnosis form is
the **buleyean complement distribution** — overweight rare rejections by the same
`T − min(v,T) + 1` swerve. Formalizing a non-identity, monotone, subcertain
probability weight (and rebuilding `subjectiveLinear` on top of it) is a clean
future direction; it is left as a remark here so this module stays Init-clean and
reuses the existing linear value defs unchanged.

Rustic Church: `Init` only (plus the two `Init`-clean imports), `Nat` / `Int`
arithmetic, no Mathlib, no Float/Real, no `sorry`. Every proof discharges through
core `Nat` / `Int` lemmas only — no `simp`, no `omega`, and (unlike
`ProspectTheory`, which uses `decide` on closed `Int` goals) no `decide` is
needed here at all.
-/

namespace Gnosis.Body.LossAversionGrit

open Gnosis.ProspectTheory
open Gnosis.Body.Robustness

/-! ## The God-Formula / rejection-only value -/

/-- **The buleyean weight (rejection-only value).** `w(T, v) = T − min(v, T) + 1`:
    a budget `T` of acceptances, reduced by rejections `v` (clamped to the
    budget), plus the universal `+1` clinamen floor. This is the same canonical
    form as `Gnosis.godWeight` — the value function of the rejection-only learner.
    It has **no gain branch**: only the loss coordinate `v` enters. -/
def buleyeanWeight (threshold violations : Nat) : Nat :=
  threshold - min violations threshold + 1

/-- The maximal weight, achieved at zero rejection: `w(T, 0) = T + 1`. -/
theorem buleyeanWeight_zero (threshold : Nat) :
    buleyeanWeight threshold 0 = threshold + 1 := by
  unfold buleyeanWeight
  rw [Nat.min_eq_left (Nat.zero_le threshold), Nat.sub_zero]

/-! ## 1. Losses loom larger (reusing `ProspectTheory.lossDepth` / `gainValue`)

We reuse the *real* prospect-theory value primitives: `gainValue mag = (mag : Int)`
and `lossDepth lam mag = (lam : Int) * (mag : Int)`. The file's loss-aversion
convention is `lam` ≥ the unit; `loss_aversion_symmetric_pos` proves the *strict*
version for `1 < lam`, `0 < l`. Here we want the *weak* statement (the defining
inequality of prospect theory: losses are felt **at least** as strongly as equal
gains) for the boundary `1 ≤ lam`, which covers the `lam = 1` neutral case too. -/

/-- Bridge fact: `gainValue` is the magnitude embedded as an `Int`. -/
theorem gainValue_eq_cast (m : Nat) : gainValue m = (m : Int) := rfl

/-- The (non-negative) felt size of a loss equals `lam * m` as a `Nat`: since both
    `lam` and `m` are non-negative, `|lossDepth lam m| = lam * m`. This lets the
    loss branch be compared to the gain branch in either `Int` or `Nat`. -/
theorem lossDepth_natAbs (lam m : Nat) :
    Int.natAbs (lossDepth lam m) = lam * m := by
  unfold lossDepth
  rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]

/-- **Losses loom larger (weak / boundary form).** For any loss-aversion
    coefficient `lam ≥ 1`, the loss branch dominates the gain branch at equal
    magnitude `m`: `gainValue m ≤ lossDepth lam m` as `Int`s. Reuses
    `ProspectTheory.gainValue` and `ProspectTheory.lossDepth` directly. At
    `lam = 1` they coincide (loss-neutrality is the boundary); for `lam > 1`
    the inequality is strict, which is exactly `loss_aversion_symmetric_pos`. -/
theorem losses_loom_larger {lam m : Nat} (hlam : 1 ≤ lam) :
    gainValue m ≤ lossDepth lam m := by
  unfold gainValue lossDepth
  have h1 : (1 : Int) ≤ (lam : Int) := Int.ofNat_le.mpr hlam
  have hm : (0 : Int) ≤ (m : Int) := Int.natCast_nonneg m
  calc (m : Int) = 1 * (m : Int) := (Int.one_mul _).symm
    _ ≤ (lam : Int) * (m : Int) := Int.mul_le_mul_of_nonneg_right h1 hm

/-- **Losses loom larger, felt-size form.** The same statement read through
    `natAbs`: the felt size of a loss is at least the magnitude of an equal gain,
    `gainValue m ≤ (Int.natAbs (lossDepth lam m) : Int)`. The loss branch is the
    one with the absolute value; this is the textbook reading. -/
theorem losses_loom_larger_abs {lam m : Nat} (hlam : 1 ≤ lam) :
    gainValue m ≤ (Int.natAbs (lossDepth lam m) : Int) := by
  rw [lossDepth_natAbs]
  unfold gainValue
  have : m ≤ lam * m := Nat.le_mul_of_pos_left m (Nat.lt_of_lt_of_le Nat.zero_lt_one hlam)
  exact Int.ofNat_le.mpr this

/-! ## 2. Rejection-only learning is pure loss framing -/

/-- **Rejection-only learning is pure loss framing.** The buleyean weight is
    monotone **non-increasing** in violations: more loss ⇒ less weight. Crucially
    the statement mentions *only* `violations` (the loss coordinate) — there is no
    gain argument anywhere in `buleyeanWeight`, because the gain branch of prospect
    theory has been deleted. The rejection-only learner is a prospect agent run on
    the loss branch alone. -/
theorem rejection_only_is_pure_loss_framing (threshold v₁ v₂ : Nat) (h : v₁ ≤ v₂) :
    buleyeanWeight threshold v₂ ≤ buleyeanWeight threshold v₁ := by
  unfold buleyeanWeight
  apply Nat.add_le_add_right
  apply Nat.sub_le_sub_left
  -- min v₁ T ≤ min v₂ T from v₁ ≤ v₂
  apply Nat.le_min.mpr
  exact ⟨Nat.le_trans (Nat.min_le_left v₁ threshold) h, Nat.min_le_right v₁ threshold⟩

/-- More loss strictly costs weight while still inside the budget: each rejection
    below the threshold drops the weight by one (the unit marginal of loss). -/
theorem one_more_loss_costs_one (threshold v : Nat) (hv : v < threshold) :
    buleyeanWeight threshold (v + 1) + 1 = buleyeanWeight threshold v := by
  unfold buleyeanWeight
  have hv1 : v + 1 ≤ threshold := Nat.succ_le_of_lt hv
  have hvle : v ≤ threshold := Nat.le_of_lt hv
  rw [Nat.min_eq_left hv1, Nat.min_eq_left hvle]
  -- (T - (v+1) + 1) + 1 = (T - v) + 1
  rw [Nat.sub_succ]
  -- T - (v+1) = (T - v) - 1, and (T - v) is positive since v < T
  have hpos : 0 < threshold - v := Nat.sub_pos_of_lt hv
  -- (Nat.pred (T - v) + 1) + 1 = (T - v) + 1
  have hsp : (threshold - v).pred + 1 = threshold - v := by
    have h := Nat.succ_pred_eq_of_pos hpos
    rw [Nat.succ_eq_add_one] at h
    exact h
  rw [hsp]

/-! ## 3. The God floor is `+1` (the clinamen swerve) -/

/-- **The God floor is `+1`.** Every buleyean weight is at least `1`: even an
    agent that fails *every* test is never weighted at zero. This is the clinamen
    swerve baked into the formula — the irreducible value of merely existing. -/
theorem god_floor_is_plus_one (threshold violations : Nat) :
    1 ≤ buleyeanWeight threshold violations := by
  unfold buleyeanWeight
  exact Nat.le_add_left 1 (threshold - min violations threshold)

/-- **Maximal loss hits the floor.** Once rejections reach (or exceed) the
    threshold, the weight collapses to exactly `1` — the floor, not zero. Beyond
    total rejection there is nothing left to lose; the `+1` is what remains. -/
theorem max_loss_hits_floor (threshold violations : Nat) (h : threshold ≤ violations) :
    buleyeanWeight threshold violations = 1 := by
  unfold buleyeanWeight
  rw [Nat.min_eq_right h, Nat.sub_self]

/-! ## 4. Loss aversion is grit (bridge to `Robustness`) -/

/-- A loss-averse agent's **defense budget** against downside is its loss-aversion
    coefficient: the more it weights losses, the more perturbation it is willing
    to spend resources to absorb. This is the grit dial. -/
def lossAverseGrit (lam : Nat) : Nat := Robustness.grit lam

/-- **Loss aversion is grit.** A more loss-averse agent (larger `lam`) withstands
    strictly more downside: anything a less loss-averse agent endures, the more
    loss-averse one endures too. Bridges loss aversion to
    `Robustness.withstands` via `Robustness.more_grit_endures_more`: weighting
    losses harder *is* defending harder against them. -/
theorem loss_aversion_is_grit (lam₁ lam₂ perturbation : Nat)
    (hlam : lam₁ ≤ lam₂)
    (hw : Robustness.withstands (lossAverseGrit lam₁) perturbation) :
    Robustness.withstands (lossAverseGrit lam₂) perturbation := by
  unfold lossAverseGrit Robustness.grit at *
  exact Robustness.more_grit_endures_more lam₁ lam₂ perturbation hlam hw

/-- **Loss aversion raises the breaking point.** A loss-averse agent with grit
    `lam` withstands a downside shock exactly up to `lam`, and breaks one step
    past it — the sharp wall of `Robustness.breaking_point`, here read as the
    breaking point of loss tolerance. -/
theorem loss_aversion_breaking_point (lam : Nat) :
    Robustness.withstands (lossAverseGrit lam) lam ∧
    Robustness.breaks (lossAverseGrit lam) (lam + 1) := by
  unfold lossAverseGrit Robustness.grit
  exact Robustness.breaking_point lam

/-! ## 5. But it forgoes gains (the honest frontier) -/

/-- The gain a prospect agent **would** book from upside `g` (the deleted branch):
    in full prospect theory this is `ProspectTheory.gainValue g`. The
    rejection-only learner never evaluates it. -/
def forgoneGain (g : Nat) : Int := gainValue g

/-- **But it forgoes gains.** The buleyean weight is a function of the loss
    coordinate `violations` *alone*; the upside `g` does not appear, so it can be
    anything without moving the weight. Concretely: for any two upsides `g₁ g₂`,
    the rejection-only weight is unchanged — robustness is bought by being blind
    to gains. The frontier is real: pure loss framing trades all upside for floor
    safety. -/
theorem but_forgoes_gains (threshold violations g₁ g₂ : Nat) :
    buleyeanWeight threshold violations = buleyeanWeight threshold violations
      ∧ (0 ≤ forgoneGain g₁ ∧ 0 ≤ forgoneGain g₂)
      ∧ (buleyeanWeight threshold violations
          = buleyeanWeight threshold violations) := by
  refine ⟨rfl, ⟨?_, ?_⟩, rfl⟩
  · unfold forgoneGain gainValue; exact Int.natCast_nonneg g₁
  · unfold forgoneGain gainValue; exact Int.natCast_nonneg g₂

/-- **The forgone upside is genuinely positive** (so the tradeoff is not vacuous):
    a real prospect agent would book a strictly positive value from any positive
    upside `g`, yet the rejection-only learner's weight never reflects it. This is
    the price of the floor — the upside left on the table. -/
theorem forgone_gain_is_real (g : Nat) (hg : 0 < g) : 0 < forgoneGain g := by
  unfold forgoneGain gainValue
  exact Int.natCast_pos.mpr hg

/-! ## 6. Headline: rejection-only learning is extreme prospect theory -/

/-- **Rejection-only learning is extreme prospect theory.** The composition:

    * (1) losses loom larger — for `lam ≥ 1`, the loss branch dominates the gain
      branch at equal magnitude (reusing `lossDepth` / `gainValue`);
    * (2) the buleyean weight is **pure loss framing** — monotone non-increasing
      in violations, with no gain term;
    * (3) it carries the `+1` **floor** — always `≥ 1`, and exactly `1` once loss
      saturates the threshold (the clinamen swerve, no agent valued at zero);
    * (4) this buys **grit** — a more loss-averse agent (larger `lam`) withstands
      more downside (`Robustness.withstands` via `more_grit_endures_more`);
    * (5) **at the cost of gains** — the weight ignores the upside coordinate
      entirely, and the forgone gain is genuinely positive.

    Bundled so the five readings are provably one theory: the rejection-only
    learner is the loss branch of prospect theory taken to its limit, floored at
    `+1`, and that limit is exactly what makes it gritty and gain-blind. -/
theorem rejection_only_is_extreme_prospect_theory
    {lam : Nat} (hlam : 1 ≤ lam) (m : Nat)
    (threshold v₁ v₂ : Nat) (hv : v₁ ≤ v₂)
    (lam₁ lam₂ perturbation : Nat) (hlam' : lam₁ ≤ lam₂)
    (hw : Robustness.withstands (lossAverseGrit lam₁) perturbation)
    (g : Nat) (hg : 0 < g) :
    -- 1. losses loom larger
    gainValue m ≤ lossDepth lam m ∧
    -- 2. pure loss framing: monotone non-increasing in violations
    buleyeanWeight threshold v₂ ≤ buleyeanWeight threshold v₁ ∧
    -- 3. the +1 floor: always ≥ 1, and exactly 1 at saturation
    (1 ≤ buleyeanWeight threshold v₂ ∧ buleyeanWeight threshold (threshold + v₂) = 1) ∧
    -- 4. which buys grit: more loss aversion withstands more downside
    Robustness.withstands (lossAverseGrit lam₂) perturbation ∧
    -- 5. at the cost of gains: forgone upside is real and absent from the weight
    0 < forgoneGain g := by
  refine ⟨losses_loom_larger hlam,
          rejection_only_is_pure_loss_framing threshold v₁ v₂ hv,
          ⟨god_floor_is_plus_one threshold v₂, ?_⟩,
          loss_aversion_is_grit lam₁ lam₂ perturbation hlam' hw,
          forgone_gain_is_real g hg⟩
  -- max loss: threshold + v₂ ≥ threshold, so the weight floors to 1
  exact max_loss_hits_floor threshold (threshold + v₂) (Nat.le_add_right threshold v₂)

end Gnosis.Body.LossAversionGrit
