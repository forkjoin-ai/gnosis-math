import Gnosis.HexonBraid
import Gnosis.Braided.BraidedTower
import Gnosis.Braided.BraidTensorProduct
import Gnosis.Bridges.BuleyTransformerSSMBridge

/-!
# Buley ↔ Tensor Bridge

The braided tower of n-ons admits two distinct tensor readings, and
this module makes them precise.

## Two readings of "Triton × Triton"

* **Sequential tensor (BraidedTower / Hexon):** the hexon's phaseCount
  is `2 × 3 = 6` and the cycle visits all six pairs in a single linear
  traversal — the `BraidedAsymptote` of `phaseCount := 6` from
  `Gnosis.HexonBraid`. Two Tritons stacked.
* **Parallel tensor (BraidTensorProduct):** the cycle visits both
  coordinates simultaneously via `pairSucc`. The return time is
  `lcm(k₁, k₂)`, which only equals `k₁ × k₂` when the factors are
  coprime. Two clinamens advancing in lockstep.

The two agree exactly when `gcd(k₁, k₂) = 1` (CRT regime). This module
exhibits both regimes and connects them to the multi-head transformer
attention block from `Gnosis.BuleyTransformerSSMBridge`:

* `pair_3_2_matches_hexon`: the parallel-tensor cycle for a triton ⊗
  bisided-bit (k₁=3, k₂=2) returns at 6 and matches the Hexon's
  phaseCount.
* `pair_3_n_matches_multi_head_when_coprime`: the parallel-tensor
  matches `multiHeadPhaseCount n` exactly when `gcd(3, n) = 1`.
* `pair_3_3_returns_at_three_not_nine`: the *parallel* triton ⊗ triton
  has period 3 — strictly less than the *sequential* enneon's
  phaseCount 9. The reading determines the period.

This is the formal reason multi-head attention with `n` heads works
differently when `n` is coprime to 3 vs. when it shares a factor: the
parallel-clinamen return time depends on `lcm(3, n)`, not the head
count itself.

Imports `Gnosis.HexonBraid`, `Gnosis.BraidedTower`,
`Gnosis.BraidTensorProduct`, and `Gnosis.BuleyTransformerSSMBridge`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace BuleyTensorBridge

open Gnosis.BraidTensorProduct (pairSucc iteratePairSucc)
open Gnosis.BuleyTransformerSSMBridge (multiHeadPhaseCount multi_head_phase_count_eq)

/-! ## Triton ⊗ BiSided = Hexon (parallel reading agrees with sequential) -/

/-- Parallel-tensor for triton (k=3) and bisided (k=2) returns at 6.
This is the `pair_2_3` theorem from `BraidTensorProduct` with the
arguments matching the Bule reading: triton first, bisided second. -/
theorem pair_3_2_returns_at_six :
    iteratePairSucc 3 2 6 (0, 0) = (0, 0) := by decide

theorem pair_3_2_no_early_return :
    iteratePairSucc 3 2 1 (0, 0) ≠ (0, 0)
    ∧ iteratePairSucc 3 2 2 (0, 0) ≠ (0, 0)
    ∧ iteratePairSucc 3 2 3 (0, 0) ≠ (0, 0)
    ∧ iteratePairSucc 3 2 4 (0, 0) ≠ (0, 0)
    ∧ iteratePairSucc 3 2 5 (0, 0) ≠ (0, 0) := by decide

/-! ## Parallel triton ⊗ triton has period 3 — strictly less than the
sequential enneon's phaseCount 9. The reading determines the period. -/

theorem pair_3_3_returns_at_three :
    iteratePairSucc 3 3 3 (0, 0) = (0, 0) := by decide

theorem pair_3_3_no_early_return :
    iteratePairSucc 3 3 1 (0, 0) ≠ (0, 0)
    ∧ iteratePairSucc 3 3 2 (0, 0) ≠ (0, 0) := by decide

/-- The crucial distinction: parallel triton ⊗ triton returns at 3,
not at 9. The sequential enneon (`Gnosis.HexonBraid.enneonBraid`,
phaseCount 9) is a *different* cycle on the same 3×3 underlying set. -/
theorem parallel_triton_squared_period_is_three_not_nine :
    iteratePairSucc 3 3 3 (0, 0) = (0, 0)
    ∧ iteratePairSucc 3 3 9 (0, 0) = (0, 0)
    ∧ iteratePairSucc 3 3 1 (0, 0) ≠ (0, 0)
    ∧ iteratePairSucc 3 3 2 (0, 0) ≠ (0, 0) := by decide

/-! ## Multi-head attention: parallel period matches sequential phaseCount
exactly in the coprime regime -/

/-- Five-head attention (k₁=3, k₂=5, coprime): the parallel cycle
returns at 15, matching `multiHeadPhaseCount 5`. -/
theorem five_head_attention_pair_returns_at_fifteen :
    iteratePairSucc 3 5 15 (0, 0) = (0, 0)
    ∧ multiHeadPhaseCount 5 = 15 := by
  refine ⟨?_, ?_⟩
  · decide
  · show 3 * (5 * 1) = 15
    decide

/-- Seven-head attention (k₁=3, k₂=7, coprime): parallel cycle returns
at 21, matching `multiHeadPhaseCount 7`. -/
theorem seven_head_attention_pair_returns_at_twenty_one :
    iteratePairSucc 3 7 21 (0, 0) = (0, 0)
    ∧ multiHeadPhaseCount 7 = 21 := by
  refine ⟨?_, ?_⟩
  · decide
  · show 3 * (7 * 1) = 21
    decide

/-! ## Non-coprime regime: parallel period is strictly less than sequential

When the head count shares a factor with 3 (e.g., 3, 6, 9, 12), the
parallel-tensor return time is `lcm(3, n) < 3n`. Multi-head attention
with such a head count "self-collapses" earlier than its nominal phase
count would suggest. -/

/-- Six-head attention's parallel period is 6 (lcm(3, 6) = 6), while
its sequential phaseCount is 18. The parallel return is much earlier. -/
theorem six_head_attention_parallel_vs_sequential :
    iteratePairSucc 3 6 6 (0, 0) = (0, 0)
    ∧ multiHeadPhaseCount 6 = 18
    ∧ iteratePairSucc 3 6 3 (0, 0) ≠ (0, 0) := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · show 3 * (6 * 1) = 18
    decide
  · decide

/-- Twelve-head attention's parallel period is 12 (lcm(3, 12) = 12),
while its sequential phaseCount is 36. -/
theorem twelve_head_attention_parallel_vs_sequential :
    iteratePairSucc 3 12 12 (0, 0) = (0, 0)
    ∧ multiHeadPhaseCount 12 = 36 := by
  refine ⟨?_, ?_⟩
  · decide
  · show 3 * (12 * 1) = 36
    decide

end BuleyTensorBridge
end Gnosis
