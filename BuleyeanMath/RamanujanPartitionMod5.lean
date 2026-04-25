import Init

/-!
# Ramanujan's Partition Congruence `p(5n + 4) ≡ 0 (mod 5)` on small instances

The unrestricted partition function `p(n)` counts the number of ways to
write `n` as an unordered sum of positive integers. Ramanujan observed the
congruence

    p(5n + 4) ≡ 0 (mod 5)

for every natural number `n`. This module witnesses the congruence on a
finite list of small `n` by direct computation.

The computation uses the nested max-part recurrence: let
`partitionsMaxPart n k` be the number of partitions of `n` using only
parts bounded by `k`. Then

    partitionsMaxPart 0       k       = 1
    partitionsMaxPart (n+1)   0       = 0
    partitionsMaxPart n       (k+1)   = partitionsMaxPart n k
                                      + partitionsMaxPart (n - (k+1)) (k+1)
                                        when n ≥ k+1

and the second summand is dropped when `n < k+1` because you cannot use a
part larger than what remains. Setting `p n = partitionsMaxPart n n`
recovers the unrestricted partition function.

Structural recursion on the pair `(k, n)` is arranged through a fuel
parameter equal to `n + k`; the fuel strictly decreases in both the
"omit the largest part" branch (where `k` drops by one) and the
"use the largest part" branch (where `n` drops by `k+1 ≥ 1`), so the
total `n + k` drops by at least one in each recursive call. This keeps
the definition reducible by kernel computation and hence by `decide`.

What is witnessed:
* `p 0 = 1`, `p 4 = 5`, `p 9 = 30`, `p 14 = 135`.
* `(p (5 * n + 4)) % 5 = 0` for `n = 0, 1, 2, 3, 4`
  (i.e. `p 4`, `p 9`, `p 14`, `p 19 = 490`, `p 24 = 1575`, each divisible by 5).

What is *not* proved:
* Ramanujan's theorem in general (the congruence for all `n ≥ 0`).
* Any connection to the generating-function identity
  `Σ p(5n+4) qⁿ = 5 · ∏(1-q⁵ⁿ)⁵ / ∏(1-qⁿ)⁶` or to modular forms.
* Euler's pentagonal number recurrence or any partition-theoretic
  machinery beyond the max-part bookkeeping.

These are numerical witnesses that the general theorem implies. The file
stops at `n = 4` to match the target set in the task spec; the `decide`
budget remains well under the 2-second ceiling on this range.

No `sorry`, no new `axiom`, no `native_decide`; `Init`-only.
-/

namespace BuleyeanMath
namespace RamanujanPartitionMod5

/-! ## Max-part partition recurrence via fuel -/

/-- Fuel-driven worker for the max-part partition count.

`partitionsAux fuel n k` computes `partitionsMaxPart n k` provided
`fuel ≥ n + k`. The fuel strictly decreases in every recursive call, so
the definition is structurally terminating on `fuel`. -/
def partitionsAux : Nat → Nat → Nat → Nat
  | 0,            _,     _     => 0  -- fuel exhausted; unused when fuel ≥ n+k
  | _ + 1,        0,     _     => 1  -- partitions of zero: empty partition
  | _ + 1,        _ + 1, 0     => 0  -- positive `n` with max part `0`
  | fuel + 1,     n + 1, k + 1 =>
      let without := partitionsAux fuel (n + 1) k
      if n + 1 < k + 1 then without
      else without + partitionsAux fuel (n + 1 - (k + 1)) (k + 1)

/-- `partitionsMaxPart n k` counts partitions of `n` using only parts `≤ k`. -/
def partitionsMaxPart (n k : Nat) : Nat :=
  partitionsAux (n + k + 1) n k

/-- The unrestricted partition function `p(n)`. -/
def p (n : Nat) : Nat := partitionsMaxPart n n

/-! ## Sanity checks on small values -/

/-- `p 0 = 1`: the empty partition of zero. -/
theorem p_zero : p 0 = 1 := by decide

/-- `p 1 = 1`: the partition `1`. -/
theorem p_one : p 1 = 1 := by decide

/-- `p 2 = 2`: the partitions `2` and `1+1`. -/
theorem p_two : p 2 = 2 := by decide

/-- `p 3 = 3`: the partitions `3`, `2+1`, `1+1+1`. -/
theorem p_three : p 3 = 3 := by decide

/-- `p 4 = 5`: the first Ramanujan target value. -/
theorem p_four : p 4 = 5 := by decide

/-- `p 9 = 30`: the second Ramanujan target value. -/
theorem p_nine : p 9 = 30 := by decide

/-- `p 14 = 135`: the third Ramanujan target value. -/
theorem p_fourteen : p 14 = 135 := by decide

/-! ## Ramanujan congruence instances `p(5n + 4) ≡ 0 (mod 5)` -/

/-- `n = 0`: `p 4 = 5`, and `5 % 5 = 0`. -/
theorem ramanujan_mod5_zero : p (5 * 0 + 4) % 5 = 0 := by decide

/-- `n = 1`: `p 9 = 30`, and `30 % 5 = 0`. -/
theorem ramanujan_mod5_one : p (5 * 1 + 4) % 5 = 0 := by decide

/-- `n = 2`: `p 14 = 135`, and `135 % 5 = 0`. -/
theorem ramanujan_mod5_two : p (5 * 2 + 4) % 5 = 0 := by decide

/-- `n = 3`: `p 19 = 490`, and `490 % 5 = 0`. -/
theorem ramanujan_mod5_three : p (5 * 3 + 4) % 5 = 0 := by decide

/-- `n = 4`: `p 24 = 1575`, and `1575 % 5 = 0`. -/
theorem ramanujan_mod5_four : p (5 * 4 + 4) % 5 = 0 := by decide

end RamanujanPartitionMod5
end BuleyeanMath
