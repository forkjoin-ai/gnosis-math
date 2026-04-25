import Init

/-!
# Independent Sets on the Cycle Graph `C_n` Are Counted by the Lucas Numbers

The **cycle graph** `C_n` has vertex set `{0, 1, ..., n-1}` with edges
`{(i, (i+1) mod n) : i = 0, ..., n-1}`. An **independent set** is a subset
of the vertex set no two of whose elements are adjacent. The identity

    |IS(C_n)| = L_n

witnesses a bijection between independent sets of the cycle and the Lucas
sequence `L_0 = 2, L_1 = 1, L_{k+1} = L_k + L_{k-1}`. The companion identity
for the **path graph** `P_n` on `n` vertices reads

    |IS(P_n)| = F_{n+2}

with the Fibonacci sequence `F_0 = 0, F_1 = 1, F_{k+1} = F_k + F_{k-1}`.
Cyclic closure --- the single extra edge joining `n-1` back to `0` ---
shifts the Fibonacci count on the path to the Lucas count on the cycle.

This module computes `|IS(C_n)|` and `|IS(P_n)|` directly by enumerating
all `2^n` bit-indicator subsets of `{0, ..., n-1}` and counting those that
pass the independence check, then witnesses equality with the corresponding
Lucas or Fibonacci value at small `n`.

## What is witnessed

- Lucas identities `L_0 = 2`, `L_1 = 1`, `L_7 = 29`.
- Fibonacci identities `F_0 = 0`, `F_1 = 1`, `F_7 = 13`.
- Cycle independent-set counts `|IS(C_n)| = L_n` for `n = 3, 4, 5, 6, 7`.
- Path independent-set counts `|IS(P_n)| = F_{n+2}` for `n = 3, 4, 5`.

## What is *not* proved

This module witnesses the identities at specific small `n` by kernel
reduction, not as a general theorem for all `n`. The definitions
`lucas` and `fib` are direct structural recursions on `Nat`; no closed
form, Binet expression, transfer-matrix argument, or generating-function
derivation appears here. The enumeration `allSubsets` brute-forces `2^n`
bit-vectors and has no connection to a transfer-matrix count. The
general bijection between independent sets of `C_n` and Lucas numbers
(and of `P_n` and Fibonacci numbers) is assumed as background, and
only checked at the listed depths.

No `sorry`, no new `axiom`, `Init`-only. Each instance closes by
kernel `decide`.
-/

namespace Gnosis
namespace IndependentSetCycleCnLucas

/-! ## Lucas and Fibonacci sequences -/

/-- Lucas numbers with the standard convention `L_0 = 2, L_1 = 1`. -/
def lucas : Nat → Nat
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-- Fibonacci numbers with the standard convention `F_0 = 0, F_1 = 1`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib (n + 1) + fib n

/-! ## Lucas and Fibonacci sanity checks -/

/-- `L_0 = 2`. -/
theorem lucas_0 : lucas 0 = 2 := by decide

/-- `L_1 = 1`. -/
theorem lucas_1 : lucas 1 = 1 := by decide

/-- `L_7 = 29`. -/
theorem lucas_7 : lucas 7 = 29 := by decide

/-- `F_0 = 0`. -/
theorem fib_0 : fib 0 = 0 := by decide

/-- `F_1 = 1`. -/
theorem fib_1 : fib 1 = 1 := by decide

/-- `F_7 = 13`. -/
theorem fib_7 : fib 7 = 13 := by decide

/-! ## Bit-indicator enumeration of subsets

A subset of `{0, ..., n-1}` is encoded as a `List Bool` of length `n`,
with position `i` carrying `true` iff vertex `i` is in the subset. The
function `allSubsets n` enumerates all `2^n` such bit-vectors. -/

/-- Prepend both `false` and `true` to each list in the input, doubling
the length of the list-of-lists. One step of the power-set enumeration. -/
def extendSubsets : List (List Bool) → List (List Bool)
  | [] => []
  | xs :: rest => (false :: xs) :: (true :: xs) :: extendSubsets rest

/-- All `2^n` bit-vectors of length `n`, in lexicographic order with
`false < true` at each position. -/
def allSubsets : Nat → List (List Bool)
  | 0 => [[]]
  | (n + 1) => extendSubsets (allSubsets n)

/-! ## Independence checks -/

/-- On the path graph `P_n` the independence constraint is: no two
consecutive positions both carry `true`. -/
def isIndependentPath : List Bool → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    if a && b then false else isIndependentPath (b :: rest)

/-- Wrap-around check: given the original first bit and the current tail,
assert that the final bit of the tail is not `true` when the original
first bit was also `true`. -/
def noWrapClash : Bool → List Bool → Bool
  | _,     []      => true
  | first, [last]  => !(first && last)
  | first, _ :: rest => noWrapClash first rest

/-- On the cycle graph `C_n` the independence constraint is the path
constraint *plus* the wrap-around edge `(n-1, 0)`. For `n ≤ 1` the
wrap-around edge is absent or loops on a single vertex and the path
check suffices. -/
def isIndependentCycle : List Bool → Bool
  | [] => true
  | [_] => true
  | (first :: rest) =>
    isIndependentPath (first :: rest) && noWrapClash first rest

/-! ## Counting independent sets -/

/-- Count the elements of a `List (List Bool)` passing a `Bool` predicate. -/
def countPassing (p : List Bool → Bool) : List (List Bool) → Nat
  | [] => 0
  | xs :: rest => (if p xs then 1 else 0) + countPassing p rest

/-- `|IS(P_n)|` by brute-force enumeration of bit-vectors of length `n`. -/
def countIndependentPath (n : Nat) : Nat :=
  countPassing isIndependentPath (allSubsets n)

/-- `|IS(C_n)|` by brute-force enumeration of bit-vectors of length `n`. -/
def countIndependentCycle (n : Nat) : Nat :=
  countPassing isIndependentCycle (allSubsets n)

/-! ## Cycle identities: `|IS(C_n)| = L_n` -/

/-- `|IS(C_3)| = 4 = L_3`. -/
theorem count_IS_C3_eq_L3 : countIndependentCycle 3 = lucas 3 := by decide

/-- `|IS(C_4)| = 7 = L_4`. -/
theorem count_IS_C4_eq_L4 : countIndependentCycle 4 = lucas 4 := by decide

/-- `|IS(C_5)| = 11 = L_5`. -/
theorem count_IS_C5_eq_L5 : countIndependentCycle 5 = lucas 5 := by decide

/-- `|IS(C_6)| = 18 = L_6`. -/
theorem count_IS_C6_eq_L6 : countIndependentCycle 6 = lucas 6 := by decide

-- The `n = 7` enumeration unfolds `2^7 = 128` bit-vectors, which
-- overflows the default recursion depth for kernel `decide`. We raise
-- `maxRecDepth` locally for this instance only.
-- `|IS(C_7)| = 29 = L_7`.
set_option maxRecDepth 4096 in
theorem count_IS_C7_eq_L7 : countIndependentCycle 7 = lucas 7 := by decide

/-! ## Path identities: `|IS(P_n)| = F_{n+2}` -/

/-- `|IS(P_3)| = 5 = F_5`. -/
theorem count_IS_P3_eq_F5 : countIndependentPath 3 = fib 5 := by decide

/-- `|IS(P_4)| = 8 = F_6`. -/
theorem count_IS_P4_eq_F6 : countIndependentPath 4 = fib 6 := by decide

/-- `|IS(P_5)| = 13 = F_7`. -/
theorem count_IS_P5_eq_F7 : countIndependentPath 5 = fib 7 := by decide

end IndependentSetCycleCnLucas
end Gnosis
