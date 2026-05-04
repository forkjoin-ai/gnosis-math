import Init

/-!
# Fibonacci weights (Init-only)

Same indexing as [`ZeckendorfFST.F`](../ZeckendorfFST.lean) (`F 0 = F 1 = 1`, recurrence on `n+2`),
kept here for **MathSandbox** / `GnosisMath.Basic` consumers without importing the Mathlib-backed
`ZeckendorfFST` module.
-/

namespace GnosisMath

/-- Fibonacci tower for Zeckendorf-style weights: `1, 1, 2, 3, 5, 8, …`. -/
def fibZ : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => fibZ (n + 1) + fibZ n

theorem fibZ_zero : fibZ 0 = 1 := rfl

theorem fibZ_one : fibZ 1 = 1 := rfl

theorem fibZ_two : fibZ 2 = 2 := rfl

theorem fibZ_three : fibZ 3 = 3 := rfl

theorem fibZ_four : fibZ 4 = 5 := rfl

theorem fibZ_five : fibZ 5 = 8 := rfl

theorem fibZ_six : fibZ 6 = 13 := rfl

theorem fibZ_seven : fibZ 7 = 21 := rfl

theorem fibZ_eight : fibZ 8 = 34 := rfl

/-- Standard recurrence (unfolded one step). -/
theorem fibZ_succ_succ (n : Nat) : fibZ (n + 2) = fibZ (n + 1) + fibZ n := rfl

/-- Marker that the Fibonacci slice is linked. -/
theorem gnosisMathFibonacciLinked (n : Nat) : n + 0 = n := by
  simp

end GnosisMath
