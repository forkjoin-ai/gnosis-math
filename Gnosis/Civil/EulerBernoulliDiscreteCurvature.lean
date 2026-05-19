import Init

/-
  EulerBernoulliDiscreteCurvature.lean
  ====================================

  Formalizes the discrete Euler-Bernoulli relationship for linear elastic
  beam elements. In a discrete grid of spacing Δx = 1, the curvature κ
  at node i is defined by the second-order central difference of the transverse displacement y.

  The bending moment M is the product of the flexural rigidity EI and
  the curvature κ. This module proves the stability witness that a linear
  displacement field (zero curvature) results in zero internal moment.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

/-- Flexural rigidity (EI) as a non-negative scalar. -/
def FlexuralRigidity := Nat

/-- 
  Discrete Curvature (κ) at node i+1 using central difference:
  κ[i+1] = y[i+2] - 2*y[i+1] + y[i]
-/
def Curvature (y : Nat → Int) (i : Nat) : Int :=
  y (i + 2) - 2 * y (i + 1) + y i

/-- 
  Bending Moment (M) at node i+1:
  M[i+1] = EI * κ[i+1]
-/
def BendingMoment (ei : FlexuralRigidity) (y : Nat → Int) (i : Nat) : Int :=
  (Int.ofNat ei) * Curvature y i

/-- 
  Theorem: Linear Displacement Yields Zero Moment.
  If the displacement field is linear (y[i] = m*i + c), then the internal
  bending moment is zero at all nodes.
-/
theorem linear_displacement_yields_zero_moment
  (m c : Int)
  (ei : FlexuralRigidity)
  (y : Nat → Int)
  (h_linear : ∀ i, y i = m * (i : Int) + c) :
  ∀ i, BendingMoment ei y i = 0 := by
  intro i
  unfold BendingMoment
  calc (Int.ofNat ei) * Curvature y i
    = (Int.ofNat ei) * (y (i + 2) - 2 * y (i + 1) + y i) := rfl
  _ = (Int.ofNat ei) * ((m * ↑(i + 2) + c) - 2 * (m * ↑(i + 1) + c) + (m * ↑i + c)) := by
      rw [h_linear, h_linear, h_linear]
  _ = (Int.ofNat ei) * 0 := by
      congr
      /-
        MASTER LIST OF FAILURES (Persistence Record):
        1. omega Ban: Forbidden by Rustic Church doctrine.
        2. maxRecDepth: Reached by repeat rw [Int.add_left_neg] on large additive trees.
        3. ac_rfl Negation Limit: Fails to simplify x + -x to 0 for open variables.
        4. Int.add_left_comm Brittleness: Fails if the pattern is nested or hidden.
        5. generalize + ac_rfl: Fails due to negation bottleneck in kernel reduction.
        6. Int.neg_add Essentiality: Required to flatten -(a+b) sums for term accessibility.
        7. Int.mul_add Depth: Requires multiple targeted passes for nested sums.
        8. Constant Expansion: 2 * x must be expanded to x + x via Int.two_mul.
        9. Casting Gaps: Int.natCast_add and Int.ofNat_one/two required for Nat/Int bridge.
        10. calc Step Reduction: Fails if atoms are shifted without alignment.
        11. match ... ac_rfl: Fails because kernel does not reduce -v + v during AC.
        12. Int.mul_add 2 Pattern Match: Fails if tree structure is inconsistent.
        13. show Normalization: Brittle due to subtle definitional literal differences.
        14. Manual Cancellation Chain: Failed due to associative mismatch.
        15. Target Pattern Mismatch (Already flattened): Attempting Int.neg_add on -A + -B.
        16. Association Mismatch in Bubble-up: Bubbling fails if right-hand side isn't parenthesized.
        17. Int.add_left_neg Mismatch: Fails to match mi + mi + (-mi + -mi) due to nesting.
        18. Int.neg_add Match failure: Failed to match -(m*↑i) + -(m*↑i).
        19. Nested Distribution failure: rw [Int.neg_add] failed on already split sums.
        20. Int.mul_add expansion order: Failed to expand when intermediate atoms were already separated.
        21. Associative Pattern mismatch: rw [Int.add_left_comm] failed due to different internal grouping.
        
        SOLUTION: Completely bypass tree-matching by creating an explicit difference-of-increments
        helper lemma that isolates the algebra into purely linear, structurally guaranteed steps.
      -/
      have h_A_1 : m * ↑(i + 1) + c = (m * ↑i + c) + m := by
        rw [show (↑(i + 1) : Int) = ↑i + 1 from rfl]
        rw [Int.mul_add]
        repeat rw [Int.mul_one]
        rw [Int.add_assoc, Int.add_comm m c, ← Int.add_assoc]

      have h_A_2 : m * ↑(i + 2) + c = (m * ↑i + c) + m + m := by
        rw [show (↑(i + 2) : Int) = ↑i + 1 + 1 from rfl]
        rw [Int.mul_add, Int.mul_add]
        repeat rw [Int.mul_one]
        rw [Int.add_assoc (m * ↑i + m) m c]
        rw [Int.add_comm m c]
        rw [← Int.add_assoc (m * ↑i + m) c m]
        rw [Int.add_assoc (m * ↑i) m c]
        rw [Int.add_comm m c]
        rw [← Int.add_assoc (m * ↑i) c m]

      have h_reduce (A M : Int) : (A + M + M) - 2 * (A + M) + A = 0 := by
        calc (A + M + M) - 2 * (A + M) + A
          = (A + M + M) - ((A + M) + (A + M)) + A := by rw [Int.two_mul]
        _ = (A + M + M) + -((A + M) + (A + M)) + A := rfl
        _ = (A + M + M) + (-(A + M) + -(A + M)) + A := by rw [Int.neg_add]
        _ = (A + M) + M + -(A + M) + -(A + M) + A := by rw [← Int.add_assoc (A + M + M) (-(A + M)) (-(A + M))]
        _ = (A + M) + (M + -(A + M)) + -(A + M) + A := by rw [Int.add_assoc (A + M) M (-(A + M))]
        _ = (A + M) + (-(A + M) + M) + -(A + M) + A := by rw [Int.add_comm M (-(A + M))]
        _ = (A + M) + -(A + M) + M + -(A + M) + A := by rw [← Int.add_assoc (A + M) (-(A + M)) M]
        _ = 0 + M + -(A + M) + A := by rw [Int.add_right_neg (A + M)]
        _ = M + -(A + M) + A := by rw [Int.zero_add]
        _ = M + (-A + -M) + A := by rw [Int.neg_add]
        _ = M + -A + -M + A := by rw [← Int.add_assoc M (-A) (-M)]
        _ = M + (-A + -M) + A := by rw [Int.add_assoc M (-A) (-M)]
        _ = M + (-M + -A) + A := by rw [Int.add_comm (-A) (-M)]
        _ = M + -M + -A + A := by rw [← Int.add_assoc M (-M) (-A)]
        _ = 0 + -A + A := by rw [Int.add_right_neg M]
        _ = -A + A := by rw [Int.zero_add]
        _ = 0 := by rw [Int.add_left_neg A]

      rw [h_A_1, h_A_2]
      exact h_reduce (m * ↑i + c) m
  _ = 0 := Int.mul_zero _

end Gnosis.Civil
