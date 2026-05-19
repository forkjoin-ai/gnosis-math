import Init

/-
  FickSecondLaw.lean
  ==================

  Formalizes a discrete interpretation of Fick's Second Law:
  ∂c/∂t = D ∂²c/∂x²

  In Gnosis, we model the rate of concentration change (Accumulation)
  as a witness of the spatial curvature of the concentration field.
  Stability is reached when the spatial curvature is zero (Linear profile).

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Materials

/-- 
  Concentration Profile across discrete nodes.
-/
def ConcentrationProfile := Nat → Int

/-- 
  Spatial Curvature (Second difference) at node i+1.
-/
def SpatialCurvature (c : ConcentrationProfile) (i : Nat) : Int :=
  c (i + 2) - 2 * c (i + 1) + c i

/-- 
  Accumulation Witness:
  The change in concentration per unit time.
-/
def Accumulation (d : Int) (c : ConcentrationProfile) (i : Nat) : Int :=
  d * SpatialCurvature c i

/-- 
  Theorem: Steady State Witness.
  In a linear concentration profile (c_i = m*i + k), the accumulation
  witness is zero everywhere (Steady state).
-/
theorem steady_state_linear_profile (d m k : Int) (c : ConcentrationProfile)
  (h_linear : ∀ i, c i = m * (i : Int) + k) :
  ∀ i, Accumulation d c i = 0 := by
  intro i
  unfold Accumulation
  calc d * SpatialCurvature c i
    = d * (c (i + 2) - 2 * c (i + 1) + c i) := rfl
  _ = d * ((m * ↑(i + 2) + k) - 2 * (m * ↑(i + 1) + k) + (m * ↑i + k)) := by
      rw [h_linear, h_linear, h_linear]
  _ = d * 0 := by
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
      have h_A_1 : m * ↑(i + 1) + k = (m * ↑i + k) + m := by
        rw [show (↑(i + 1) : Int) = ↑i + 1 from rfl]
        rw [Int.mul_add]
        repeat rw [Int.mul_one]
        rw [Int.add_assoc, Int.add_comm m k, ← Int.add_assoc]

      have h_A_2 : m * ↑(i + 2) + k = (m * ↑i + k) + m + m := by
        rw [show (↑(i + 2) : Int) = ↑i + 1 + 1 from rfl]
        rw [Int.mul_add, Int.mul_add]
        repeat rw [Int.mul_one]
        rw [Int.add_assoc (m * ↑i + m) m k]
        rw [Int.add_comm m k]
        rw [← Int.add_assoc (m * ↑i + m) k m]
        rw [Int.add_assoc (m * ↑i) m k]
        rw [Int.add_comm m k]
        rw [← Int.add_assoc (m * ↑i) k m]

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
      exact h_reduce (m * ↑i + k) m
  _ = 0 := Int.mul_zero _

end Gnosis.Materials
