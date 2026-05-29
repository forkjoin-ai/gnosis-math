import Init

/-!
# GnosisMathPrelude

Central repository for core mathematical truths, basic arithmetic identities,
and structural successors used across the Gnosis codebase.

Consolidates definitions from:
- `MeshArithmeticOrigin.lean` (gnosisSucc, gnosisAdd)
- `FoilZeroDragCompatibility.lean` (identity lifts)
- `MoonshotRecursiveTruthDeficit.lean` (truth bounds)
-/

namespace GnosisMath

/-- Power on Nat (Init-only). -/
def powNat (base : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => base * powNat base n

theorem powNat_succ (base n : Nat) : powNat base (n + 1) = base * powNat base n := rfl

theorem powNat_one (base : Nat) : powNat base 1 = base := by
  unfold powNat
  simp [powNat]

-- ═══════════════════════════════════════════════════════════════════════
-- (1) Successors and Basic Addition
-- ═══════════════════════════════════════════════════════════════════════

/-- The "Gnosis Successor" (from MeshArithmeticOrigin). -/
def gnosisSucc (n : Nat) : Nat := n + 1

/-- Addition defined as repeated application of gnosisSucc. -/
def gnosisAdd (n m : Nat) : Nat :=
  match m with
  | 0 => n
  | k + 1 => gnosisSucc (gnosisAdd n k)

theorem gnosisAdd_is_add (n m : Nat) : gnosisAdd n m = n + m := by
  induction m with
  | zero => rfl
  | succ k ih =>
      show gnosisSucc (gnosisAdd n k) = n + (k + 1)
      show (gnosisAdd n k) + 1 = n + (k + 1)
      exact congrArg (· + 1) ih

-- ═══════════════════════════════════════════════════════════════════════
-- (2) Identity Lifts (from FoilZeroDragCompatibility)
-- ═══════════════════════════════════════════════════════════════════════

/-- The ordinary swerve lift: advance one phase. -/
def plusOneLift (n : Nat) : Nat := n + 1

/-- Multiplicative identity lift. -/
def timesOneLift (n : Nat) : Nat := n * 1

/-- Exponential identity lift. -/
def powOneLift (n : Nat) : Nat := n ^ 1

theorem timesOneLift_id (n : Nat) : timesOneLift n = n := Nat.mul_one n
theorem powOneLift_id (n : Nat) : powOneLift n = n := Nat.pow_one n

-- ═══════════════════════════════════════════════════════════════════════
-- (3) Truth Deficits and Bounds
-- ═══════════════════════════════════════════════════════════════════════

def truthDeficit (depth : Nat) : Nat := depth
def truthBounds (n : Nat) : Nat := n + 1

theorem truthDeficit_bounded (d : Nat) : truthDeficit d < truthBounds d :=
  Nat.lt_succ_self d

end GnosisMath