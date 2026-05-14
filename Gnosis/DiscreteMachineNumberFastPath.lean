import Gnosis.DiscreteMachineNumberApproximation

/-!
# Gnosis.DiscreteMachineNumberFastPath

Closed Boolean skip paths for finite machine-number certification.  A bracket
can skip further approximation work once it lies strictly inside a candidate
machine cell's midpoint interval.
-/

namespace Gnosis
namespace DiscreteMachineNumberFastPath

open DiscreteContinuumConstants
open DiscreteContinuumConstantRefinement
open DiscreteMachineNumberApproximation

/-- The finite check that a rational bracket lies inside a machine cell's
midpoint interval:

`lowerMidpoint < bracket.lower` and `bracket.upper < upperMidpoint`.

Everything is cross-multiplied over `Nat`; no rational or real arithmetic is
introduced. -/
def bracketInsideMachineCell
    (b : ScaledBracket)
    (c : NearestMachineCertificate) : Bool :=
  decide (c.lowerMidpointTwice * b.lower.denominator <
      2 * c.cell.denominator * b.lower.numerator)
    && decide (2 * c.cell.denominator * b.upper.numerator <
      c.upperMidpointTwice * b.upper.denominator)

/-- Skip result for a machine approximation request. -/
structure MachineFastPath where
  certificate : NearestMachineCertificate
  bracket : ScaledBracket
  forced : Bool
  deriving Repr

def machineFastPath
    (b : ScaledBracket)
    (c : NearestMachineCertificate) : MachineFastPath :=
  { certificate := c, bracket := b, forced := bracketInsideMachineCell b c }

/-! ## Positive sanity checks: exact candidate cells force themselves -/

def exactBinary64PiCellBracket : ScaledBracket :=
  { lower :=
      { numerator := binary64PiNearest.cell.significand
      , denominator := binary64PiNearest.cell.denominator
      , denominatorPositive := by discrete_modulus }
  , upper :=
      { numerator := binary64PiNearest.cell.significand
      , denominator := binary64PiNearest.cell.denominator
      , denominatorPositive := by discrete_modulus } }

def exactBinary32PiCellBracket : ScaledBracket :=
  { lower :=
      { numerator := binary32PiNearest.cell.significand
      , denominator := binary32PiNearest.cell.denominator
      , denominatorPositive := by discrete_modulus }
  , upper :=
      { numerator := binary32PiNearest.cell.significand
      , denominator := binary32PiNearest.cell.denominator
      , denominatorPositive := by discrete_modulus } }

theorem exact_cell_brackets_force_fast_paths :
    bracketInsideMachineCell exactBinary64PiCellBracket binary64PiNearest = true
    ∧ bracketInsideMachineCell exactBinary32PiCellBracket binary32PiNearest = true := by
  discrete_modulus

/-! ## Current frontier status: useful skips versus still-wide brackets -/

theorem current_binary32_brackets_do_not_yet_force_machine_cells :
    bracketInsideMachineCell piArchimedeanBracket binary32PiNearest = false
    ∧ bracketInsideMachineCell eBracketTenTerms binary32ENearest = false
    ∧ bracketInsideMachineCell sqrtTwoPellBracket binary32SqrtTwoNearest = false
    ∧ bracketInsideMachineCell phiFibonacciBracket binary32PhiNearest = false := by
  discrete_modulus

theorem current_binary64_brackets_do_not_yet_force_machine_cells :
    bracketInsideMachineCell piArchimedeanBracket binary64PiNearest = false
    ∧ bracketInsideMachineCell eBracketTenTerms binary64ENearest = false
    ∧ bracketInsideMachineCell sqrtTwoPellBracket binary64SqrtTwoNearest = false
    ∧ bracketInsideMachineCell phiFibonacciBracket binary64PhiNearest = false := by
  discrete_modulus

def piBinary32FastPath : MachineFastPath :=
  machineFastPath piArchimedeanBracket binary32PiNearest

def piBinary64FastPath : MachineFastPath :=
  machineFastPath piArchimedeanBracket binary64PiNearest

theorem pi_fast_paths_record_frontier_status :
    piBinary32FastPath.forced = false
    ∧ piBinary64FastPath.forced = false := by
  discrete_modulus

/-! ## Tight machine-target brackets flip the skip paths -/

theorem machine_target_brackets_force_binary32_cells :
    bracketInsideMachineCell
        DiscreteContinuumConstantRefinement.piMachineTargetBracket binary32PiNearest = true
    ∧ bracketInsideMachineCell
        DiscreteContinuumConstantRefinement.eMachineTargetBracket binary32ENearest = true
    ∧ bracketInsideMachineCell
        DiscreteContinuumConstantRefinement.sqrtTwoMachineTargetBracket
        binary32SqrtTwoNearest = true
    ∧ bracketInsideMachineCell
        DiscreteContinuumConstantRefinement.phiMachineTargetBracket binary32PhiNearest = true := by
  discrete_modulus

theorem machine_target_brackets_force_binary64_cells :
    bracketInsideMachineCell
        DiscreteContinuumConstantRefinement.piMachineTargetBracket binary64PiNearest = true
    ∧ bracketInsideMachineCell
        DiscreteContinuumConstantRefinement.eMachineTargetBracket binary64ENearest = true
    ∧ bracketInsideMachineCell
        DiscreteContinuumConstantRefinement.sqrtTwoMachineTargetBracket
        binary64SqrtTwoNearest = true
    ∧ bracketInsideMachineCell
        DiscreteContinuumConstantRefinement.phiMachineTargetBracket binary64PhiNearest = true := by
  discrete_modulus

end DiscreteMachineNumberFastPath
end Gnosis
