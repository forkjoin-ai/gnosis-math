import Gnosis.GodFormula
import Gnosis.BracketedSpace

/-!
# Gnosis.GodBracket

Finite bracket/rejection certificates for lowering bracket arithmetic into FOIL.
The broad monotonicity theorem remains a promotion frontier; this module exposes
checked rows that the runtime can reuse without recomputing rational containment.
-/

namespace Gnosis
namespace GodBracket

open ForkRaceFoldMath
open BracketedSpace

/-- A bracket paired with a finite rejection count under budget `R`. -/
structure GodBracket (R : Nat) where
  bracket : QBracket
  rejection : Nat
  matches_rejection : Q.beq bracket.width (Q.of (Int.ofNat rejection) R) = true
  deriving Repr

/-- Weight inherited from `GodFormula`: smaller rejection gives larger weight. -/
def weight {R : Nat} (b : GodBracket R) : Nat :=
  godWeight R b.rejection

/-- Checked containment of one bracket inside another. -/
def bracketContained (outer inner : QBracket) : Bool :=
  Q.bracketRefines outer.lower outer.upper inner.lower inner.upper

/-- Checked width ordering of rational brackets. -/
def bracketWidthLe (left right : QBracket) : Bool :=
  Q.bracketWidthLe left.lower left.upper right.lower right.upper

/-- A reusable finite row: the inner bracket is contained and has higher weight. -/
def finiteWeightImproves (R outerRejection innerRejection : Nat) : Bool :=
  decide (innerRejection <= outerRejection ∧
    godWeight R outerRejection < godWeight R innerRejection)

/-- Outer budget-8 half bracket: [0, 1/2]. -/
def outerHalfBracket : QBracket :=
  QBracket.ofChecked Q.zero (Q.of 1 2)

/-- Inner budget-8 quarter bracket: [1/8, 3/8]. -/
def innerQuarterBracket : QBracket :=
  QBracket.ofChecked (Q.of 1 8) (Q.of 3 8)

/-- The outer bracket width is 4/8. -/
def outerBudget8 : GodBracket 8 :=
  { bracket := outerHalfBracket
  , rejection := 4
  , matches_rejection := by native_decide }

/-- The inner bracket width is 2/8. -/
def innerBudget8 : GodBracket 8 :=
  { bracket := innerQuarterBracket
  , rejection := 2
  , matches_rejection := by native_decide }

/-- FOIL lowering certificate: narrower budget-8 bracket strictly improves weight. -/
theorem god_bracket_budget8_skip_certificate :
    bracketContained outerBudget8.bracket innerBudget8.bracket = true
    ∧ bracketWidthLe innerBudget8.bracket outerBudget8.bracket = true
    ∧ finiteWeightImproves 8 outerBudget8.rejection innerBudget8.rejection = true
    ∧ weight outerBudget8 = 5
    ∧ weight innerBudget8 = 7 := by
  native_decide

end GodBracket
end Gnosis
