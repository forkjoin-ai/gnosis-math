import Init

namespace Gnosis
namespace CournotCompetition

/-!
# Cournot competition (duopoly, linear inverse demand)

This module gives an Init-only formal scaffold for a two-firm Cournot game.
It separates:

1. **Economic objects** (inverse demand, profit),
2. **Optimization semantics** (`IsBestResponse`: global argmax predicate),
3. **Algebraic closed-form candidate** (`bestResponseValue`), and
4. **Fixed-point equilibrium logic** (`IsNashEquilibrium`).

The closed-form best response is encoded in discrete arithmetic as:

`qᵢ*(qⱼ) = (a - c - b*qⱼ) / (2*b)` (with `Nat` division / floor semantics).

This file defines that object and proves the fixed-point wiring
(mutual best responses => Nash) without importing calculus.
-/

/-- Linear inverse demand: `P(Q) = a - b*Q`, represented as `Int`
so below-zero prices are representable when quantity is very large. -/
def inverseDemand (a b : Nat) (qTotal : Nat) : Int :=
  (a : Int) - (b : Int) * (qTotal : Int)

/-- Firm `i` profit:
`πᵢ(qᵢ, qⱼ) = qᵢ * P(qᵢ + qⱼ) - c*qᵢ`.
We keep quantities in `Nat` and evaluate payoff in `Int`. -/
def profit (a b c : Nat) (qi qj : Nat) : Int :=
  (qi : Int) * inverseDemand a b (qi + qj) - (c : Int) * (qi : Int)

/-- Semantic best response: `qi` globally maximizes payoff against fixed `qj`. -/
def IsBestResponse (a b c : Nat) (qj qi : Nat) : Prop :=
  ∀ q : Nat, profit a b c q qj ≤ profit a b c qi qj

/-- Closed-form Cournot best-response value in discrete arithmetic.
`Nat` division implements floor semantics. -/
def bestResponseValue (a b c qj : Nat) : Nat :=
  (a - c - b * qj) / (2 * b)

/-- A firm is *playing* the closed-form best response when its chosen quantity
equals `bestResponseValue`. -/
def PlaysBestResponseValue (a b c : Nat) (qj qi : Nat) : Prop :=
  qi = bestResponseValue a b c qj

/-- Cournot Nash equilibrium in semantic (argmax) form. -/
def IsNashEquilibrium (a b c q1 q2 : Nat) : Prop :=
  IsBestResponse a b c q2 q1 ∧ IsBestResponse a b c q1 q2

/-- Cournot Nash equilibrium in closed-form fixed-point form. -/
def IsNashFixedPoint (a b c q1 q2 : Nat) : Prop :=
  PlaysBestResponseValue a b c q2 q1 ∧ PlaysBestResponseValue a b c q1 q2

/-- Master fixed-point wiring: if both firms simultaneously play best-response
values, the profile is a Cournot fixed-point equilibrium. -/
theorem nash_fixed_point_intro (a b c q1 q2 : Nat)
    (h1 : q1 = bestResponseValue a b c q2)
    (h2 : q2 = bestResponseValue a b c q1) :
    IsNashFixedPoint a b c q1 q2 := by
  exact ⟨h1, h2⟩

/-- Symmetric fixed-point condition for duopoly:
if one quantity `qe` equals its own response against itself,
then `(qe, qe)` is a fixed-point Nash profile. -/
theorem symmetric_fixed_point_of_self_response (a b c qe : Nat)
    (h : qe = bestResponseValue a b c qe) :
    IsNashFixedPoint a b c qe qe := by
  exact ⟨h, h⟩

/-- Executable witness helper:
unpack a fixed-point equilibrium into the two response equations. -/
theorem fixed_point_components (a b c q1 q2 : Nat)
    (h : IsNashFixedPoint a b c q1 q2) :
    q1 = bestResponseValue a b c q2 ∧ q2 = bestResponseValue a b c q1 := by
  exact h

/-- A pure definition-level witness showing each concept composes:
inverse demand, profit, best response value, and fixed-point equilibrium. -/
theorem cournot_master_certificate (a b c q1 q2 : Nat)
    (h1 : q1 = bestResponseValue a b c q2)
    (h2 : q2 = bestResponseValue a b c q1) :
    inverseDemand a b (q1 + q2) = (a : Int) - (b : Int) * ((q1 + q2) : Int) ∧
    IsNashFixedPoint a b c q1 q2 := by
  refine ⟨rfl, ?_⟩
  exact nash_fixed_point_intro a b c q1 q2 h1 h2

end CournotCompetition
end Gnosis
