import Init

/-!
# Propositional Inference Rules

Init-only formalization of eight common propositional inference rules used by
the GG fact-finding and fact-checking topology layer.
-/

namespace Gnosis.GreekLogicCanon.PropositionalInference

theorem modus_ponens {P Q : Prop}
    (implication : P -> Q)
    (premise : P) :
    Q := by
  exact implication premise

theorem modus_tollens {P Q : Prop}
    (implication : P -> Q)
    (deniedConclusion : ¬ Q) :
    ¬ P := by
  intro premise
  exact deniedConclusion (implication premise)

theorem disjunctive_syllogism {P Q : Prop}
    (disjunction : P ∨ Q)
    (deniedLeft : ¬ P) :
    Q := by
  cases disjunction with
  | inl p => exact False.elim (deniedLeft p)
  | inr q => exact q

theorem hypothetical_syllogism {P Q R : Prop}
    (firstImplication : P -> Q)
    (secondImplication : Q -> R) :
    P -> R := by
  intro p
  exact secondImplication (firstImplication p)

theorem simplification {P Q : Prop}
    (conjunction : P ∧ Q) :
    P := by
  exact conjunction.left

theorem conjunction {P Q : Prop}
    (left : P)
    (right : Q) :
    P ∧ Q := by
  exact And.intro left right

theorem addition {P Q : Prop}
    (premise : P) :
    P ∨ Q := by
  exact Or.inl premise

theorem constructive_dilemma {P Q R S : Prop}
    (implications : (P -> Q) ∧ (R -> S))
    (alternatives : P ∨ R) :
    Q ∨ S := by
  cases alternatives with
  | inl p => exact Or.inl (implications.left p)
  | inr r => exact Or.inr (implications.right r)

end Gnosis.GreekLogicCanon.PropositionalInference
