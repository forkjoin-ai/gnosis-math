import Init

namespace Gnosis

/-!
# Refinement Signatures

Finite observer signatures for bounded refinement and tail-equivalence claims.
-/

structure RefinementSignature (Space Observer : Type) where
  answer : Space → Observer → Nat → Prop

def RefinementTailEqual
    {Space Observer : Type}
    (signature : RefinementSignature Space Observer)
    (left right : Space) : Prop :=
  ∀ observer : Observer, ∃ threshold : Nat,
    ∀ extra : Nat,
      (signature.answer left observer (threshold + extra) ↔
        signature.answer right observer (threshold + extra))

def RefinementComplete
    {Space Observer : Type}
    (signature : RefinementSignature Space Observer)
    (space : Space) : Prop :=
  ∀ observer : Observer, ∃ threshold : Nat,
    ∀ extra : Nat, signature.answer space observer (threshold + extra)

end Gnosis
