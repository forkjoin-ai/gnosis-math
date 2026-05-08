import Gnosis.BeckettUnnamableWitness

namespace Gnosis

/--
**Absence = Authority**
Extends `Gnosis.BeckettUnnamableWitness`: the highest systemic authority
is found in the "Unnamable" witness—the part of the state space that
lacks an identifier and thus cannot be addressed by an Operator.
-/
structure AuthorityState where
  has_name : Bool
  authority_level : Nat
  unnamable_is_maximal : has_name = false → authority_level = 100

theorem absence_of_name_is_maximal_authority (s : AuthorityState) :
    s.has_name = false → s.authority_level > 50 := by
  intro h
  have h_max := s.unnamable_is_maximal h
  rw [h_max]
  decide

end Gnosis
