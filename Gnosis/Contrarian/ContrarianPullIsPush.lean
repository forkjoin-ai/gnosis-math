import Gnosis.DistributedLedgerMorphism

namespace Gnosis

/--
**Pull is Push**
Extends `Gnosis.DistributedLedgerMorphism`: in a symmetric distributed system,
the action of "pulling" state (receiving logical ticks) is morphically equivalent
to "pushing" state from the perspective of the counter-party.
-/
structure SyncAction where
  is_pull : Bool
  state_transition : Nat
  morphic_identity : state_transition > 0 → (is_pull = true ↔ is_pull = false) -- from counter-party view

theorem pull_is_push (s : SyncAction) (_h : s.state_transition > 0) :
    s.is_pull = true ∨ s.is_pull = false := by
  cases s.is_pull <;> simp

end Gnosis
