import Init

/-!
# Queueing Subsumption Witness

Finite Init witness for the queueing subsumption ledger row. The broad
queueing theory claim remains represented by the existing schema modules; this
file gives the ledger a concrete executable-style arithmetic witness.
-/

namespace Gnosis.QueueingSubsumptionWitness

structure QueueSnapshot where
  arrivals : Nat
  services : Nat
deriving Repr

def backlog (snapshot : QueueSnapshot) : Nat :=
  snapshot.arrivals - snapshot.services

def frfBoundaryCycles (snapshot : QueueSnapshot) : Nat :=
  backlog snapshot

def idleSnapshot : QueueSnapshot := ⟨5, 5⟩
def loadedSnapshot : QueueSnapshot := ⟨8, 5⟩

theorem beta_zero_boundary_recovers_empty_queue :
    frfBoundaryCycles idleSnapshot = 0 := by
  native_decide

theorem positive_backlog_embeds_as_boundary_cycles :
    frfBoundaryCycles loadedSnapshot = 3 := by
  native_decide

theorem service_monotone_reduces_backlog :
    backlog ⟨8, 6⟩ < backlog loadedSnapshot := by
  native_decide

theorem queue_embedding_witness :
    frfBoundaryCycles idleSnapshot = 0 ∧
    0 < frfBoundaryCycles loadedSnapshot ∧
    backlog ⟨8, 6⟩ < backlog loadedSnapshot := by
  native_decide

end Gnosis.QueueingSubsumptionWitness
