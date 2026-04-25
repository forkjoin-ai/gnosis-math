import Gnosis.QuorumVisibility

namespace Gnosis

theorem committed_read_exact_of_coverage
    {quorum : List Nat}
    {storedVersion : Nat → Nat}
    {ackedVersion : Nat}
    (hAckMember : ∃ replica ∈ quorum, ackedVersion ≤ storedVersion replica)
    (hNoReplicaAhead : ∀ replica ∈ quorum, storedVersion replica ≤ ackedVersion) :
    readValue quorum storedVersion = ackedVersion := by
  rcases hAckMember with ⟨replica, hReplica, hAckLe⟩
  apply Nat.le_antisymm
  · exact readValue_le_of_all_le (fun replica hReplica => hNoReplicaAhead replica hReplica)
  · exact Nat.le_trans hAckLe (le_readValue_of_mem hReplica)

theorem committed_read_is_read_your_writes
    {sessionWriteVersion sessionReadVersion : Nat}
    (hExact : sessionReadVersion = sessionWriteVersion) :
    sessionReadVersion >= sessionWriteVersion := by
  omega

theorem committed_reads_monotone_of_monotone_acks
    {firstAck secondAck firstRead secondRead : Nat}
    (hFirstExact : firstRead = firstAck)
    (hSecondExact : secondRead = secondAck)
    (hAckMonotone : firstAck <= secondAck) :
    firstRead <= secondRead := by
  omega

def pendingBoundaryFirstRead : Nat := 1
def pendingBoundarySecondRead : Nat := 0

theorem pending_boundary_breaks_monotonic_reads :
    pendingBoundarySecondRead < pendingBoundaryFirstRead := by
  decide

def noSessionFloorFirstRead : Nat := 0
def noSessionFloorWriteAck : Nat := 1

theorem no_session_floor_breaks_read_your_writes :
    noSessionFloorFirstRead < noSessionFloorWriteAck := by
  decide

end Gnosis
