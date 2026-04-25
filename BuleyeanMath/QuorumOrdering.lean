import BuleyeanMath.QuorumConsistency

namespace BuleyeanMath

theorem committed_multiwriter_read_exact_of_coverage
    {quorum : List Nat}
    {storedBallot : Nat → Nat}
    {ackedBallot : Nat}
    (hAckMember : ∃ replica ∈ quorum, ackedBallot ≤ storedBallot replica)
    (hNoReplicaAhead : ∀ replica ∈ quorum, storedBallot replica ≤ ackedBallot) :
    readValue quorum storedBallot = ackedBallot := by
  exact committed_read_exact_of_coverage hAckMember hNoReplicaAhead

theorem committed_multiwriter_read_tracks_latest_writer
    {ballotWriter : Nat → Nat}
    {sessionReadBallot ackedBallot sessionReadWriter ackedWriter : Nat}
    (hExact : sessionReadBallot = ackedBallot)
    (hReadWriter : sessionReadWriter = ballotWriter sessionReadBallot)
    (hAckWriter : ackedWriter = ballotWriter ackedBallot) :
    sessionReadWriter = ackedWriter := by
  rw [hReadWriter, hAckWriter, hExact]

theorem committed_multiwriter_reads_monotone_of_acked_order
    {firstAck secondAck firstRead secondRead : Nat}
    (hFirstExact : firstRead = firstAck)
    (hSecondExact : secondRead = secondAck)
    (hAckOrder : firstAck <= secondAck) :
    firstRead <= secondRead := by
  omega

theorem later_committed_ballot_excludes_stale_read
    {firstAck secondAck firstRead secondRead : Nat}
    (hFirstExact : firstRead = firstAck)
    (hSecondExact : secondRead = secondAck)
    (hAckOrder : firstAck < secondAck) :
    firstRead < secondRead := by
  omega

theorem ack_monotone_does_not_force_strict_read_growth :
    ¬ (∀ firstAck secondAck firstRead secondRead : Nat,
      firstRead = firstAck →
      secondRead = secondAck →
      firstAck ≤ secondAck →
      firstRead < secondRead) := by
  intro hStrict
  have hCounterexample := hStrict 1 1 1 1 rfl rfl (by omega)
  omega

def partitionBoundaryReadSet : List Nat := [0, 1]

def partitionBoundaryStoredBallot (replica : Nat) : Nat :=
  if replica = 0 ∨ replica = 1 then 1 else 2

def partitionBoundaryLatestAck : Nat := 2

theorem partition_boundary_read_set_not_quorum :
    partitionBoundaryReadSet.length < quorumSize 5 2 := by
  decide

theorem partition_boundary_read_returns_stale_ballot :
    readValue partitionBoundaryReadSet partitionBoundaryStoredBallot = 1 := by
  decide

theorem partition_boundary_read_stale_under_split_connectivity :
    readValue partitionBoundaryReadSet partitionBoundaryStoredBallot < partitionBoundaryLatestAck := by
  decide

structure WriterBallot where
  ballot : Nat
  writer : Nat
deriving DecidableEq

def ballotCollisionLeft : WriterBallot := { ballot := 1, writer := 1 }
def ballotCollisionRight : WriterBallot := { ballot := 1, writer := 2 }

def exactReadCollisionQuorum : List Nat := [0]

def exactReadCollisionStoredBallot : Nat → Nat
  | _ => 1

def exactReadCollisionAckedBallot : Nat := 1

theorem ballot_collision_boundary_same_ballot :
    ballotCollisionLeft.ballot = ballotCollisionRight.ballot := by
  rfl

theorem ballot_collision_boundary_distinct_writers :
    ballotCollisionLeft.writer ≠ ballotCollisionRight.writer := by
  decide

theorem ballot_collision_boundary_distinct_records :
    ballotCollisionLeft ≠ ballotCollisionRight := by
  decide

theorem ballot_collision_boundary_unique_writer_fails :
    ¬ ∃ record : WriterBallot,
        record.ballot = 1 ∧ ∀ other : WriterBallot, other.ballot = 1 → other = record := by
  intro hUnique
  rcases hUnique with ⟨record, _hRecord, hOnly⟩
  have hLeft : ballotCollisionLeft = record := hOnly ballotCollisionLeft rfl
  have hRight : ballotCollisionRight = record := hOnly ballotCollisionRight rfl
  exact ballot_collision_boundary_distinct_records (hLeft.trans hRight.symm)

end BuleyeanMath
