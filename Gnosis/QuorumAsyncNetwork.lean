import Gnosis.QuorumConsistency

namespace Gnosis

/-- A `Nodup` quorum sub-list of a `connected` list has length bounded by
    `connected.length`. Standard `Sublist`-style argument over `List.Nodup`. -/
theorem nodup_subset_length_le
    {q connected : List Nat}
    (hSubset : ∀ r ∈ q, r ∈ connected)
    (hNodup : q.Nodup) :
    q.length ≤ connected.length := by
  induction q generalizing connected with
  | nil => simp
  | cons head tail ih =>
    have hHead : head ∈ connected := hSubset head List.mem_cons_self
    have hTailSubset : ∀ r ∈ tail, r ∈ connected.erase head := by
      intro r hr
      have hrInConnected : r ∈ connected := hSubset r (List.mem_cons_of_mem _ hr)
      have hrNeHead : r ≠ head := by
        intro hEq
        rcases List.nodup_cons.mp hNodup with ⟨hNotMem, _⟩
        subst hEq
        exact hNotMem hr
      exact (List.mem_erase_of_ne hrNeHead).mpr hrInConnected
    have hTailNodup : tail.Nodup := (List.nodup_cons.mp hNodup).2
    have hTailLen : tail.length ≤ (connected.erase head).length :=
      ih hTailSubset hTailNodup
    have hConnectedPos : 0 < connected.length :=
      List.length_pos_of_mem hHead
    have hEraseLen : (connected.erase head).length = connected.length - 1 :=
      List.length_erase_of_mem hHead
    have hTailLen2 : tail.length ≤ connected.length - 1 := by
      rw [← hEraseLen]
      exact hTailLen
    have hStep : tail.length + 1 ≤ connected.length - 1 + 1 := Nat.succ_le_succ hTailLen2
    rw [Nat.sub_add_cancel hConnectedPos] at hStep
    rw [List.length_cons]
    exact hStep

theorem minority_connected_set_cannot_host_quorum
    {replicaCount failureBudget : Nat}
    {connected : List Nat}
    (hConnectedCard : connected.length < quorumSize replicaCount failureBudget) :
    ¬ ∃ q : List Nat,
        q.Nodup ∧ (∀ r ∈ q, r ∈ connected) ∧
        q.length = quorumSize replicaCount failureBudget := by
  intro hQuorum
  rcases hQuorum with ⟨q, hNodup, hSubset, hCard⟩
  have hLe : q.length ≤ connected.length := nodup_subset_length_le hSubset hNodup
  rw [hCard] at hLe
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hLe hConnectedCard)

theorem connected_quorum_read_exact_of_coverage
    {quorum : List Nat}
    {storedVersion : Nat → Nat}
    {ackedVersion : Nat}
    (hAckMember : ∃ replica ∈ quorum, ackedVersion ≤ storedVersion replica)
    (hNoReplicaAhead : ∀ replica ∈ quorum, storedVersion replica ≤ ackedVersion) :
    readValue quorum storedVersion = ackedVersion := by
  exact committed_read_exact_of_coverage hAckMember hNoReplicaAhead

def minoritySplitReadSet : List Nat := [0, 1]

def minoritySplitStoredVersion (replica : Nat) : Nat :=
  if replica = 0 ∨ replica = 1 then 1 else 2

def minoritySplitAckedVersion : Nat := 2

theorem minority_split_read_set_not_quorum :
    minoritySplitReadSet.length < quorumSize 5 2 := by
  decide

theorem minority_split_read_stale_if_weak_reads_are_allowed :
    readValue minoritySplitReadSet minoritySplitStoredVersion = 1 := by
  decide

theorem minority_split_read_below_acked_if_weak_reads_are_allowed :
    readValue minoritySplitReadSet minoritySplitStoredVersion < minoritySplitAckedVersion := by
  decide

def noRepairSafeQuorum : List Nat := [0, 1, 2]

def noRepairStoredVersion : Nat → Nat
  | 4 => 1
  | _ => 2

theorem no_repair_boundary_safe_quorum_still_reads_acked :
    readValue noRepairSafeQuorum noRepairStoredVersion = 2 := by
  decide

theorem no_repair_boundary_stale_replica_persists :
    noRepairStoredVersion 4 < 2 := by
  decide

end Gnosis
