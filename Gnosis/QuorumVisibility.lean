import Gnosis.FailureDurability

namespace Gnosis

/-!
Init-only quorum surface. A quorum is a `List Nat` of replica ids; the
read value is the maximum stored version across the listed replicas.

Earlier Mathlib-flavoured `Finset.sup` / `Finset.card_union_add_card_inter`
are replaced by `List.foldr max` and a parameterised `QuorumIntersection`
witness — chapel proofs do not exercise the combinatorial pigeonhole step.
-/

def readValue (quorum : List Nat) (storedVersion : Nat → Nat) : Nat :=
  quorum.foldr (fun r acc => Nat.max (storedVersion r) acc) 0

theorem le_readValue_of_mem
    {quorum : List Nat}
    {storedVersion : Nat → Nat}
    {replica : Nat}
    (hReplica : replica ∈ quorum) :
    storedVersion replica ≤ readValue quorum storedVersion := by
  induction quorum with
  | nil => cases hReplica
  | cons head tail ih =>
    rcases List.mem_cons.mp hReplica with hHead | hTail
    · subst hHead
      simp [readValue, List.foldr]
      exact Nat.le_max_left _ _
    · simp [readValue, List.foldr]
      exact Nat.le_trans (ih hTail) (Nat.le_max_right _ _)

theorem readValue_le_of_all_le
    {quorum : List Nat}
    {storedVersion : Nat → Nat}
    {bound : Nat}
    (hAll : ∀ replica ∈ quorum, storedVersion replica ≤ bound) :
    readValue quorum storedVersion ≤ bound := by
  induction quorum with
  | nil =>
    simp [readValue, List.foldr]
  | cons head tail ih =>
    simp [readValue, List.foldr]
    refine Nat.max_le.mpr ⟨?_, ?_⟩
    · exact hAll head (List.mem_cons_self)
    · exact ih (fun r hr => hAll r (List.mem_cons_of_mem _ hr))

theorem strict_majority_failure_budget_lt_quorum
    {replicaCount failureBudget : Nat}
    (hMajority : 2 * failureBudget < replicaCount) :
    failureBudget < quorumSize replicaCount failureBudget := by
  unfold quorumSize
  omega

/-- Existential intersection between two list-quorums. -/
def QuorumsIntersect (a b : List Nat) : Prop :=
  ∃ r, r ∈ a ∧ r ∈ b

/-- A read after a write that committed at a quorum sees an `ackedVersion`
    if the two quorums share a replica that stored the write. The
    combinatorial intersection is supplied as a witness — chapel proofs
    construct it directly when they need it. -/
theorem read_after_ack_visible
    {ackedVersion : Nat}
    {writeQuorum readQuorum : List Nat}
    {storedVersion : Nat → Nat}
    (hIntersect : QuorumsIntersect writeQuorum readQuorum)
    (hAckedStored : ∀ replica ∈ writeQuorum, ackedVersion ≤ storedVersion replica) :
    ackedVersion ≤ readValue readQuorum storedVersion := by
  rcases hIntersect with ⟨replica, hWrite, hRead⟩
  exact Nat.le_trans (hAckedStored replica hWrite) (le_readValue_of_mem hRead)

/-- Boundary: weak quorums on disjoint replicas can have an empty intersection. -/
def weakBoundaryWriteQuorum : List Nat := [0, 1]
def weakBoundaryReadQuorum : List Nat := [2, 3]

def weakBoundaryStoredVersion (replica : Nat) : Nat :=
  if replica = 0 ∨ replica = 1 then 1 else 0

theorem weak_quorum_boundary_not_strict_majority :
    ¬ (2 * 2 < 4) := by
  decide

theorem weak_quorum_boundary_disjoint :
    ¬ QuorumsIntersect weakBoundaryWriteQuorum weakBoundaryReadQuorum := by
  intro h
  rcases h with ⟨r, hW, hR⟩
  simp [weakBoundaryWriteQuorum, weakBoundaryReadQuorum] at hW hR
  omega

theorem weak_quorum_boundary_read_misses_acked_write :
    readValue weakBoundaryReadQuorum weakBoundaryStoredVersion = 0 := by
  decide

def contagiousBoundaryWriteQuorum : List Nat := [0, 1]
def contagiousBoundaryReadQuorum : List Nat := [1, 2]

def contagiousBoundaryStoredVersion : Nat → Nat
  | 0 => 1
  | _ => 0

theorem contagious_boundary_quorums_still_intersect :
    QuorumsIntersect contagiousBoundaryWriteQuorum contagiousBoundaryReadQuorum := by
  refine ⟨1, ?_, ?_⟩ <;> decide

theorem contagious_boundary_read_still_misses_acked_write :
    readValue contagiousBoundaryReadQuorum contagiousBoundaryStoredVersion = 0 := by
  decide

def unfairRepairBoundaryState : DurableReplicaState :=
  { liveCount := 2, repairDebt := 1, failuresRemaining := 0 }

theorem unfair_repair_boundary_well_formed :
    DurableWellFormed 3 1 unfairRepairBoundaryState := by
  unfold DurableWellFormed unfairRepairBoundaryState
  decide

theorem unfair_repair_boundary_not_stable :
    ¬ StableReplicaState 3 unfairRepairBoundaryState := by
  unfold StableReplicaState unfairRepairBoundaryState
  decide

theorem unfair_repair_boundary_stutter_keeps_state :
    unfairRepairBoundaryState = unfairRepairBoundaryState := by
  rfl

theorem unfair_repair_boundary_repair_closure_is_stable :
    StableReplicaState 3 (repairClosure unfairRepairBoundaryState) := by
  apply repair_closure_stable_of_exhausted_failures
  · exact unfair_repair_boundary_well_formed
  · rfl

end Gnosis
