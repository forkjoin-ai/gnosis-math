import Init

/-
  Gnosis.MeshBatchSpeedup

  Why the resilient R1 inference mesh's CONCURRENT throughput beats the pipeline count.

  Sibling of `Gnosis.PipelineSpeedup` (which bounds pipelineTime ≤ seqTime ≤ B*N). Here the
  point is the surplus ABOVE the pipeline count: each entry->exit pipeline serves one request
  at a time, so P independent pipelines give at most Px on their own — but every node also
  BATCHES concurrent requests (NATIVE_BATCH_CAPACITY), paying the fixed per-step overhead once
  for the whole batch. Model a node's time to clear a batch of `k` requests as

    tau a b k = a + b * k        (fixed overhead a > 0 once, plus b per request)

  Then a batch of B > 1 costs strictly less than B separate singles (`tau B < B * tau 1`),
  because B * tau 1 - tau B = a*(B-1) > 0. So P pipelines that batch strictly beat the Px
  pipeline-only bound. This formalizes the measured 4-node result: 2 entry->exit pipelines,
  concurrent speedup 3.23x > 2 (docs/R1_RESILIENT_MESH.md, 2026-05-24).

  This is a model-level fact about the cost function tau, not a claim the hardware EQUALS it;
  it isolates exactly why batching makes the speedup superlinear in pipelines.

  Rustic Church: Init-only, no Mathlib, no omega / simp / decide on open goals.
-/

namespace Gnosis.MeshBatchSpeedup

/-- A node's latency to clear a batch of `k` requests: a fixed per-step overhead `a` paid
once, plus `b` per request in the batch. -/
def tau (a b k : Nat) : Nat := a + b * k

/-- Core: with positive overhead, `a < B * a` whenever `1 < B`. -/
private theorem self_lt_mul (a B : Nat) (ha : 0 < a) (hB : 1 < B) : a < B * a := by
  have h1 : a * 1 < a * B := (Nat.mul_lt_mul_left ha).mpr hB
  rw [Nat.mul_one, Nat.mul_comm a B] at h1
  exact h1

/-- **Batch amortization.** A batch of `B > 1` requests costs strictly less than serving
those `B` requests one at a time. The strict surplus `B * tau 1 - tau B = a*(B-1)` is what
pushes the concurrent speedup above the pipeline count. -/
theorem batch_beats_serial (a b B : Nat) (ha : 0 < a) (hB : 1 < B) :
    tau a b B < B * tau a b 1 := by
  unfold tau
  rw [Nat.mul_one, Nat.mul_add, Nat.mul_comm b B]
  -- goal: a + B * b < B * a + B * b
  exact Nat.add_lt_add_right (self_lt_mul a B ha hB) (B * b)

/-- **The batched fleet beats the pipeline-count bound.** `P` parallel pipelines each
batching `B` spend `P * tau B`, but that clears what would serially cost `P * (B * tau 1)`;
the latter is strictly larger, so the throughput speedup is strictly greater than `P`.
(Measured: 2 pipelines, 3.23x > 2.) -/
theorem batched_fleet_beats_pipeline_count (a b B P : Nat)
    (ha : 0 < a) (hB : 1 < B) (hP : 0 < P) :
    P * tau a b B < P * (B * tau a b 1) :=
  (Nat.mul_lt_mul_left hP).mpr (batch_beats_serial a b B ha hB)

end Gnosis.MeshBatchSpeedup

/-
  Next exploration (follow-on agent):
  - Generalize `tau` to any concave (sub-additive) batch cost with positive fixed term;
    show the amortization surplus persists beyond the affine model.
  - Finite-fleet scheduling bound: N requests, P pipelines, capacity B -> wall-clock
    ≥ (N / (P*B)) * tau B, and tie it to a measured frontier (cf. PipelineSpeedup sandwich).
  - Gate the speedup on ADMITTED replicas only (cross-ref the qspec admission witnesses).
-/
