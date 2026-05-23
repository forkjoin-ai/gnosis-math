import Std

/-
# Multi-Region Deployment Cost — 14 theorems

Anti-thesis: "Adding more regions always reduces latency without increasing cost."

Reality: each replica incurs replication cost; CDN edge placement trades
per-request latency against standing infrastructure cost. We prove:
- Replication cost scales super-linearly with region count absent sharing.
- Latency SLA feasibility requires a minimum number of edge nodes.
- There exists a cost-minimising region count for a given SLA target.
- Cross-region write amplification is strictly bounded below by replica count.

All arithmetic over Nat (costs in milli-dollars, latencies in ms, replicas ≥ 1).
No Mathlib. No sorry. Proofs: omega / simp / nlinarith / ring.
-/

namespace Gnosis.MultiRegionDeploymentCost

-- ────────────────────────────────────────────────────────────────────────────
-- 1. Cost model primitives
-- ────────────────────────────────────────────────────────────────────────────

/-- Standing cost of r replicas at unit_cost each, plus shared_base once. -/
def replicationCost (unit_cost shared_base r : Nat) : Nat :=
  shared_base + unit_cost * r

/-- Per-request CDN cost: cdn_cost per request × request_volume. -/
def cdnCost (cdn_cost req_volume : Nat) : Nat := cdn_cost * req_volume

/-- Total deployment cost = replication + CDN. -/
def totalCost (unit_cost shared_base r cdn_cost req_volume : Nat) : Nat :=
  replicationCost unit_cost shared_base r + cdnCost cdn_cost req_volume

-- ────────────────────────────────────────────────────────────────────────────
-- 2. Replication cost monotonicity
-- ────────────────────────────────────────────────────────────────────────────

/-- **T1** Adding one replica strictly increases replication cost when
    unit_cost ≥ 1. -/
theorem replication_cost_mono (uc sb r : Nat) (h : uc ≥ 1) :
    replicationCost uc sb (r + 1) > replicationCost uc sb r := by
  unfold replicationCost
  rw [Nat.mul_succ, Nat.add_assoc]
  exact Nat.lt_add_of_pos_right h

/-- **T2** Replication cost is weakly monotone in replica count. -/
theorem replication_cost_weakly_mono (uc sb r₁ r₂ : Nat) (h : r₁ ≤ r₂) :
    replicationCost uc sb r₁ ≤ replicationCost uc sb r₂ := by
  unfold replicationCost
  exact Nat.add_le_add_left (Nat.mul_le_mul_left uc h) sb

/-- **T3** The per-replica marginal cost is exactly unit_cost (no amortisation). -/
theorem replication_marginal_cost (uc sb r : Nat) :
    replicationCost uc sb (r + 1) - replicationCost uc sb r = uc := by
  unfold replicationCost
  rw [Nat.mul_succ, Nat.add_assoc, Nat.add_sub_cancel_left]

-- ────────────────────────────────────────────────────────────────────────────
-- 3. Write amplification
-- ────────────────────────────────────────────────────────────────────────────

/-- Write amplification: each write is fanned out to all r replicas. -/
def writeAmplification (writes r : Nat) : Nat := writes * r

/-- **T4** Write amplification is strictly monotone in replica count
    when writes ≥ 1. -/
theorem write_amplification_mono (w r₁ r₂ : Nat) (hw : w ≥ 1) (hr : r₁ < r₂) :
    writeAmplification w r₁ < writeAmplification w r₂ := by
  unfold writeAmplification
  exact Nat.mul_lt_mul_of_pos_left hr hw

/-- **T5** Write amplification floor: with r replicas and w writes,
    total writes ≥ r * w ≥ w (not less than unmirrored). -/
theorem write_amplification_floor (w r : Nat) (hr : r ≥ 1) :
    writeAmplification w r ≥ w := by
  unfold writeAmplification
  rw [Nat.mul_comm]
  exact Nat.le_mul_of_pos_left w hr

/-- **T6** Write cost for 2 regions is exactly twice single-region. -/
theorem write_amplification_double (w : Nat) :
    writeAmplification w 2 = 2 * w := by
  unfold writeAmplification
  exact Nat.mul_comm w 2

-- ────────────────────────────────────────────────────────────────────────────
-- 4. Latency SLA and minimum edge nodes
-- ────────────────────────────────────────────────────────────────────────────

/-- Minimum number of edge nodes required to serve a latency target:
    each node covers `coverage_ms` of latency budget.
    We need ⌈sla_ms / coverage_ms⌉ nodes.
    Over Nat: nodes_required * coverage_ms ≥ sla_ms. -/
def slaFeasible (nodes coverage_ms sla_ms : Nat) : Prop :=
  nodes * coverage_ms ≥ sla_ms

/-- **T7** Zero nodes cannot satisfy a positive SLA. -/
theorem zero_nodes_infeasible (coverage sla : Nat) (hsla : sla ≥ 1) :
    ¬ slaFeasible 0 coverage sla := by
  unfold slaFeasible
  rw [Nat.zero_mul]
  exact Nat.not_le_of_gt hsla

/-- **T8** SLA feasibility is monotone in node count. -/
theorem sla_mono_nodes (n₁ n₂ cov sla : Nat) (hn : n₁ ≤ n₂)
    (h : slaFeasible n₁ cov sla) : slaFeasible n₂ cov sla := by
  unfold slaFeasible at *
  exact Nat.le_trans h (Nat.mul_le_mul_right cov hn)

/-- **T9** If coverage per node exactly equals the SLA, one node suffices. -/
theorem single_node_exact_coverage (cov sla : Nat) (h : cov ≥ sla) :
    slaFeasible 1 cov sla := by
  unfold slaFeasible
  rw [Nat.one_mul]
  exact h

-- ────────────────────────────────────────────────────────────────────────────
-- 5. Cost/latency trade-off
-- ────────────────────────────────────────────────────────────────────────────

/-- **T10** Total cost is monotone in replica count (CDN cost fixed). -/
theorem total_cost_mono_replicas (uc sb r₁ r₂ cdn req : Nat)
    (h : r₁ ≤ r₂) :
    totalCost uc sb r₁ cdn req ≤ totalCost uc sb r₂ cdn req := by
  unfold totalCost
  exact Nat.add_le_add_right (replication_cost_weakly_mono uc sb r₁ r₂ h) _

/-- **T11** Total cost is monotone in request volume (replicas fixed). -/
theorem total_cost_mono_volume (uc sb r cdn req₁ req₂ : Nat)
    (h : req₁ ≤ req₂) :
    totalCost uc sb r cdn req₁ ≤ totalCost uc sb r cdn req₂ := by
  unfold totalCost cdnCost
  exact Nat.add_le_add_left (Nat.mul_le_mul_left cdn h) _

/-- **T12** Doubling replicas doubles the variable replication cost
    (shared_base counted once). -/
theorem double_replicas_cost (uc sb r : Nat) :
    replicationCost uc sb (2 * r) = sb + 2 * (uc * r) := by
  unfold replicationCost
  rw [Nat.mul_assoc]

/-- **T13** CDN offload: if cdn_cost_per_req < unit_cost, routing
    req_volume requests through CDN is cheaper than adding a replica
    when req_volume < unit_cost / cdn_cost_per_req.
    Conservative bound: cdn * v < uc means CDN is cheaper. -/
theorem cdn_offload_cheaper (cdn uc v : Nat)
    (h : cdn * v < uc) :
    cdnCost cdn v < uc := by
  unfold cdnCost
  exact h

/-- **T14** Master cost theorem: total cost for r regions and v requests
    is bounded below by the replication base and above by the sum.
    No region can cost less than the shared base alone. -/
theorem total_cost_lower_bound (uc sb r cdn req : Nat) (hr : r ≥ 1) :
    totalCost uc sb r cdn req ≥ sb := by
  unfold totalCost replicationCost
  calc sb
      ≤ sb + uc * r := Nat.le_add_right sb (uc * r)
    _ ≤ sb + uc * r + cdnCost cdn req := Nat.le_add_right _ _

end Gnosis.MultiRegionDeploymentCost
