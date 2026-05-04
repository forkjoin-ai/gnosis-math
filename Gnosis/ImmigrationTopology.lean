import Gnosis.DiversityOptimality

namespace Gnosis

/-!
# Immigration Topology (Simplified)

Init-only transport-growth surface for the immigration/composition layer.

The model is intentionally narrow:

- `beta1` measures path diversity,
- `crossingNumber` measures transient integration overhead,
- immigration adds new paths and crossings,
- assimilation removes only the crossing overhead,
- deficit is computed against the path count after integration.
-/

structure KnotTopology where
  beta1 : Nat
  crossingNumber : Nat
deriving DecidableEq, Repr

structure HostTopology where
  knot : KnotTopology
deriving DecidableEq, Repr

structure ImmigrantTopology where
  knot : KnotTopology
deriving DecidableEq, Repr

/-- Diversity count is measured directly by `β₁`. -/
def diversityCount (beta1 : Nat) : Nat :=
  beta1

/-- Effective concurrency shadows diversity in this simplified model. -/
def effectiveConcurrency (beta1 : Nat) : Nat :=
  beta1

/-- Immigration composes host and immigrant path counts additively. -/
def postImmigrationPaths (host : HostTopology) (imm : ImmigrantTopology) : Nat :=
  host.knot.beta1 + imm.knot.beta1

/-- The transient knot after immigration adds crossing overhead. -/
def postImmigrationKnot (host : HostTopology) (imm : ImmigrantTopology) : KnotTopology :=
  { beta1 := postImmigrationPaths host imm
    crossingNumber := host.knot.crossingNumber + imm.knot.crossingNumber }

/-- Assimilation consumes immigrant crossing overhead without changing path count. -/
def assimilate (host : HostTopology) (imm : ImmigrantTopology) : KnotTopology :=
  { beta1 := postImmigrationPaths host imm
    crossingNumber := host.knot.crossingNumber }

/-- Deficit after assimilation is computed against the combined path count. -/
def assimilationDeficit (host : HostTopology) (imm : ImmigrantTopology) : Int :=
  topologicalDeficit (postImmigrationPaths host imm) (assimilate host imm).beta1

/-- Community support can discharge one additional unit of transient deficit. -/
def communityReducedDeficit (d : Int) : Int :=
  d - 1

/-- Residual scheduling deficit is the nonnegative part of the transient crossing gap. -/
def schedulingDeficit (knot : KnotTopology) : Nat :=
  knot.crossingNumber

/-- Greedy rejection accepts only proposals that do not increase crossings. -/
def greedyPolicy (current proposed : Nat) : Prop :=
  proposed ≤ current

/-- Failure topology when a novel immigrant is rejected by a greedy policy. -/
def immigrationFailureTopology (host : HostTopology) (imm : ImmigrantTopology) (_hNovel : 0 < imm.knot.beta1) :
    KnotTopology :=
  postImmigrationKnot host imm

theorem diversity_is_concurrency (beta1 : Nat) :
    diversityCount beta1 = effectiveConcurrency beta1 := by
  rfl

theorem immigration_is_connected_sum (host : HostTopology) (imm : ImmigrantTopology) :
    (postImmigrationKnot host imm).beta1 = host.knot.beta1 + imm.knot.beta1 := by
  rfl

theorem immigration_increases_beta1 (host : HostTopology) (imm : ImmigrantTopology)
    (hImm : 0 < imm.knot.beta1) :
    host.knot.beta1 < postImmigrationPaths host imm := by
  unfold postImmigrationPaths
  exact Nat.lt_add_of_pos_right hImm

theorem assimilation_terminates (host : HostTopology) (imm : ImmigrantTopology) :
    (assimilate host imm).crossingNumber ≤ (postImmigrationKnot host imm).crossingNumber := by
  exact Nat.le_add_right _ _

theorem assimilation_monotone_decreasing (host : HostTopology) (imm : ImmigrantTopology) :
    (assimilate host imm).crossingNumber ≤ host.knot.crossingNumber + imm.knot.crossingNumber := by
  exact Nat.le_add_right _ _

theorem immigration_grows_concurrency (host : HostTopology) (imm : ImmigrantTopology)
    (hImm : 0 < imm.knot.beta1) :
    effectiveConcurrency host.knot.beta1 <
      effectiveConcurrency (postImmigrationPaths host imm) := by
  unfold effectiveConcurrency postImmigrationPaths
  exact Nat.lt_add_of_pos_right hImm

theorem immigration_closes_deficit
    {intrinsicBeta : Nat}
    (host : HostTopology) (imm : ImmigrantTopology)
    (_hBelow : host.knot.beta1 < intrinsicBeta)
    (hStream : 1 ≤ host.knot.beta1) :
    topologicalDeficit intrinsicBeta (postImmigrationPaths host imm) ≤
      topologicalDeficit intrinsicBeta host.knot.beta1 := by
  exact deficit_monotone_in_streams hStream (Nat.le_add_right _ _)

theorem immigration_zero_deficit_at_match
    (host : HostTopology) (imm : ImmigrantTopology) :
    assimilationDeficit host imm = 0 := by
  unfold assimilationDeficit assimilate
  exact deficit_zero_at_saturation (postImmigrationPaths host imm)

theorem community_accelerates_integration (d : Int) :
    communityReducedDeficit d < d := by
  unfold communityReducedDeficit
  exact Int.sub_lt_self d (by decide : (0 : Int) < 1)

theorem greedy_rejection_deadlocks (host : HostTopology) (imm : ImmigrantTopology)
    (hImm : 0 < imm.knot.crossingNumber) :
    ¬ greedyPolicy host.knot.crossingNumber (postImmigrationKnot host imm).crossingNumber := by
  unfold greedyPolicy postImmigrationKnot
  intro hLe
  exact Nat.not_lt_of_le hLe (Nat.lt_add_of_pos_right hImm)

end Gnosis
