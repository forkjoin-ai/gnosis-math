import ForkRaceFoldTheorems.SpiderwebMeshNetwork
import ForkRaceFoldTheorems.SpiderwebBFT

namespace Gnosis

/-!
# Dark Fork Mesh Cross-Pollination

A compact formal surface for “dark fork mesh” behavior:

- public mesh capacity comes from Spiderweb β₁ (`meshRoutingPaths`),
- hidden forks add latent routing lanes,
- fold-time testimony is bounded by a BFT quorum.

This captures the practical rule-of-thumb used in the application sketch:
hidden fork lanes cannot make deficit worse, and quorum-bounded folding
cannot over-claim witness authority.

Zero -- placeholder.
-/

/-- A dark fork mesh is a public mesh plus hidden fork lanes and a fold quorum. -/
structure DarkForkMesh where
  public : MeshConfig
  hiddenForks : Nat
  witnessQuorum : Nat
  witnessBound : witnessQuorum ≤ bftQuorum public.peers

/-- Total lanes available at fold-time = public routing + hidden forks. -/
def totalForkLanes (d : DarkForkMesh) : Nat :=
  meshRoutingPaths d.public + d.hiddenForks

/-- Deficit seen by an external observer that only sees the public mesh. -/
def observableDeficit (d : DarkForkMesh) (required : Nat) : Nat :=
  meshDeficit required d.public

/-- Deficit after fold reconciliation uses hidden fork lanes too. -/
def reconciledDeficit (d : DarkForkMesh) (required : Nat) : Nat :=
  required - totalForkLanes d

/-- Hidden forks never increase deficit at fold-time. -/
theorem reconciled_deficit_le_observable (d : DarkForkMesh) (required : Nat) :
    reconciledDeficit d required ≤ observableDeficit d required := by
  unfold reconciledDeficit observableDeficit totalForkLanes
  unfold meshDeficit meshRoutingPaths orbWebDeficit orbWebBeta1
  omega

/-- If at least one hidden fork exists, fold-time deficit is at most
    one smaller than public deficit (the +1 clinamen witness). -/
theorem clinamen_hidden_fork_gain (d : DarkForkMesh) (required : Nat)
    (hHidden : 1 ≤ d.hiddenForks) :
    reconciledDeficit d required + 1 ≤ observableDeficit d required := by
  unfold reconciledDeficit observableDeficit totalForkLanes
  unfold meshDeficit meshRoutingPaths orbWebDeficit orbWebBeta1
  omega

/-- Additional hidden forks are monotone improvements in reconciled deficit. -/
theorem more_hidden_forks_improves
    (m : MeshConfig) (h1 h2 required : Nat) (hmono : h1 ≤ h2) :
    (required - (meshRoutingPaths m + h2)) ≤
    (required - (meshRoutingPaths m + h1)) := by
  unfold meshRoutingPaths orbWebBeta1
  omega

/-- Fold testimony cannot exceed the peer set size if it is quorum-bounded. -/
theorem witness_quorum_le_peers (d : DarkForkMesh) :
    d.witnessQuorum ≤ d.public.peers := by
  exact le_trans d.witnessBound (quorum_le_peers d.public.peers)

/-- Public-vs-fold decomposition identity for deficits. -/
theorem deficit_decomposition (d : DarkForkMesh) (required : Nat) :
    observableDeficit d required =
      reconciledDeficit d required +
      (totalForkLanes d - meshRoutingPaths d.public) := by
  unfold observableDeficit reconciledDeficit totalForkLanes
  unfold meshDeficit meshRoutingPaths orbWebDeficit orbWebBeta1
  omega

/-- Master bundle: dark fork meshes preserve three operational invariants.
    (1) reconciled deficit never exceeds public deficit,
    (2) witness quorum is peer-safe,
    (3) hidden-fork gain is monotone by +1 clinamen. -/
theorem dark_fork_mesh_master (d : DarkForkMesh) (required : Nat)
    (hHidden : 1 ≤ d.hiddenForks) :
    reconciledDeficit d required ≤ observableDeficit d required ∧
    d.witnessQuorum ≤ d.public.peers ∧
    reconciledDeficit d required + 1 ≤ observableDeficit d required := by
  exact ⟨reconciled_deficit_le_observable d required,
    witness_quorum_le_peers d,
    clinamen_hidden_fork_gain d required hHidden⟩

-- ═══════════════════════════════════════════════════════════════════════
-- Extended cross-pollination lemmas
-- ═══════════════════════════════════════════════════════════════════════

/-- Hidden lanes explain exactly the observable→reconciled deficit drop
    when demand is above total folded capacity. -/
theorem hidden_exact_gain_when_unsatisfied
    (d : DarkForkMesh) (required : Nat)
    (hUnsat : totalForkLanes d ≤ required) :
    observableDeficit d required - reconciledDeficit d required = d.hiddenForks := by
  unfold observableDeficit reconciledDeficit totalForkLanes
  unfold meshDeficit meshRoutingPaths orbWebDeficit orbWebBeta1
  omega

/-- If demand exceeds public capacity and at least one hidden lane exists,
    reconciled deficit is strictly smaller than observable deficit. -/
theorem strict_gain_with_hidden_lane
    (d : DarkForkMesh) (required : Nat)
    (hPublicMiss : meshRoutingPaths d.public < required)
    (hHidden : 1 ≤ d.hiddenForks) :
    reconciledDeficit d required < observableDeficit d required := by
  unfold observableDeficit reconciledDeficit totalForkLanes
  unfold meshDeficit meshRoutingPaths orbWebDeficit orbWebBeta1 at hPublicMiss ⊢
  omega

/-- Hidden lanes are capped by the observable deficit gap under unsatisfied demand. -/
theorem hidden_lanes_bounded_by_gap
    (d : DarkForkMesh) (required : Nat)
    (hUnsat : totalForkLanes d ≤ required) :
    d.hiddenForks ≤ observableDeficit d required := by
  unfold observableDeficit totalForkLanes
  unfold meshDeficit meshRoutingPaths orbWebDeficit orbWebBeta1 at hUnsat ⊢
  omega

/-- Fold-time deficit vanishes whenever required demand is within total folded lanes. -/
theorem fold_zero_deficit_of_sufficient_total_lanes
    (d : DarkForkMesh) (required : Nat)
    (hEnough : required ≤ totalForkLanes d) :
    reconciledDeficit d required = 0 := by
  unfold reconciledDeficit
  exact Nat.sub_eq_zero_of_le hEnough

/-- Operational bundle with strict-improvement branch. -/
theorem dark_fork_mesh_strict_master
    (d : DarkForkMesh) (required : Nat)
    (hPublicMiss : meshRoutingPaths d.public < required)
    (hHidden : 1 ≤ d.hiddenForks) :
    reconciledDeficit d required < observableDeficit d required ∧
    d.witnessQuorum ≤ d.public.peers := by
  exact ⟨strict_gain_with_hidden_lane d required hPublicMiss hHidden,
    witness_quorum_le_peers d⟩

-- ═══════════════════════════════════════════════════════════════════════
-- Innovation frontier: adversarial and regime-theoretic surface
-- ═══════════════════════════════════════════════════════════════════════

/-- Epistemic gap between what public observers see and what fold-time
    reconciliation can actually resolve. -/
def epistemicGap (d : DarkForkMesh) (required : Nat) : Nat :=
  observableDeficit d required - reconciledDeficit d required

/-- Adversarial headroom after subtracting total Byzantine damage budget. -/
def adversarialHeadroom (d : DarkForkMesh) : Nat :=
  totalForkLanes d - totalByzantineDamage d.public

/-- Hidden forks upper-bound the epistemic gap for all demand levels. -/
theorem epistemic_gap_le_hidden (d : DarkForkMesh) (required : Nat) :
    epistemicGap d required ≤ d.hiddenForks := by
  unfold epistemicGap observableDeficit reconciledDeficit totalForkLanes
  unfold meshDeficit meshRoutingPaths orbWebDeficit orbWebBeta1
  omega

/-- In global shortfall, the epistemic gap is exactly the hidden lane count. -/
theorem epistemic_gap_exact_in_shortfall
    (d : DarkForkMesh) (required : Nat)
    (hShort : totalForkLanes d ≤ required) :
    epistemicGap d required = d.hiddenForks := by
  unfold epistemicGap
  exact hidden_exact_gain_when_unsatisfied d required hShort

/-- If demand plus Byzantine damage fits inside total folded lanes,
    the system still closes with zero reconciled deficit. -/
theorem adversarial_closure_zero_deficit
    (d : DarkForkMesh) (required : Nat)
    (hRobust : required + totalByzantineDamage d.public ≤ totalForkLanes d) :
    reconciledDeficit d required = 0 := by
  apply fold_zero_deficit_of_sufficient_total_lanes
  have : required ≤ required + totalByzantineDamage d.public := by omega
  exact le_trans this hRobust

/-- Hidden lanes absorb Byzantine damage when they cover the damage budget. -/
theorem hidden_absorbs_byzantine_damage
    (d : DarkForkMesh)
    (hCover : totalByzantineDamage d.public ≤ d.hiddenForks) :
    meshRoutingPaths d.public ≤ adversarialHeadroom d := by
  unfold adversarialHeadroom totalForkLanes meshRoutingPaths orbWebBeta1
  unfold totalByzantineDamage
  omega

/-- Regime I: public mesh alone is sufficient; both deficits vanish. -/
theorem regime_public_sufficient
    (d : DarkForkMesh) (required : Nat)
    (hPublic : required ≤ meshRoutingPaths d.public) :
    observableDeficit d required = 0 ∧ reconciledDeficit d required = 0 := by
  unfold observableDeficit reconciledDeficit
  unfold meshDeficit meshRoutingPaths orbWebDeficit orbWebBeta1 at hPublic ⊢
  omega

/-- Regime II: dark-rescue window. Public deficit is positive, but fold
    deficit is zero because hidden lanes close the gap. -/
theorem regime_dark_rescue
    (d : DarkForkMesh) (required : Nat)
    (hPublicMiss : meshRoutingPaths d.public < required)
    (hFoldEnough : required ≤ totalForkLanes d) :
    0 < observableDeficit d required ∧ reconciledDeficit d required = 0 := by
  unfold observableDeficit reconciledDeficit totalForkLanes
  unfold meshDeficit meshRoutingPaths orbWebDeficit orbWebBeta1 at hPublicMiss hFoldEnough ⊢
  omega

/-- Regime III: global shortfall. Both ledgers show positive deficit, and
    the hidden-lane epistemic gap remains explicitly measurable. -/
theorem regime_global_shortfall
    (d : DarkForkMesh) (required : Nat)
    (hShort : totalForkLanes d < required) :
    0 < observableDeficit d required ∧
    0 < reconciledDeficit d required ∧
    epistemicGap d required = d.hiddenForks := by
  unfold observableDeficit reconciledDeficit totalForkLanes epistemicGap
  unfold meshDeficit meshRoutingPaths orbWebDeficit orbWebBeta1 at hShort ⊢
  omega

/-- Innovation master theorem: three regimes plus adversarial closure law. -/
theorem dark_fork_innovation_master
    (d : DarkForkMesh) (required : Nat) :
    (required ≤ meshRoutingPaths d.public →
      observableDeficit d required = 0 ∧ reconciledDeficit d required = 0) ∧
    (meshRoutingPaths d.public < required →
      required ≤ totalForkLanes d →
      0 < observableDeficit d required ∧ reconciledDeficit d required = 0) ∧
    (totalForkLanes d < required →
      0 < observableDeficit d required ∧
      0 < reconciledDeficit d required ∧
      epistemicGap d required = d.hiddenForks) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact regime_public_sufficient d required h
  · intro hMiss hEnough
    exact regime_dark_rescue d required hMiss hEnough
  · intro hShort
    exact regime_global_shortfall d required hShort

end Gnosis
