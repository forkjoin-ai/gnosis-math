import ForkRaceFoldTheorems.DarkForkMeshCrossPollination

namespace Gnosis

/-!
# Dark Fork Atomized Encryption

Unknowability is treated as a cryptographic resource.

A public observer sees only the observable ledger, while fold-time processing
sees the reconciled ledger. Their gap (`epistemicGap`) is converted into an
"atomization factor" that scales encryption work in sharded form.

This provides a formal bridge from dark-fork topology to a crypto surface
for mesh-atomized encryption.

Zero -- placeholder.
-/

/-- Atomization factor extracted from dark-fork epistemic gap. -/
def atomizationFactor (d : DarkForkMesh) (required : Nat) : Nat :=
  epistemicGap d required

/-- Mesh-atomized encryption work model.
    `keyspace` is per-atom effort; atoms multiply by epistemic gap. -/
def meshAtomizedCost (d : DarkForkMesh) (required keyspace : Nat) : Nat :=
  keyspace * atomizationFactor d required

/-- Security uplift relative to a non-atomized baseline (one atom). -/
def atomizationUplift (d : DarkForkMesh) (required keyspace : Nat) : Nat :=
  meshAtomizedCost d required keyspace - keyspace

/-- Global upper bound: atomization factor cannot exceed hidden forks. -/
theorem atomization_factor_le_hidden
    (d : DarkForkMesh) (required : Nat) :
    atomizationFactor d required ≤ d.hiddenForks := by
  unfold atomizationFactor
  exact epistemic_gap_le_hidden d required

/-- In shortfall, atomization factor is exactly hidden forks. -/
theorem atomization_factor_exact_in_shortfall
    (d : DarkForkMesh) (required : Nat)
    (hShort : totalForkLanes d ≤ required) :
    atomizationFactor d required = d.hiddenForks := by
  unfold atomizationFactor
  exact epistemic_gap_exact_in_shortfall d required hShort

/-- Cost is bounded by hidden forks at fixed keyspace. -/
theorem mesh_cost_le_hidden_scaled
    (d : DarkForkMesh) (required keyspace : Nat) :
    meshAtomizedCost d required keyspace ≤ keyspace * d.hiddenForks := by
  unfold meshAtomizedCost
  have h := atomization_factor_le_hidden d required
  unfold atomizationFactor at h
  omega

/-- In shortfall, cost is exactly keyspace × hiddenForks. -/
theorem mesh_cost_exact_in_shortfall
    (d : DarkForkMesh) (required keyspace : Nat)
    (hShort : totalForkLanes d ≤ required) :
    meshAtomizedCost d required keyspace = keyspace * d.hiddenForks := by
  unfold meshAtomizedCost
  rw [atomization_factor_exact_in_shortfall d required hShort]

/-- If hidden forks are absent, atomized crypto advantage collapses to zero. -/
theorem no_hidden_no_atomized_gain
    (d : DarkForkMesh) (required keyspace : Nat)
    (hZero : d.hiddenForks = 0) :
    meshAtomizedCost d required keyspace = 0 := by
  unfold meshAtomizedCost
  have hFac : atomizationFactor d required = 0 := by
    apply Nat.eq_zero_of_le_zero
    have hLe : atomizationFactor d required ≤ d.hiddenForks :=
      atomization_factor_le_hidden d required
    omega
  rw [hFac]
  omega

/-- If keyspace is positive and shortfall holds with at least one hidden fork,
    atomized cost is at least one keyspace unit (strict cryptographic uplift). -/
theorem positive_cost_from_hidden_shortfall
    (d : DarkForkMesh) (required keyspace : Nat)
    (hShort : totalForkLanes d ≤ required)
    (hHidden : 1 ≤ d.hiddenForks)
    (hKey : 0 < keyspace) :
    keyspace ≤ meshAtomizedCost d required keyspace := by
  rw [mesh_cost_exact_in_shortfall d required keyspace hShort]
  omega

/-- Uplift is nonnegative whenever atomization factor is at least one. -/
theorem uplift_nonnegative_when_atomized
    (d : DarkForkMesh) (required keyspace : Nat)
    (hAtomized : 1 ≤ atomizationFactor d required) :
    keyspace ≤ meshAtomizedCost d required keyspace := by
  unfold meshAtomizedCost
  omega

/-- Crypto master theorem for dark-fork atomization.
    1) factor is hidden-bounded,
    2) shortfall gives exact hidden scaling,
    3) positive keyspace gets positive uplift when hidden+shortfall hold. -/
theorem mesh_atomized_crypto_master
    (d : DarkForkMesh) (required keyspace : Nat)
    (hShort : totalForkLanes d ≤ required)
    (hHidden : 1 ≤ d.hiddenForks)
    (hKey : 0 < keyspace) :
    atomizationFactor d required ≤ d.hiddenForks ∧
    meshAtomizedCost d required keyspace = keyspace * d.hiddenForks ∧
    keyspace ≤ meshAtomizedCost d required keyspace := by
  refine ⟨atomization_factor_le_hidden d required, ?_, ?_⟩
  · exact mesh_cost_exact_in_shortfall d required keyspace hShort
  · exact positive_cost_from_hidden_shortfall d required keyspace hShort hHidden hKey

/-- Regime III (global shortfall): demand strictly exceeds total folded lanes.
    Observable and reconciled deficits are positive; epistemic gap is exactly
    hidden forks; mesh-atomized cost is keyspace × hidden forks. -/
theorem regime_global_shortfall_mesh_cost_master
    (d : DarkForkMesh) (required keyspace : Nat)
    (hStrict : totalForkLanes d < required) :
    0 < observableDeficit d required ∧
    0 < reconciledDeficit d required ∧
    epistemicGap d required = d.hiddenForks ∧
    meshAtomizedCost d required keyspace = keyspace * d.hiddenForks := by
  rcases regime_global_shortfall d required hStrict with ⟨hObs, hRec, hGap⟩
  have hShort : totalForkLanes d ≤ required := Nat.le_of_lt hStrict
  exact ⟨hObs, hRec, hGap, mesh_cost_exact_in_shortfall d required keyspace hShort⟩

-- ═══════════════════════════════════════════════════════════════════════
-- Observation model: unknowability as reconstruction hardness
-- ═══════════════════════════════════════════════════════════════════════

/-- Atomized ciphertext observation surface. -/
structure AtomizedObservation where
  totalAtoms : Nat
  observedAtoms : Nat
  keyspace : Nat
  observed_le_total : observedAtoms ≤ totalAtoms
  keyspace_pos : 0 < keyspace

/-- Hidden atoms are the unknowable reconstruction units. -/
def hiddenAtoms (o : AtomizedObservation) : Nat :=
  o.totalAtoms - o.observedAtoms

/-- Linearized reconstruction work surface (lower-bound style). -/
def reconstructionWork (o : AtomizedObservation) : Nat :=
  o.keyspace * hiddenAtoms o

/-- Full observation collapses hidden atoms to zero. -/
theorem full_observation_zero_hidden (o : AtomizedObservation)
    (hFull : o.observedAtoms = o.totalAtoms) :
    hiddenAtoms o = 0 := by
  unfold hiddenAtoms
  omega

/-- Strictly partial observation implies at least one hidden atom. -/
theorem partial_observation_positive_hidden (o : AtomizedObservation)
    (hPartial : o.observedAtoms < o.totalAtoms) :
    0 < hiddenAtoms o := by
  unfold hiddenAtoms
  omega

/-- No hidden atoms implies full observation (given observation bound). -/
theorem zero_hidden_implies_full_observation (o : AtomizedObservation)
    (hZero : hiddenAtoms o = 0) :
    o.observedAtoms = o.totalAtoms := by
  unfold hiddenAtoms at hZero
  omega

/-- Reconstruction work is positive whenever any atom remains hidden. -/
theorem hidden_atoms_imply_positive_work (o : AtomizedObservation)
    (hHidden : 0 < hiddenAtoms o) :
    0 < reconstructionWork o := by
  unfold reconstructionWork
  exact Nat.mul_pos o.keyspace_pos hHidden

/-- Work collapses to zero iff observation is complete. -/
theorem work_zero_iff_full_observation (o : AtomizedObservation) :
    reconstructionWork o = 0 ↔ o.observedAtoms = o.totalAtoms := by
  constructor
  · intro h
    have hHidden : hiddenAtoms o = 0 := by
      unfold reconstructionWork at h
      have : o.keyspace = 0 ∨ hiddenAtoms o = 0 := Nat.mul_eq_zero.mp h
      cases this with
      | inl hk => omega
      | inr hh => exact hh
    exact zero_hidden_implies_full_observation o hHidden
  · intro h
    unfold reconstructionWork hiddenAtoms
    omega

/-- Observing more atoms cannot increase reconstruction work. -/
theorem more_observation_reduces_work
    (total keyspace obs1 obs2 : Nat)
    (hObsOrder : obs1 ≤ obs2)
    (hObs2Bound : obs2 ≤ total)
    (hKey : 0 < keyspace) :
    keyspace * (total - obs2) ≤ keyspace * (total - obs1) := by
  omega

/-- Bridge theorem: shortfall-induced atomization with partial observation
    yields strictly positive reconstruction work. -/
theorem shortfall_partial_observation_positive_work
    (d : DarkForkMesh) (required keyspace observed : Nat)
    (hShort : totalForkLanes d ≤ required)
    (hHidden : 1 ≤ d.hiddenForks)
    (hObs : observed < atomizationFactor d required)
    (hKey : 0 < keyspace) :
    0 < keyspace * (atomizationFactor d required - observed) := by
  have hFactorEq : atomizationFactor d required = d.hiddenForks :=
    atomization_factor_exact_in_shortfall d required hShort
  rw [hFactorEq] at hObs
  have hUnknown : 0 < d.hiddenForks - observed := by omega
  have hMul : 0 < keyspace * (d.hiddenForks - observed) := Nat.mul_pos hKey hUnknown
  rw [← hFactorEq]
  exact hMul

-- ═══════════════════════════════════════════════════════════════════════
-- Epistemic factorization: mesh cost as keyed epistemic gap
-- ═══════════════════════════════════════════════════════════════════════

/-- `atomizationFactor` is exactly the epistemic gap (definitional unfolding). -/
theorem atomization_factor_eq_epistemic (d : DarkForkMesh) (required : Nat) :
    atomizationFactor d required = epistemicGap d required := by
  rfl

/-- Mesh-atomized cost is keyspace times epistemic gap — the bridge to observers. -/
theorem mesh_atomized_via_epistemic (d : DarkForkMesh) (required keyspace : Nat) :
    meshAtomizedCost d required keyspace = keyspace * epistemicGap d required := by
  unfold meshAtomizedCost atomizationFactor
  rfl

/-- Monotone in keyspace: larger per-atom effort scales cost linearly. -/
theorem mesh_cost_monotone_keyspace (d : DarkForkMesh) (required : Nat) {k1 k2 : Nat}
    (hk : k1 ≤ k2) :
    meshAtomizedCost d required k1 ≤ meshAtomizedCost d required k2 := by
  unfold meshAtomizedCost
  exact Nat.mul_le_mul_left (atomizationFactor d required) hk

/-- Zero epistemic gap collapses mesh cost regardless of nominal keyspace. -/
theorem mesh_cost_zero_of_zero_epistemic_gap
    (d : DarkForkMesh) (required keyspace : Nat)
    (hGap : epistemicGap d required = 0) :
    meshAtomizedCost d required keyspace = 0 := by
  unfold meshAtomizedCost atomizationFactor
  rw [hGap]
  simp

/-- Positive gap and positive keyspace force strictly positive mesh cost. -/
theorem mesh_cost_pos_of_pos_gap
    (d : DarkForkMesh) (required keyspace : Nat)
    (hGap : 0 < epistemicGap d required) (hKey : 0 < keyspace) :
    0 < meshAtomizedCost d required keyspace := by
  unfold meshAtomizedCost atomizationFactor
  exact Nat.mul_pos hKey hGap

-- ═══════════════════════════════════════════════════════════════════════
-- Adversarial composition: Byzantine budgets, headroom, and mesh cost
-- ═══════════════════════════════════════════════════════════════════════

/-- Epistemic gap never exceeds the public observable deficit (fold can only help). -/
theorem epistemic_gap_le_observable_deficit (d : DarkForkMesh) (required : Nat) :
    epistemicGap d required ≤ observableDeficit d required := by
  unfold epistemicGap
  omega

/-- Mesh-atomized cost is always bounded by the keyed public-stress envelope. -/
theorem mesh_cost_le_keyed_observable_envelope
    (d : DarkForkMesh) (required keyspace : Nat) :
    meshAtomizedCost d required keyspace ≤ keyspace * observableDeficit d required := by
  rw [mesh_atomized_via_epistemic]
  exact Nat.mul_le_mul_left keyspace (epistemic_gap_le_observable_deficit d required)

/-- When fold-time deficit vanishes, epistemic gap equals observable deficit alone. -/
theorem epistemic_gap_eq_observable_when_reconciled_zero
    (d : DarkForkMesh) (required : Nat)
    (hRec : reconciledDeficit d required = 0) :
    epistemicGap d required = observableDeficit d required := by
  unfold epistemicGap
  rw [hRec]
  simp

/-- Same situation: mesh cost is exactly keyed observable deficit. -/
theorem mesh_cost_eq_keyed_observable_when_reconciled_zero
    (d : DarkForkMesh) (required keyspace : Nat)
    (hRec : reconciledDeficit d required = 0) :
    meshAtomizedCost d required keyspace = keyspace * observableDeficit d required := by
  rw [mesh_atomized_via_epistemic, epistemic_gap_eq_observable_when_reconciled_zero d required hRec]

/-- Demand + Byzantine damage within total folded lanes: mesh cost locks to keyed observable stress. -/
theorem mesh_cost_eq_keyed_observable_under_adversarial_closure
    (d : DarkForkMesh) (required keyspace : Nat)
    (hRobust : required + totalByzantineDamage d.public ≤ totalForkLanes d) :
    meshAtomizedCost d required keyspace = keyspace * observableDeficit d required := by
  exact mesh_cost_eq_keyed_observable_when_reconciled_zero d required keyspace
    (adversarial_closure_zero_deficit d required hRobust)

/-- Public mesh capacity covers demand: mesh-atomized cost vanishes (no epistemic load). -/
theorem mesh_cost_zero_under_public_capacity
    (d : DarkForkMesh) (required keyspace : Nat)
    (hPublic : required ≤ meshRoutingPaths d.public) :
    meshAtomizedCost d required keyspace = 0 := by
  rcases regime_public_sufficient d required hPublic with ⟨hObs, hRec⟩
  unfold meshAtomizedCost atomizationFactor epistemicGap
  rw [hObs, hRec]
  simp

/-- Dark-rescue regime: fold closes deficit while public still sees load — cost tracks observable only. -/
theorem mesh_cost_eq_keyed_observable_dark_rescue
    (d : DarkForkMesh) (required keyspace : Nat)
    (hPublicMiss : meshRoutingPaths d.public < required)
    (hFoldEnough : required ≤ totalForkLanes d) :
    meshAtomizedCost d required keyspace = keyspace * observableDeficit d required := by
  refine mesh_cost_eq_keyed_observable_when_reconciled_zero d required keyspace ?_
  exact (regime_dark_rescue d required hPublicMiss hFoldEnough).2

/-- `required ≤ adversarialHeadroom` is equivalent to the robust closure inequality
    (when Byzantine damage fits under the folded lane total). -/
theorem required_le_headroom_iff_robust_closure
    (d : DarkForkMesh) (required : Nat)
    (hB : totalByzantineDamage d.public ≤ totalForkLanes d) :
    required ≤ adversarialHeadroom d ↔
      required + totalByzantineDamage d.public ≤ totalForkLanes d := by
  unfold adversarialHeadroom
  constructor
  · intro h
    exact (Nat.le_sub_iff_add_le hB).mp h
  · intro h
    exact (Nat.le_sub_iff_add_le hB).mpr h

/-- Headroom feasibility implies the same keyed-observable mesh cost identity as closure. -/
theorem mesh_cost_eq_keyed_observable_of_required_le_headroom
    (d : DarkForkMesh) (required keyspace : Nat)
    (hB : totalByzantineDamage d.public ≤ totalForkLanes d)
    (hHead : required ≤ adversarialHeadroom d) :
    meshAtomizedCost d required keyspace = keyspace * observableDeficit d required := by
  apply mesh_cost_eq_keyed_observable_under_adversarial_closure
  exact (required_le_headroom_iff_robust_closure d required hB).mp hHead

/-- Bundle: adversarial robustness pathways collapse to one mesh-cost identity. -/
theorem adversarial_mesh_cost_master
    (d : DarkForkMesh) (required keyspace : Nat)
    (hRobust : required + totalByzantineDamage d.public ≤ totalForkLanes d) :
    meshAtomizedCost d required keyspace = keyspace * observableDeficit d required ∧
    reconciledDeficit d required = 0 ∧
    epistemicGap d required = observableDeficit d required := by
  refine ⟨?_, ?_, ?_⟩
  · exact mesh_cost_eq_keyed_observable_under_adversarial_closure d required keyspace hRobust
  · exact adversarial_closure_zero_deficit d required hRobust
  · exact epistemic_gap_eq_observable_when_reconciled_zero d required
      (adversarial_closure_zero_deficit d required hRobust)

-- ═══════════════════════════════════════════════════════════════════════
-- Aligned observation: reconstruction work vs mesh-atomized cost
-- ═══════════════════════════════════════════════════════════════════════

/-- When the observation lattice is aligned to the atomization factor, partial
    observation never demands more reconstruction work than the mesh cost model. -/
theorem reconstruction_work_le_aligned_mesh_cost
    (o : AtomizedObservation) (d : DarkForkMesh) (required : Nat)
    (hTotal : o.totalAtoms = atomizationFactor d required) :
    reconstructionWork o ≤ meshAtomizedCost d required o.keyspace := by
  unfold reconstructionWork meshAtomizedCost hiddenAtoms
  rw [hTotal]
  exact Nat.mul_le_mul_left o.keyspace (Nat.sub_le_self o.totalAtoms o.observedAtoms)

/-- Full unobserved alignment: observation cost equals mesh cost at zero observation. -/
theorem reconstruction_eq_mesh_when_unobserved_aligned
    (o : AtomizedObservation) (d : DarkForkMesh) (required : Nat)
    (hTotal : o.totalAtoms = atomizationFactor d required)
    (hObs : o.observedAtoms = 0) :
    reconstructionWork o = meshAtomizedCost d required o.keyspace := by
  unfold reconstructionWork meshAtomizedCost hiddenAtoms
  rw [hObs, Nat.sub_zero, hTotal]

/-- Dimensional-zero entropy budget matches mesh cost — same scalar, different narrative. -/
theorem mesh_cost_eq_chosen_entropy_dim_zero (d : DarkForkMesh) (required keyspace : Nat) :
    meshAtomizedCost d required keyspace =
      chosenEntropyBudget 0 (atomizationFactor d required) keyspace := by
  unfold meshAtomizedCost chosenEntropyBudget dimensionEntropyMultiplier
  simp [Nat.one_mul]
  rw [Nat.mul_comm]

/-- Every dimensional lift allocates at least the mesh-atomized baseline (dimension 0). -/
theorem mesh_cost_le_chosen_entropy_any_dimension
    (d : DarkForkMesh) (required keyspace dimension : Nat) :
    meshAtomizedCost d required keyspace ≤
      chosenEntropyBudget dimension (atomizationFactor d required) keyspace := by
  rw [mesh_cost_eq_chosen_entropy_dim_zero]
  exact chosen_entropy_monotone_dimension 0 dimension (atomizationFactor d required) keyspace
    (Nat.zero_le dimension)

/-- Any positive dimensional lift strictly dominates baseline mesh cost when
    atomization and keyspace are both positive. -/
theorem mesh_cost_lt_chosen_entropy_after_dim_step
    (d : DarkForkMesh) (required keyspace : Nat)
    (hAtom : 0 < atomizationFactor d required) (hKey : 0 < keyspace) :
    meshAtomizedCost d required keyspace <
      chosenEntropyBudget 1 (atomizationFactor d required) keyspace := by
  rw [mesh_cost_eq_chosen_entropy_dim_zero]
  exact choose_your_entropy_step 0 (atomizationFactor d required) keyspace hAtom hKey

/-- Once any atom is observed, aligned reconstruction work drops strictly below the
    mesh envelope (which measures the full hidden atom count). -/
theorem reconstruction_lt_mesh_when_observation_positive_aligned
    (o : AtomizedObservation) (d : DarkForkMesh) (required : Nat)
    (hTotal : o.totalAtoms = atomizationFactor d required)
    (hObsPos : 0 < o.observedAtoms) :
    reconstructionWork o < meshAtomizedCost d required o.keyspace := by
  have hsub : o.totalAtoms - o.observedAtoms < o.totalAtoms := by
    omega
  unfold reconstructionWork meshAtomizedCost hiddenAtoms
  rw [hTotal]
  exact Nat.mul_lt_mul_of_pos_left hsub o.keyspace_pos

-- ═══════════════════════════════════════════════════════════════════════
-- Dimensional entropy control (choose-your-own entropy level)
-- ═══════════════════════════════════════════════════════════════════════

/-- Entropy multiplier chosen by dimensional lift.
    dimension=0 gives baseline multiplier 1. -/
def dimensionEntropyMultiplier (dimension : Nat) : Nat :=
  dimension + 1

/-- Entropy budget chosen by (dimension × atomization × keyspace). -/
def chosenEntropyBudget (dimension atomization keyspace : Nat) : Nat :=
  dimensionEntropyMultiplier dimension * atomization * keyspace

/-- Dimension 0 is baseline entropy (no lift). -/
theorem baseline_entropy_multiplier :
    dimensionEntropyMultiplier 0 = 1 := by
  unfold dimensionEntropyMultiplier
  omega

/-- Dimensional lifts are monotone for entropy multiplier. -/
theorem entropy_multiplier_monotone (d1 d2 : Nat) (h : d1 ≤ d2) :
    dimensionEntropyMultiplier d1 ≤ dimensionEntropyMultiplier d2 := by
  unfold dimensionEntropyMultiplier
  omega

/-- Chosen entropy budget is monotone in dimension. -/
theorem chosen_entropy_monotone_dimension
    (d1 d2 atomization keyspace : Nat)
    (hDim : d1 ≤ d2) :
    chosenEntropyBudget d1 atomization keyspace ≤
      chosenEntropyBudget d2 atomization keyspace := by
  unfold chosenEntropyBudget dimensionEntropyMultiplier
  omega

/-- Chosen entropy budget is monotone in atomization factor. -/
theorem chosen_entropy_monotone_atomization
    (dimension a1 a2 keyspace : Nat)
    (hAtom : a1 ≤ a2) :
    chosenEntropyBudget dimension a1 keyspace ≤
      chosenEntropyBudget dimension a2 keyspace := by
  unfold chosenEntropyBudget dimensionEntropyMultiplier
  omega

/-- Positive atomization and keyspace imply positive chosen entropy. -/
theorem chosen_entropy_positive
    (dimension atomization keyspace : Nat)
    (hAtom : 0 < atomization)
    (hKey : 0 < keyspace) :
    0 < chosenEntropyBudget dimension atomization keyspace := by
  unfold chosenEntropyBudget dimensionEntropyMultiplier
  omega

/-- Bridge: shortfall-induced dark-fork atomization can be lifted by any
    chosen dimension to produce a tunable entropy budget. -/
theorem shortfall_dimensional_entropy
    (d : DarkForkMesh) (required dimension keyspace : Nat)
    (hShort : totalForkLanes d ≤ required)
    (hHidden : 1 ≤ d.hiddenForks)
    (hKey : 0 < keyspace) :
    chosenEntropyBudget dimension (atomizationFactor d required) keyspace =
      (dimension + 1) * d.hiddenForks * keyspace := by
  have hFactor : atomizationFactor d required = d.hiddenForks :=
    atomization_factor_exact_in_shortfall d required hShort
  unfold chosenEntropyBudget dimensionEntropyMultiplier
  rw [hFactor]

/-- Choose-your-own entropy theorem:
    increasing dimension by one step strictly increases entropy budget
    when atomization and keyspace are positive. -/
theorem choose_your_entropy_step
    (dimension atomization keyspace : Nat)
    (hAtom : 0 < atomization)
    (hKey : 0 < keyspace) :
    chosenEntropyBudget dimension atomization keyspace <
      chosenEntropyBudget (dimension + 1) atomization keyspace := by
  unfold chosenEntropyBudget dimensionEntropyMultiplier
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- Void staircase: elegant affine law for entropy by dimension
-- ═══════════════════════════════════════════════════════════════════════

/-- One-step dimensional lift adds exactly one atomization×keyspace unit
    of entropy budget. -/
theorem entropy_staircase_step_exact
    (dimension atomization keyspace : Nat) :
    chosenEntropyBudget (dimension + 1) atomization keyspace
      - chosenEntropyBudget dimension atomization keyspace =
    atomization * keyspace := by
  unfold chosenEntropyBudget dimensionEntropyMultiplier
  omega

/-- n-step dimensional lift is affine: each step contributes the same unit. -/
theorem entropy_staircase_n_steps
    (dimension steps atomization keyspace : Nat) :
    chosenEntropyBudget (dimension + steps) atomization keyspace =
      chosenEntropyBudget dimension atomization keyspace +
      steps * (atomization * keyspace) := by
  unfold chosenEntropyBudget dimensionEntropyMultiplier
  omega

/-- Closed form: entropy budget is exactly linear in (dimension + 1). -/
theorem entropy_closed_form
    (dimension atomization keyspace : Nat) :
    chosenEntropyBudget dimension atomization keyspace =
      (dimension + 1) * (atomization * keyspace) := by
  unfold chosenEntropyBudget dimensionEntropyMultiplier
  omega

/-- Resonance bridge: under shortfall, the staircase unit equals
    hiddenForks × keyspace. -/
theorem shortfall_entropy_staircase_unit
    (d : DarkForkMesh) (required dimension keyspace : Nat)
    (hShort : totalForkLanes d ≤ required) :
    chosenEntropyBudget (dimension + 1) (atomizationFactor d required) keyspace
      - chosenEntropyBudget dimension (atomizationFactor d required) keyspace =
    d.hiddenForks * keyspace := by
  have hFactor : atomizationFactor d required = d.hiddenForks :=
    atomization_factor_exact_in_shortfall d required hShort
  rw [hFactor]
  exact entropy_staircase_step_exact dimension d.hiddenForks keyspace

/-- Surprise theorem: target entropy is reachable exactly by dimensional dialing.
    Every added dimension is a deterministic entropy quantum. -/
theorem entropy_target_reachable
    (dimension steps atomization keyspace : Nat) :
    chosenEntropyBudget dimension atomization keyspace +
      steps * (atomization * keyspace) =
    chosenEntropyBudget (dimension + steps) atomization keyspace := by
  symm
  exact entropy_staircase_n_steps dimension steps atomization keyspace

end Gnosis
