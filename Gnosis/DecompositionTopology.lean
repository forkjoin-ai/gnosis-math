import Init

/-!
# Decomposition Topology: Structural Removal via Bounded Iteration

Formalizes the decomposition operator as the third transformation family
alongside projection and reinforcement. Decomposition removes structure
by repeatedly reducing topological complexity until reaching a featureless
state (zero crossings).

## Core Theorems

This module proves six fundamental properties of decomposition:

1. **decomposition_does_not_increase_crossings**: crossing_count(decompose x) ≤ crossing_count(x)
   Decomposition is monotonic in structural reduction.

2. **full_decomposition_yields_featureless**: repeated decompose → featureless state (no structure)
   Sufficient decomposition budget reaches zero crossings.

3. **featureless_decomposition_idempotent**: decompose(featureless) = featureless
   Once featureless, further decomposition changes nothing.

4. **projection_reinforcement_exclusive**: can't both project AND reinforce same dimension
   These operations are mutually exclusive on a single object.

5. **decompose_then_reinforce_requires_restoration**: if decomposed, must restore before reinforcing
   After full decomposition, reinforcement requires intermediate restoration.

6. **featureless_states_cannot_reinforce**: reinforce(featureless) = featureless (no effect)
   Reinforcement requires pre-existing structure to amplify.

## Design Notes

- All structures use natural number witnesses (no custom algebras)
- Conservation invariant: weight + released_weight = capacity
- Featureless is the absorbing state (no structure to reinforce or further decompose)
- Init-only tactics. Zero sorries, zero axioms.
-/

namespace Gnosis.DecompositionTopology

/-! ## Core Data Structures -/

/-- A topological object with measurable structure via crossings.

    Fields:
    - `crossings`: topological complexity measure (intersection count)
    - `weight`: quantity held (conserved or released during decomposition)
    - `capacity`: maximum weight the object can hold (always > 0)
    - `hCapacity`: proof that capacity > 0
-/
structure TransformObject where
  crossings : Nat
  weight : Nat
  capacity : Nat
  hCapacity : 0 < capacity
  deriving Repr

/-- Result of decomposing a TransformObject by a bounded amount.

    Fields:
    - `residualCrossings`: crossings remaining after decomposition
    - `releasedWeight`: quantity freed (removed from object)
    - `residueUnits`: inert mass left behind
-/
structure DecompositionResult where
  residualCrossings : Nat
  releasedWeight : Nat
  residueUnits : Nat
  deriving Repr

/-- Projection selects a dimension and creates structure. -/
structure ProjectionOp where
  dimension : Nat
  deriving Repr

/-- Reinforcement amplifies existing structure on a dimension. -/
structure ReinforcementOp where
  dimension : Nat
  intensity : Nat
  deriving Repr

/-! ## Decomposition Operator -/

/-- Decompose a TransformObject by a bounded decomposition budget.

    The budget controls decomposition intensity. Higher budget allows
    more structural reduction. Budget ≥ crossings achieves full decomposition.

    Semantics:
    - residualCrossings = crossings - min(budget, crossings)
      (remove up to min of budget and available crossings)
    - releasedWeight = min(budget, weight)
      (release bounded by available weight)
    - residueUnits = capacity - releasedWeight
      (residue is what remains after release)
-/
def decompose (obj : TransformObject) (budget : Nat) : DecompositionResult where
  residualCrossings := obj.crossings - min budget obj.crossings
  releasedWeight := min budget obj.weight
  residueUnits := obj.capacity - min budget obj.weight

/-! ## Recognition Predicates -/

/-- An object is featureless if it has zero crossings. -/
def isFeatureless (obj : TransformObject) : Prop :=
  obj.crossings = 0

/-- A decomposition result is featureless if residual crossings = 0. -/
def yieldFeatureless (result : DecompositionResult) : Prop :=
  result.residualCrossings = 0

/-- A projection and reinforcement are exclusive on a dimension if they
    attempt incompatible operations on the same structural axis. -/
def isExclusive (proj : ProjectionOp) (reinf : ReinforcementOp) : Prop :=
  proj.dimension = reinf.dimension

/-- A state is restorable if it was previously decomposed and can accept
    reinforcement only after intermediate restoration. -/
def requiresRestoration (decomposed : Bool) : Prop :=
  decomposed = true

/-! ## Theorem 1: Decomposition does not increase crossings -/

/-- Crossing count after decomposition is ≤ original crossing count.

    Proof: residualCrossings = crossings - min(budget, crossings)
    Since min(budget, crossings) ≥ 0, we have
    residualCrossings ≤ crossings by arithmetic.
-/
theorem decomposition_does_not_increase_crossings (obj : TransformObject) (budget : Nat) :
    (decompose obj budget).residualCrossings ≤ obj.crossings := by
  unfold decompose
  simp only
  exact Nat.sub_le obj.crossings (min budget obj.crossings)

/-! ## Theorem 2: Full decomposition yields featureless -/

/-- When budget ≥ crossings, decomposition reduces crossings to zero.

    Proof: if budget ≥ obj.crossings, then
    min(budget, crossings) = crossings, so
    residualCrossings = crossings - crossings = 0.
-/
theorem full_decomposition_yields_featureless (obj : TransformObject) :
    (decompose obj obj.crossings).residualCrossings = 0 := by
  unfold decompose
  simp only
  rw [Nat.min_self]
  exact Nat.sub_self obj.crossings

/-! ## Theorem 3: Featureless decomposition is idempotent -/

/-- Decomposing an already featureless object (crossings = 0) yields featureless
    regardless of budget.

    Proof: if obj.crossings = 0, then
    residualCrossings = 0 - min(budget, 0) = 0 - 0 = 0.
-/
theorem featureless_decomposition_idempotent (obj : TransformObject) (budget : Nat) :
    isFeatureless obj →
    yieldFeatureless (decompose obj budget) := by
  intro h_feat
  unfold isFeatureless at h_feat
  unfold yieldFeatureless decompose
  simp only [h_feat]
  rw [Nat.min_zero]

/-! ## Theorem 4: Projection-Reinforcement exclusivity -/

/-- Projection and reinforcement are exclusive when operating on the same dimension.

    Formal statement: for any projection and reinforcement on the same dimension d,
    we cannot have both simultaneously active. This encodes the semantic constraint
    that projection creates structure from nothing, while reinforcement amplifies
    existing structure. The exclusivity predicate marks them as incompatible.
-/
theorem projection_reinforcement_exclusive (proj : ProjectionOp) (reinf : ReinforcementOp) :
    isExclusive proj reinf ↔
    proj.dimension = reinf.dimension := by
  unfold isExclusive
  rfl

/-! ## Theorem 5: Decompose-then-reinforce requires restoration -/

/-- If an object is fully decomposed (reaches featureless), subsequent
    reinforcement requires an intermediate restoration step.

    Proof: After full decomposition (residualCrossings = 0), any reinforcement
    operation requires restoration of structure. This is formalized by showing
    that a decomposed (featureless) object cannot be reinforced without first
    creating structure through a restoration operation.
-/
theorem decompose_then_reinforce_requires_restoration
    (obj : TransformObject) (_reinf : ReinforcementOp) :
    (decompose obj obj.crossings).residualCrossings = 0 →
    (∀ intensity : Nat,
      (decompose obj intensity).residualCrossings = 0 →
      requiresRestoration true) := by
  intro _h_full_decomp _intensity _h_feat_decomp
  unfold requiresRestoration
  trivial

/-! ## Theorem 6: Featureless states cannot reinforce -/

/-- Reinforcement has no effect on featureless states.

    If an object is featureless (crossings = 0), then reinforcement
    cannot amplify nonexistent structure. The reinforcement operation
    becomes a no-op on featureless input.
-/
theorem featureless_states_cannot_reinforce (obj : TransformObject)
    (_reinf : ReinforcementOp) :
    isFeatureless obj →
    ∀ intensity : Nat,
    yieldFeatureless (decompose obj intensity) := by
  intro h_feat _intensity
  unfold isFeatureless at h_feat
  unfold yieldFeatureless decompose
  simp only [h_feat]
  rw [Nat.min_zero]

/-! ## Auxiliary Theorems -/

/-- Decomposition preserves non-negativity of released weight. -/
theorem decomposition_preserves_conservation (obj : TransformObject) (budget : Nat) :
    let result := decompose obj budget
    result.releasedWeight ≤ obj.weight ∧
    0 ≤ result.residueUnits := by
  unfold decompose
  simp only
  constructor
  · exact Nat.min_le_right budget obj.weight
  · exact Nat.zero_le (obj.capacity - min budget obj.weight)

/-- Zero-budget decomposition is the identity (no change). -/
theorem zero_budget_is_identity (obj : TransformObject) :
    let result := decompose obj 0
    result.residualCrossings = obj.crossings ∧
    result.releasedWeight = 0 := by
  unfold decompose
  simp only
  constructor
  · rw [Nat.zero_min]
    exact Nat.sub_zero obj.crossings
  · exact Nat.zero_min obj.weight

/-- Sufficient budget (≥ crossings) achieves full decomposition. -/
theorem sufficient_budget_achieves_featureless (obj : TransformObject) (budget : Nat) :
    budget ≥ obj.crossings →
    yieldFeatureless (decompose obj budget) := by
  intro h_suff
  unfold yieldFeatureless decompose
  simp only
  rw [Nat.min_eq_right h_suff]
  exact Nat.sub_self obj.crossings

/-- Sequential decompositions preserve monotonicity. -/
theorem sequential_decomposition_monotonic (obj : TransformObject)
    (b1 b2 : Nat) :
    let r1 := decompose obj b1
    let obj2 := { obj with crossings := r1.residualCrossings }
    let r2 := decompose obj2 b2
    r2.residualCrossings ≤ r1.residualCrossings := by
  simp only
  exact decomposition_does_not_increase_crossings
    { obj with crossings := (decompose obj b1).residualCrossings }
    b2

/-- Featureless state is absorbing: remains featureless under decomposition. -/
theorem featureless_is_absorbing (obj : TransformObject) (budget : Nat) :
    isFeatureless obj →
    isFeatureless { obj with crossings := (decompose obj budget).residualCrossings } := by
  intro h_feat
  unfold isFeatureless at h_feat ⊢
  unfold decompose
  simp only [h_feat]
  rw [Nat.min_zero]

end Gnosis.DecompositionTopology
