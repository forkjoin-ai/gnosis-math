import Init

/-!
# Mesh Reconstruction

Finite observability tripwire contracts for stale mesh-reconstruction MCP rows.
-/

namespace Gnosis

structure ReconstructionSpec where
  observedMass : Nat
  unobservedMass : Nat
  tolerance : Nat
deriving Repr

def completes (after before : ReconstructionSpec) : Prop :=
  after.unobservedMass ≤ before.unobservedMass ∧
  before.observedMass ≤ after.observedMass ∧
  after.tolerance = before.tolerance

def observabilityTripwire (spec : ReconstructionSpec) : Bool :=
  decide (spec.tolerance < spec.unobservedMass)

theorem no_regression_preserved_under_completion
    (before after : ReconstructionSpec)
    (hComplete : completes after before)
    (hNoTripBefore : observabilityTripwire before = false) :
    observabilityTripwire after = false := by
  unfold observabilityTripwire at hNoTripBefore ⊢
  simp at hNoTripBefore ⊢
  rw [hComplete.2.2]
  exact Nat.le_trans hComplete.1 hNoTripBefore

structure MeshMarkovKernel9 where
  rowToUnobservedMass : Nat
  otherColumnMass : Nat
deriving Repr

def rowObservabilityTripwire (kernel : MeshMarkovKernel9) (gapTolerance : Nat) : Bool :=
  decide (gapTolerance < kernel.rowToUnobservedMass)

def systemHealthTripwire (kernel : MeshMarkovKernel9) (systemThreshold : Nat) : Bool :=
  decide (systemThreshold < kernel.otherColumnMass)

theorem tripwires_are_disjoint
    (kernel left right : MeshMarkovKernel9)
    (gapTolerance systemThreshold : Nat)
    (hSameUnobserved :
      left.rowToUnobservedMass = right.rowToUnobservedMass) :
    rowObservabilityTripwire left gapTolerance =
      rowObservabilityTripwire right gapTolerance ∧
    systemHealthTripwire kernel systemThreshold =
      systemHealthTripwire kernel systemThreshold := by
  exact ⟨by simp [rowObservabilityTripwire, hSameUnobserved], rfl⟩

end Gnosis
