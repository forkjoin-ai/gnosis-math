import Gnosis.FiniteVolume

namespace Gnosis

/-!
# Weak Residual

Weak residual probes over finite-volume residual and deficit observations.
-/

/-! ## Weak residual formulations -/

structure WeakFluxProbe where
  residualWeight : Nat
  deficitWeight : Nat
  tolerance : Nat
  deriving Repr, DecidableEq

def weakFluxResidual (cells : List FluxCell) (probe : WeakFluxProbe) : Nat :=
  probe.residualWeight * finiteVolumeResidual cells
    + probe.deficitWeight * finiteVolumeDeficit cells

def weakFluxAnswer
    (cells : List FluxCell) (probe : WeakFluxProbe) (depth : Nat) : Prop :=
  weakFluxResidual cells probe ≤ probe.tolerance + depth

def weak_flux_refinement_signature :
    RefinementSignature (List FluxCell) WeakFluxProbe :=
  { answer := weakFluxAnswer }

theorem weak_flux_residual_zero_of_conservation
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells)
    (probe : WeakFluxProbe) :
    weakFluxResidual cells probe = 0 := by
  unfold weakFluxResidual
  rw [hconserved.balanced.1, hconserved.balanced.2]
  simp

theorem weak_flux_answer_of_conservation
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells)
    (probe : WeakFluxProbe)
    (depth : Nat) :
    weak_flux_refinement_signature.answer cells probe depth := by
  change weakFluxResidual cells probe ≤ probe.tolerance + depth
  rw [weak_flux_residual_zero_of_conservation cells hconserved probe]
  exact Nat.zero_le (probe.tolerance + depth)

theorem weak_flux_refinement_complete
    (cells : List FluxCell) :
    RefinementComplete weak_flux_refinement_signature cells := by
  intro probe
  refine ⟨weakFluxResidual cells probe, ?_⟩
  intro extra
  change weakFluxResidual cells probe ≤
    probe.tolerance + (weakFluxResidual cells probe + extra)
  have hassoc : probe.tolerance + weakFluxResidual cells probe + extra =
      probe.tolerance + (weakFluxResidual cells probe + extra) :=
    Nat.add_assoc probe.tolerance (weakFluxResidual cells probe) extra
  rw [← hassoc]
  exact Nat.le_trans
    (Nat.le_add_left (weakFluxResidual cells probe) probe.tolerance)
    (Nat.le_add_right
      (probe.tolerance + weakFluxResidual cells probe) extra)

theorem weak_flux_refinement_tail_equal
    (left right : List FluxCell) :
    RefinementTailEqual weak_flux_refinement_signature left right := by
  intro probe
  refine ⟨weakFluxResidual left probe + weakFluxResidual right probe, ?_⟩
  intro extra
  unfold weak_flux_refinement_signature weakFluxAnswer
  have hleft : weakFluxResidual left probe ≤
      probe.tolerance +
        (weakFluxResidual left probe + weakFluxResidual right probe + extra) := by
    rw [Nat.add_assoc (weakFluxResidual left probe)
      (weakFluxResidual right probe) extra]
    exact Nat.le_trans
      (Nat.le_add_right (weakFluxResidual left probe)
        (weakFluxResidual right probe + extra))
      (Nat.le_add_left
        (weakFluxResidual left probe + (weakFluxResidual right probe + extra))
        probe.tolerance)
  have hright : weakFluxResidual right probe ≤
      probe.tolerance +
        (weakFluxResidual left probe + weakFluxResidual right probe + extra) := by
    have hbase : weakFluxResidual right probe ≤
        weakFluxResidual left probe + weakFluxResidual right probe + extra := by
      exact Nat.le_trans
        (Nat.le_add_left (weakFluxResidual right probe)
          (weakFluxResidual left probe))
        (Nat.le_add_right
          (weakFluxResidual left probe + weakFluxResidual right probe) extra)
    exact Nat.le_trans hbase
      (Nat.le_add_left
        (weakFluxResidual left probe + weakFluxResidual right probe + extra)
        probe.tolerance)
  exact ⟨fun _ => hright, fun _ => hleft⟩

theorem weak_flux_conservation_tail_equal_accepts
    (left right : List FluxCell)
    (hleft : FiniteVolumeConservation left)
    (hright : FiniteVolumeConservation right)
    (probe : WeakFluxProbe)
    (depth : Nat) :
    (weak_flux_refinement_signature.answer left probe depth ↔
      weak_flux_refinement_signature.answer right probe depth) := by
  constructor
  · intro _
    exact weak_flux_answer_of_conservation right hright probe depth
  · intro _
    exact weak_flux_answer_of_conservation left hleft probe depth

theorem weak_flux_answer_of_divergence_free_internal
    (exterior : List FluxCell)
    (exchanges : List InternalExchange)
    (hexterior : DivergenceFreeMesh exterior)
    (probe : WeakFluxProbe)
    (depth : Nat) :
    weak_flux_refinement_signature.answer
      (exterior ++ internalExchangeCells exchanges) probe depth := by
  exact weak_flux_answer_of_conservation
    (exterior ++ internalExchangeCells exchanges)
    (finite_volume_conservation_append_divergence_free_internal
      exterior exchanges hexterior)
    probe depth

theorem weak_flux_residual_zero_of_divergence_free_internal
    (exterior : List FluxCell)
    (exchanges : List InternalExchange)
    (hexterior : DivergenceFreeMesh exterior)
    (probe : WeakFluxProbe) :
    weakFluxResidual (exterior ++ internalExchangeCells exchanges) probe = 0 := by
  exact weak_flux_residual_zero_of_conservation
    (exterior ++ internalExchangeCells exchanges)
    (finite_volume_conservation_append_divergence_free_internal
      exterior exchanges hexterior)
    probe

theorem weak_flux_answer_mono_tolerance
    (cells : List FluxCell)
    (probe wider : WeakFluxProbe)
    (depth : Nat)
    (hsameResidualWeight : probe.residualWeight = wider.residualWeight)
    (hsameDeficitWeight : probe.deficitWeight = wider.deficitWeight)
    (htolerance : probe.tolerance ≤ wider.tolerance)
    (hanswer : weak_flux_refinement_signature.answer cells probe depth) :
    weak_flux_refinement_signature.answer cells wider depth := by
  change weakFluxResidual cells probe ≤ probe.tolerance + depth at hanswer
  change weakFluxResidual cells wider ≤ wider.tolerance + depth
  unfold weakFluxResidual at hanswer ⊢
  rw [← hsameResidualWeight, ← hsameDeficitWeight]
  exact Nat.le_trans hanswer (Nat.add_le_add_right htolerance depth)

theorem weak_flux_answer_mono_tolerance_same_weights
    (cells : List FluxCell)
    (residualWeight deficitWeight tolerance widerTolerance depth : Nat)
    (htolerance : tolerance ≤ widerTolerance)
    (hanswer :
      weak_flux_refinement_signature.answer cells
        { residualWeight := residualWeight,
          deficitWeight := deficitWeight,
          tolerance := tolerance }
        depth) :
    weak_flux_refinement_signature.answer cells
      { residualWeight := residualWeight,
        deficitWeight := deficitWeight,
        tolerance := widerTolerance }
      depth := by
  exact weak_flux_answer_mono_tolerance cells
    { residualWeight := residualWeight,
      deficitWeight := deficitWeight,
      tolerance := tolerance }
    { residualWeight := residualWeight,
      deficitWeight := deficitWeight,
      tolerance := widerTolerance }
    depth rfl rfl htolerance hanswer

end Gnosis
