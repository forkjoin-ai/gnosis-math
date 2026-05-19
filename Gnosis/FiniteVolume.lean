import Gnosis.RefinementSignature

namespace Gnosis

/-!
# Finite Volume

Finite control-volume cells, transport, divergence-free meshes, internal exchange cancellation, and conservation certificates.
-/

structure FluxCell where
  stored : Nat
  inflow : Nat
  outflow : Nat
  deriving Repr, DecidableEq

def fluxNext (cell : FluxCell) : Nat :=
  cell.stored + cell.inflow - cell.outflow

def fluxResidual (cell : FluxCell) : Nat :=
  cell.inflow - cell.outflow

def fluxDeficit (cell : FluxCell) : Nat :=
  cell.outflow - cell.inflow

structure FluxResidualObserver where
  tolerance : Nat
  deriving Repr, DecidableEq

def fluxResidualAnswer
    (cell : FluxCell) (observer : FluxResidualObserver) (depth : Nat) : Prop :=
  fluxResidual cell ≤ observer.tolerance + depth

def flux_refinement_signature :
    RefinementSignature FluxCell FluxResidualObserver :=
  { answer := fluxResidualAnswer }

theorem flux_refinement_complete (cell : FluxCell) :
    RefinementComplete flux_refinement_signature cell := by
  intro observer
  refine ⟨fluxResidual cell, ?_⟩
  intro extra
  change fluxResidual cell ≤ observer.tolerance + (fluxResidual cell + extra)
  have hassoc : observer.tolerance + fluxResidual cell + extra =
      observer.tolerance + (fluxResidual cell + extra) :=
    Nat.add_assoc observer.tolerance (fluxResidual cell) extra
  rw [← hassoc]
  exact Nat.le_trans
    (Nat.le_add_left (fluxResidual cell) observer.tolerance)
    (Nat.le_add_right (observer.tolerance + fluxResidual cell) extra)

theorem flux_refinement_tail_equal (left right : FluxCell) :
    RefinementTailEqual flux_refinement_signature left right := by
  intro observer
  refine ⟨fluxResidual left + fluxResidual right, ?_⟩
  intro extra
  unfold flux_refinement_signature fluxResidualAnswer
  have hleft : fluxResidual left ≤
      observer.tolerance + (fluxResidual left + fluxResidual right + extra) := by
    rw [Nat.add_assoc (fluxResidual left) (fluxResidual right) extra]
    exact Nat.le_trans
      (Nat.le_add_right (fluxResidual left) (fluxResidual right + extra))
      (Nat.le_add_left
        (fluxResidual left + (fluxResidual right + extra))
        observer.tolerance)
  have hright : fluxResidual right ≤
      observer.tolerance + (fluxResidual left + fluxResidual right + extra) := by
    have hbase : fluxResidual right ≤
        fluxResidual left + fluxResidual right + extra := by
      exact Nat.le_trans
        (Nat.le_add_left (fluxResidual right) (fluxResidual left))
        (Nat.le_add_right (fluxResidual left + fluxResidual right) extra)
    exact Nat.le_trans hbase
      (Nat.le_add_left
        (fluxResidual left + fluxResidual right + extra)
        observer.tolerance)
  exact ⟨fun _ => hright, fun _ => hleft⟩

def FluxBalanced (cell : FluxCell) : Prop :=
  fluxResidual cell = 0 ∧ fluxDeficit cell = 0

theorem flux_balanced_of_equal_inflow_outflow
    (cell : FluxCell) (h : cell.inflow = cell.outflow) :
    FluxBalanced cell := by
  unfold FluxBalanced fluxResidual fluxDeficit
  exact ⟨by rw [h, Nat.sub_self], by rw [h, Nat.sub_self]⟩

theorem flux_next_eq_stored_of_equal_inflow_outflow
    (cell : FluxCell) (h : cell.inflow = cell.outflow) :
    fluxNext cell = cell.stored := by
  unfold fluxNext
  rw [h]
  exact Nat.add_sub_cancel cell.stored cell.outflow

def totalStored : List FluxCell → Nat
  | [] => 0
  | cell :: rest => cell.stored + totalStored rest

def totalInflow : List FluxCell → Nat
  | [] => 0
  | cell :: rest => cell.inflow + totalInflow rest

def totalOutflow : List FluxCell → Nat
  | [] => 0
  | cell :: rest => cell.outflow + totalOutflow rest

def finiteVolumeNext (cells : List FluxCell) : Nat :=
  totalStored cells + totalInflow cells - totalOutflow cells

def finiteVolumeResidual (cells : List FluxCell) : Nat :=
  totalInflow cells - totalOutflow cells

def finiteVolumeDeficit (cells : List FluxCell) : Nat :=
  totalOutflow cells - totalInflow cells

def FiniteVolumeBalanced (cells : List FluxCell) : Prop :=
  finiteVolumeResidual cells = 0 ∧ finiteVolumeDeficit cells = 0

theorem finite_volume_balanced_of_equal_inflow_outflow
    (cells : List FluxCell)
    (h : totalInflow cells = totalOutflow cells) :
    FiniteVolumeBalanced cells := by
  unfold FiniteVolumeBalanced finiteVolumeResidual finiteVolumeDeficit
  exact ⟨by rw [h, Nat.sub_self], by rw [h, Nat.sub_self]⟩

theorem finite_volume_next_eq_stored_of_equal_inflow_outflow
    (cells : List FluxCell)
    (h : totalInflow cells = totalOutflow cells) :
    finiteVolumeNext cells = totalStored cells := by
  unfold finiteVolumeNext
  rw [h]
  exact Nat.add_sub_cancel (totalStored cells) (totalOutflow cells)

theorem total_stored_append
    (left right : List FluxCell) :
    totalStored (left ++ right) = totalStored left + totalStored right := by
  induction left with
  | nil => simp [totalStored]
  | cons cell rest ih => simp [totalStored, ih, Nat.add_assoc]

theorem total_inflow_append
    (left right : List FluxCell) :
    totalInflow (left ++ right) = totalInflow left + totalInflow right := by
  induction left with
  | nil => simp [totalInflow]
  | cons cell rest ih => simp [totalInflow, ih, Nat.add_assoc]

theorem total_outflow_append
    (left right : List FluxCell) :
    totalOutflow (left ++ right) = totalOutflow left + totalOutflow right := by
  induction left with
  | nil => simp [totalOutflow]
  | cons cell rest ih => simp [totalOutflow, ih, Nat.add_assoc]

theorem finite_volume_append_preserves_equal_boundary
    (left right : List FluxCell)
    (hleft : totalInflow left = totalOutflow left)
    (hright : totalInflow right = totalOutflow right) :
    totalInflow (left ++ right) = totalOutflow (left ++ right) := by
  rw [total_inflow_append, total_outflow_append, hleft, hright]

theorem finite_volume_append_preserves_balance
    (left right : List FluxCell)
    (hleft : totalInflow left = totalOutflow left)
    (hright : totalInflow right = totalOutflow right) :
    FiniteVolumeBalanced (left ++ right) := by
  apply finite_volume_balanced_of_equal_inflow_outflow
  exact finite_volume_append_preserves_equal_boundary left right hleft hright

structure InternalExchange where
  leftStored : Nat
  rightStored : Nat
  exchange : Nat
  deriving Repr, DecidableEq

def totalInternalExchangeStored : List InternalExchange → Nat
  | [] => 0
  | exchange :: rest =>
      exchange.leftStored + exchange.rightStored + totalInternalExchangeStored rest

def internalExchangeCells : List InternalExchange → List FluxCell
  | [] => []
  | exchange :: rest =>
      [ { stored := exchange.leftStored, inflow := 0, outflow := exchange.exchange },
        { stored := exchange.rightStored, inflow := exchange.exchange, outflow := 0 } ]
        ++ internalExchangeCells rest

theorem internal_exchange_cells_total_stored
    (exchanges : List InternalExchange) :
    totalStored (internalExchangeCells exchanges) =
      totalInternalExchangeStored exchanges := by
  induction exchanges with
  | nil =>
      simp [internalExchangeCells, totalStored, totalInternalExchangeStored]
  | cons exchange rest ih =>
      simp [internalExchangeCells, totalStored, totalInternalExchangeStored, ih,
        Nat.add_assoc]

theorem internal_exchange_cells_equal_boundary
    (exchanges : List InternalExchange) :
    totalInflow (internalExchangeCells exchanges) =
      totalOutflow (internalExchangeCells exchanges) := by
  induction exchanges with
  | nil => simp [internalExchangeCells, totalInflow, totalOutflow]
  | cons exchange rest ih =>
      simp [internalExchangeCells, totalInflow, totalOutflow, ih]

theorem finite_mesh_internal_faces_cancel
    (exchanges : List InternalExchange) :
    FiniteVolumeBalanced (internalExchangeCells exchanges) := by
  apply finite_volume_balanced_of_equal_inflow_outflow
  exact internal_exchange_cells_equal_boundary exchanges

theorem finite_mesh_internal_faces_preserve_stored
    (exchanges : List InternalExchange) :
    finiteVolumeNext (internalExchangeCells exchanges) =
      totalInternalExchangeStored exchanges := by
  rw [finite_volume_next_eq_stored_of_equal_inflow_outflow]
  · exact internal_exchange_cells_total_stored exchanges
  · exact internal_exchange_cells_equal_boundary exchanges

structure TransportRegion where
  before : Nat
  after : Nat
  boundaryIn : Nat
  boundaryOut : Nat
  deriving Repr, DecidableEq

def transportPredictedAfter (region : TransportRegion) : Nat :=
  region.before + region.boundaryIn - region.boundaryOut

def transportResidual (region : TransportRegion) : Nat :=
  region.after - transportPredictedAfter region

def transportDeficit (region : TransportRegion) : Nat :=
  transportPredictedAfter region - region.after

def TransportExact (region : TransportRegion) : Prop :=
  region.after = transportPredictedAfter region

def TransportBounded (region : TransportRegion) (tolerance : Nat) : Prop :=
  transportResidual region ≤ tolerance ∧ transportDeficit region ≤ tolerance

def transportCell (region : TransportRegion) : FluxCell :=
  { stored := region.before, inflow := region.boundaryIn, outflow := region.boundaryOut }

theorem transport_cell_next_eq_predicted
    (region : TransportRegion) :
    fluxNext (transportCell region) = transportPredictedAfter region := by
  rfl

theorem transport_exact_residual_zero
    (region : TransportRegion)
    (hexact : TransportExact region) :
    transportResidual region = 0 := by
  change region.after = transportPredictedAfter region at hexact
  unfold transportResidual
  rw [hexact, Nat.sub_self]

theorem transport_exact_deficit_zero
    (region : TransportRegion)
    (hexact : TransportExact region) :
    transportDeficit region = 0 := by
  change region.after = transportPredictedAfter region at hexact
  unfold transportDeficit
  rw [hexact, Nat.sub_self]

theorem transport_exact_bounded
    (region : TransportRegion)
    (hexact : TransportExact region)
    (tolerance : Nat) :
    TransportBounded region tolerance := by
  unfold TransportBounded
  rw [transport_exact_residual_zero region hexact,
    transport_exact_deficit_zero region hexact]
  exact ⟨Nat.zero_le tolerance, Nat.zero_le tolerance⟩

theorem stationary_transport_exact
    (before after boundaryIn boundaryOut : Nat)
    (hstored : after = before)
    (hboundary : boundaryIn = boundaryOut) :
    TransportExact
      { before := before, after := after,
        boundaryIn := boundaryIn, boundaryOut := boundaryOut } := by
  unfold TransportExact transportPredictedAfter
  rw [hstored, hboundary]
  exact (Nat.add_sub_cancel before boundaryOut).symm

theorem stationary_transport_bounded
    (before after boundaryIn boundaryOut tolerance : Nat)
    (hstored : after = before)
    (hboundary : boundaryIn = boundaryOut) :
    TransportBounded
      { before := before, after := after,
        boundaryIn := boundaryIn, boundaryOut := boundaryOut }
      tolerance := by
  exact transport_exact_bounded _
    (stationary_transport_exact before after boundaryIn boundaryOut hstored hboundary)
    tolerance

theorem transport_residual_bounded_of_after_le
    (region : TransportRegion)
    (tolerance : Nat)
    (hafter : region.after ≤ transportPredictedAfter region + tolerance) :
    transportResidual region ≤ tolerance := by
  unfold transportResidual
  rw [Nat.add_comm] at hafter
  exact Nat.sub_le_iff_le_add.mpr hafter

theorem transport_deficit_bounded_of_predicted_le
    (region : TransportRegion)
    (tolerance : Nat)
    (hpredicted : transportPredictedAfter region ≤ region.after + tolerance) :
    transportDeficit region ≤ tolerance := by
  unfold transportDeficit
  rw [Nat.add_comm] at hpredicted
  exact Nat.sub_le_iff_le_add.mpr hpredicted

theorem transport_bounded_of_mutual_le
    (region : TransportRegion)
    (tolerance : Nat)
    (hafter : region.after ≤ transportPredictedAfter region + tolerance)
    (hpredicted : transportPredictedAfter region ≤ region.after + tolerance) :
    TransportBounded region tolerance := by
  exact ⟨transport_residual_bounded_of_after_le region tolerance hafter,
    transport_deficit_bounded_of_predicted_le region tolerance hpredicted⟩

def DivergenceFreeCell (cell : FluxCell) : Prop :=
  cell.inflow = cell.outflow

def DivergenceFreeMesh : List FluxCell → Prop
  | [] => True
  | cell :: rest => DivergenceFreeCell cell ∧ DivergenceFreeMesh rest

theorem divergence_free_cell_balanced
    (cell : FluxCell)
    (hcell : DivergenceFreeCell cell) :
    FluxBalanced cell :=
  flux_balanced_of_equal_inflow_outflow cell hcell

theorem divergence_free_cell_next_eq_stored
    (cell : FluxCell)
    (hcell : DivergenceFreeCell cell) :
    fluxNext cell = cell.stored :=
  flux_next_eq_stored_of_equal_inflow_outflow cell hcell

theorem divergence_free_mesh_equal_boundary
    (cells : List FluxCell)
    (hmesh : DivergenceFreeMesh cells) :
    totalInflow cells = totalOutflow cells := by
  induction cells with
  | nil => simp [totalInflow, totalOutflow]
  | cons cell rest ih =>
      rcases hmesh with ⟨hcell, hrest⟩
      change cell.inflow = cell.outflow at hcell
      simp [totalInflow, totalOutflow, hcell, ih hrest]

theorem divergence_free_mesh_balanced
    (cells : List FluxCell)
    (hmesh : DivergenceFreeMesh cells) :
    FiniteVolumeBalanced cells := by
  apply finite_volume_balanced_of_equal_inflow_outflow
  exact divergence_free_mesh_equal_boundary cells hmesh

theorem divergence_free_mesh_next_eq_stored
    (cells : List FluxCell)
    (hmesh : DivergenceFreeMesh cells) :
    finiteVolumeNext cells = totalStored cells := by
  apply finite_volume_next_eq_stored_of_equal_inflow_outflow
  exact divergence_free_mesh_equal_boundary cells hmesh

structure FiniteVolumeConservation (cells : List FluxCell) where
  boundary : totalInflow cells = totalOutflow cells
  balanced : FiniteVolumeBalanced cells
  storedStable : finiteVolumeNext cells = totalStored cells

def finite_volume_conservation_of_equal_boundary
    (cells : List FluxCell)
    (hboundary : totalInflow cells = totalOutflow cells) :
    FiniteVolumeConservation cells :=
  { boundary := hboundary
    balanced := finite_volume_balanced_of_equal_inflow_outflow cells hboundary
    storedStable :=
      finite_volume_next_eq_stored_of_equal_inflow_outflow cells hboundary }

def finite_volume_conservation_of_divergence_free
    (cells : List FluxCell)
    (hmesh : DivergenceFreeMesh cells) :
    FiniteVolumeConservation cells :=
  finite_volume_conservation_of_equal_boundary cells
    (divergence_free_mesh_equal_boundary cells hmesh)

def finite_volume_conservation_of_internal_exchanges
    (exchanges : List InternalExchange) :
    FiniteVolumeConservation (internalExchangeCells exchanges) :=
  finite_volume_conservation_of_equal_boundary (internalExchangeCells exchanges)
    (internal_exchange_cells_equal_boundary exchanges)

theorem finite_volume_conservation_append
    (left right : List FluxCell)
    (hleft : FiniteVolumeConservation left)
    (hright : FiniteVolumeConservation right) :
    FiniteVolumeConservation (left ++ right) :=
  finite_volume_conservation_of_equal_boundary (left ++ right)
    (finite_volume_append_preserves_equal_boundary left right
      hleft.boundary hright.boundary)

theorem finite_volume_conservation_append_divergence_free_internal
    (exterior : List FluxCell)
    (exchanges : List InternalExchange)
    (hexterior : DivergenceFreeMesh exterior) :
    FiniteVolumeConservation (exterior ++ internalExchangeCells exchanges) :=
  finite_volume_conservation_append exterior (internalExchangeCells exchanges)
    (finite_volume_conservation_of_divergence_free exterior hexterior)
    (finite_volume_conservation_of_internal_exchanges exchanges)

theorem finite_volume_boundary_append_divergence_free_internal
    (exterior : List FluxCell)
    (exchanges : List InternalExchange)
    (hexterior : DivergenceFreeMesh exterior) :
    totalInflow (exterior ++ internalExchangeCells exchanges) =
      totalOutflow (exterior ++ internalExchangeCells exchanges) :=
  (finite_volume_conservation_append_divergence_free_internal
    exterior exchanges hexterior).boundary

theorem finite_volume_stored_append_divergence_free_internal
    (exterior : List FluxCell)
    (exchanges : List InternalExchange)
    (hexterior : DivergenceFreeMesh exterior) :
    finiteVolumeNext (exterior ++ internalExchangeCells exchanges) =
      totalStored (exterior ++ internalExchangeCells exchanges) :=
  (finite_volume_conservation_append_divergence_free_internal
    exterior exchanges hexterior).storedStable

end Gnosis
