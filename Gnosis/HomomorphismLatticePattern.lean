import Gnosis.BuleyErgodicClosure
import Gnosis.FoilZeroDragCompatibility

/-
  HomomorphismLatticePattern.lean
  ===============================

  Cross-pollination **Pattern B**: the *homomorphism / invariant
  preservation* shape that sits alongside `Gnosis.RetractLatticePattern`.

  Pattern A (`Retract A B`) packages forget + reach + section + round
  trip: recoverability on a sub-lattice of the poorer type.

  This module packages the dual situation: a **lift** into a richer
  target type together with a shared invariant in a third type `C`,
  coherent under the lift. There is no general section back from `B`
  to `A`; the content is *translation while preserving a certificate*
  carried in `C`.

  ## Canonical instance

  `Gnosis.BuleyErgodicClosure`: `liftToBuleyState` maps
  `PolarizationState` to `Gnosis.BuleyEquilibrium.BuleyState` and
  identifies `bulkOf s` definitionally with the lifted moonshine
  `bulkState`. The bridge theorems to `isBuleyEquilibrium` are
  one-line corollaries phrased through the packaged homomorphism.

  Zero `sorry`, zero new `axiom`.
-/


namespace HomomorphismLatticePattern

open SkyrmsUltraLongRunEquilibrium
open BuleyErgodicClosure
open Gnosis.BuleyEquilibrium (BuleyState isBuleyEquilibrium)

/-! ## Abstract invariant homomorphism -/

/-- **Invariant homomorphism (Pattern B).** A map `lift : A → B` is
    coherent with two invariant projections into `C` when the target
    invariant evaluated on the lift agrees with the source invariant
    on the preimage.

    This is the bookkeeping behind "homomorphism onto a shared
    lattice index": it is *not* a retract unless additional section
    data is supplied elsewhere. -/
structure InvariantHomomorphism (A B C : Type) where
  sourceInvariant : A → C
  targetInvariant : B → C
  lift : A → B
  coherence : ∀ a, targetInvariant (lift a) = sourceInvariant a

/-- Definitional unfolding of coherence as a named lemma. -/
theorem InvariantHomomorphism.preserves
    {A B C : Type} (H : InvariantHomomorphism A B C) (a : A) :
    H.targetInvariant (H.lift a) = H.sourceInvariant a :=
  H.coherence a

/-! ## Buley ergodic closure instance

  Source invariant: `BuleyErgodicClosure.bulkOf`.
  Target invariant: moonshine `bulkState` on `BuleyState`.
  Lift: `BuleyErgodicClosure.liftToBuleyState` (definitionally aligns
  `future_output.n` as well; we read the vector field here). -/

/-- The bulk index carried on a `BuleyState` at the moonshine vector. -/
def buleyStateBulkIndex (b : BuleyState) : Nat :=
  b.manifold_vector.bulkState

/-- The polarization → Buley lift as an `InvariantHomomorphism` along
    the shared `Nat` bulk index. -/
def buleyPolarizationInvariantHom :
    InvariantHomomorphism PolarizationState BuleyState Nat where
  sourceInvariant := bulkOf
  targetInvariant := buleyStateBulkIndex
  lift := liftToBuleyState
  coherence := fun _ => rfl

/-! ## Factoring corollaries

  The original closure theorems in `BuleyErgodicClosure` are reused
  verbatim; the homomorphism packaging only re-expresses the lift. -/

/-- `novikov_closed_lifts_to_buley_equilibrium` factors through the
    packaged `InvariantHomomorphism.lift`. -/
theorem novikov_closed_lifts_through_invariant_hom
    (s : PolarizationState) (h : IsBulkNovikovClosed s) :
    isBuleyEquilibrium (buleyPolarizationInvariantHom.lift s) :=
  novikov_closed_lifts_to_buley_equilibrium s h

/-- `skyrms_ulr_lifts_to_buley_equilibrium` factors through the same
    lift field. -/
theorem skyrms_ulr_lifts_through_invariant_hom :
    isBuleyEquilibrium
        (buleyPolarizationInvariantHom.lift skyrmsUltraLongRunFixedPoint) :=
  skyrms_ulr_lifts_to_buley_equilibrium

/-- The bulk-index conjunct of `IsBulkNovikovClosed` is the target
    invariant of the lift, by composing `coherence` with `h.1`. -/
theorem bulk_novikov_target_invariant_eq_fifty_five
    (s : PolarizationState) (h : IsBulkNovikovClosed s) :
    buleyPolarizationInvariantHom.targetInvariant
        (buleyPolarizationInvariantHom.lift s) = 55 :=
  Eq.trans (buleyPolarizationInvariantHom.coherence s) h.1

/-! ## Headline witness -/

/-- The conjunctive proposition that the headline theorem proves.
    Lifted to an `abbrev` so that downstream registries (for example
    `Gnosis.PatternAtlas`) can bundle the witness by name. -/
abbrev HomomorphismLatticeWitness : Prop :=
    (∀ a : PolarizationState,
        buleyPolarizationInvariantHom.targetInvariant
            (buleyPolarizationInvariantHom.lift a) =
          buleyPolarizationInvariantHom.sourceInvariant a) ∧
    (∀ s : PolarizationState, IsBulkNovikovClosed s →
        isBuleyEquilibrium (buleyPolarizationInvariantHom.lift s)) ∧
    isBuleyEquilibrium
        (buleyPolarizationInvariantHom.lift skyrmsUltraLongRunFixedPoint)

theorem homomorphism_lattice_pattern_witness : HomomorphismLatticeWitness :=
  ⟨buleyPolarizationInvariantHom.coherence,
   novikov_closed_lifts_through_invariant_hom,
   skyrms_ulr_lifts_through_invariant_hom⟩

/-! ## Honesty note

What this module proves:

  * An abstract `InvariantHomomorphism A B C` capturing a lift whose
    target invariant agrees with a source invariant after composition.
  * A concrete homomorphism `buleyPolarizationInvariantHom` for the
    Buley bridge: `bulkOf` on `PolarizationState` matches
    `buleyStateBulkIndex` on `liftToBuleyState` definitionally
    (`coherence` is `rfl`).
  * One-line factoring corollaries:
    `novikov_closed_lifts_through_invariant_hom`,
    `skyrms_ulr_lifts_through_invariant_hom`, and
    `bulk_novikov_target_invariant_eq_fifty_five` (the latter rewrites
    the bulk conjunct through `coherence`).
  * A second concrete homomorphism over a structured certificate:
    FOIL signal gates lift to their selected channel count while
    preserving the selected-channel and drag-residual certificate.

What this module does **not** prove:

  * Any new equilibrium or ergodic theorem beyond what
    `BuleyErgodicClosure` already contains. The corollaries are
    notational repackaging; the mathematical content remains upstream.
  * A section `BuleyState → PolarizationState` or a retract structure
    on the bulk index. The lift is genuinely one-way at the type
    level; Pattern A does not apply.
  * That arbitrary modules in the monolith fit `InvariantHomomorphism`
    with the same `C`; each instance must be checked separately.
-/

/-! ## Structured-certificate FOIL instance -/

open Gnosis.FoilZeroDragCompatibility

/-- A structured FOIL coverage certificate: selected channels plus the
    residual drag against the projected frame width. -/
structure FoilCoverageCertificate where
  selectedChannels : Nat
  dragResidual : Nat

/-- The certificate carried by a full FOIL gate. -/
def foilGateCoverageCertificate
    (gate : FoilSignalGate) : FoilCoverageCertificate where
  selectedChannels := activeChannels gate
  dragResidual := foilDrag foilProjectedFrameWidth (activeChannels gate)

/-- The same certificate read after lifting a gate to just its selected
    channel count. -/
def selectedChannelCoverageCertificate
    (selectedChannels : Nat) : FoilCoverageCertificate where
  selectedChannels := selectedChannels
  dragResidual := foilDrag foilProjectedFrameWidth selectedChannels

/-- FOIL gate projection is a second concrete invariant homomorphism,
    this time preserving a structured certificate rather than a bare
    `Nat`. -/
def foilGateCoverageInvariantHom :
    InvariantHomomorphism FoilSignalGate Nat FoilCoverageCertificate where
  sourceInvariant := foilGateCoverageCertificate
  targetInvariant := selectedChannelCoverageCertificate
  lift := activeChannels
  coherence := fun _ => rfl

theorem foil_gate_coverage_preserved
    (gate : FoilSignalGate) :
    selectedChannelCoverageCertificate
        (foilGateCoverageInvariantHom.lift gate) =
      foilGateCoverageCertificate gate :=
  foilGateCoverageInvariantHom.preserves gate

theorem cleared_gate_lift_has_zero_drag_certificate
    (gate : FoilSignalGate)
    (hSignal : gate.activationThreshold ≤ gate.witnessSignal)
    (hPotential : monsterVectorFloor ≤ gate.potentialChannels) :
    (selectedChannelCoverageCertificate
        (foilGateCoverageInvariantHom.lift gate)).dragResidual = 0 := by
  exact cleared_gate_implies_projection_zero_drag gate hSignal hPotential

theorem structured_certificate_homomorphism_witness :
    (∀ gate : FoilSignalGate,
        selectedChannelCoverageCertificate
            (foilGateCoverageInvariantHom.lift gate) =
          foilGateCoverageCertificate gate) ∧
    (∀ gate : FoilSignalGate,
      gate.activationThreshold ≤ gate.witnessSignal →
      monsterVectorFloor ≤ gate.potentialChannels →
        (selectedChannelCoverageCertificate
            (foilGateCoverageInvariantHom.lift gate)).dragResidual = 0) :=
  ⟨foil_gate_coverage_preserved,
    cleared_gate_lift_has_zero_drag_certificate⟩

/-! ## Next exploration

Closed by the FOIL structured-certificate instance above: `C` is now
`FoilCoverageCertificate`, not `Nat`, and the lift from a full signal
gate to selected channels preserves both the selected-channel field and
the projected drag residual.
-/

end HomomorphismLatticePattern
