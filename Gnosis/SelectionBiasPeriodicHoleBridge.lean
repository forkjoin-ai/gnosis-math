import Init
import Gnosis.PeriodicTableTheoremMatrix
import Gnosis.SimpsonsParadox
import Gnosis.SurvivorshipBias

/-!
# Selection bias and periodic-table structural holes

Wald's bombers, Simpson's paradox, and the IUPAC 118-row periodic-table
matrix all share the same chapel lesson: the visible table is not the whole
manifold. Missing rows, missing holes, and conditioning strata carry the
structural information that changes the recommendation.
-/

namespace Gnosis
namespace SelectionBiasPeriodicHoleBridge

/-- Three finite examples of visible-data incompleteness. -/
inductive HoleExample where
  | waldBombers
  | simpsonAggregation
  | periodicTable118
deriving DecidableEq, Repr

/-- A compact certificate that an example has a visible surface and a hidden complement. -/
structure HoleBiasCertificate where
  visibleSurface : Nat
  hiddenComplement : Nat
deriving DecidableEq, Repr

/-- The carrier counts for the three examples. -/
def holeBiasCertificate : HoleExample → HoleBiasCertificate
  | .waldBombers =>
      { visibleSurface :=
          (SurvivorshipBias.waldObservation .wings).returnedHits +
            (SurvivorshipBias.waldObservation .fuselage).returnedHits +
            (SurvivorshipBias.waldObservation .tail).returnedHits,
        hiddenComplement :=
          (SurvivorshipBias.waldObservation .engines).missingLosses +
            (SurvivorshipBias.waldObservation .cockpit).missingLosses +
            (SurvivorshipBias.waldObservation .fuelTanks).missingLosses }
  | .simpsonAggregation =>
      { visibleSurface :=
          (SimpsonsParadox.aggregateCell .A).successes,
        hiddenComplement :=
          (SimpsonsParadox.aggregateCell .B).successes -
            (SimpsonsParadox.aggregateCell .A).successes }
  | .periodicTable118 =>
      { visibleSurface :=
          PeriodicTableTheoremMatrix.iupacZ118Symbols.length,
        hiddenComplement :=
          PeriodicTableTheoremMatrix.ledgerClusterEveryElement.length }

/-- Wald's visible survivor holes and missing-loss holes balance in this sketch. -/
theorem wald_visible_surface_matches_hidden_complement :
    (holeBiasCertificate .waldBombers).visibleSurface =
      (holeBiasCertificate .waldBombers).hiddenComplement := by
  native_decide

/-- Simpson's finite table has a positive hidden aggregate reversal. -/
theorem simpson_hidden_complement_positive :
    0 < (holeBiasCertificate .simpsonAggregation).hiddenComplement := by
  unfold holeBiasCertificate
  exact Nat.sub_pos_of_lt SimpsonsParadox.aggregate_B_has_more_successes

/-- The IUPAC visible surface has 118 known rows. -/
theorem periodic_visible_surface_is_iupac_118 :
    (holeBiasCertificate .periodicTable118).visibleSurface = 118 := by
  unfold holeBiasCertificate
  exact PeriodicTableTheoremMatrix.iupacZ118Symbols_length

/-- The periodic table's structural-hole cluster is nonempty. -/
theorem periodic_hidden_hole_cluster_nonempty :
    0 < (holeBiasCertificate .periodicTable118).hiddenComplement := by
  unfold holeBiasCertificate PeriodicTableTheoremMatrix.ledgerClusterEveryElement
  native_decide

/-- The periodic-table 118-row surface matches the braid phase-cardinality witness. -/
theorem periodic_visible_surface_matches_braid_phase_cardinality :
    (holeBiasCertificate .periodicTable118).visibleSurface =
      PeriodicBraidMatterJugular.iupacBraidPhaseCardinality := by
  rw [periodic_visible_surface_is_iupac_118,
    PeriodicBraidMatterJugular.iupac_braid_phase_cardinality_eq118]

/--
Shared schema: visible survivor/aggregate/table rows are not enough. Each
example has a hidden complement certified by its own module.
-/
theorem selection_bias_periodic_hole_master :
    (SurvivorshipBias.waldArmorTarget .engines = true ∧
      SurvivorshipBias.waldArmorTarget .cockpit = true ∧
      SurvivorshipBias.waldArmorTarget .fuelTanks = true ∧
      SurvivorshipBias.naiveArmorTarget .engines = false ∧
      SurvivorshipBias.naiveArmorTarget .cockpit = false ∧
      SurvivorshipBias.naiveArmorTarget .fuelTanks = false) ∧
    (SimpsonsParadox.BetterRate
        (SimpsonsParadox.trialCell .A .small)
        (SimpsonsParadox.trialCell .B .small) ∧
      SimpsonsParadox.BetterRate
        (SimpsonsParadox.trialCell .A .large)
        (SimpsonsParadox.trialCell .B .large) ∧
      SimpsonsParadox.BetterRate
        (SimpsonsParadox.aggregateCell .B)
        (SimpsonsParadox.aggregateCell .A)) ∧
    (holeBiasCertificate .periodicTable118).visibleSurface = 118 ∧
    0 < (holeBiasCertificate .periodicTable118).hiddenComplement := by
  exact ⟨SurvivorshipBias.wald_missing_holes_master,
    SimpsonsParadox.simpsons_paradox_master,
    periodic_visible_surface_is_iupac_118,
    periodic_hidden_hole_cluster_nonempty⟩

end SelectionBiasPeriodicHoleBridge
end Gnosis
