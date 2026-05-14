import Gnosis.Axioms

namespace Gnosis
namespace InterferenceCoarsening

/-!
# Interference Coarsening

This module restores an Init-compatible core for the old interference/coarsening
sketch.  The analytic graph quotient shell is deferred; the live proof surface is
the finite support-count schema in `Gnosis.Axioms`.
-/

structure FiniteCoarseningWitness where
  fineInitialLive : Nat
  coarseInitialLive : Nat
  coarseTerminalLive : Nat
  coarseTotalVented : Nat
  coarseTotalRepairDebt : Nat
  supportPreserving : 1 < fineInitialLive -> 1 < coarseInitialLive
  survivorFaithful : 0 < coarseInitialLive -> coarseTerminalLive = 1
  zeroVentReflectsRepair :
    coarseTotalVented = 0 ->
    1 < coarseInitialLive ->
    0 < coarseTotalRepairDebt \/ 1 < coarseTerminalLive

def FiniteCoarseningWitness.fineContagious
    (witness : FiniteCoarseningWitness) : Prop :=
  1 < witness.fineInitialLive

def FiniteCoarseningWitness.coarseDeterministicCollapse
    (witness : FiniteCoarseningWitness) : Prop :=
  0 < witness.coarseInitialLive

def FiniteCoarseningWitness.toAssumptions
    (witness : FiniteCoarseningWitness) :
    InterferenceCoarseningAssumptions where
  fineInitialLive := witness.fineInitialLive
  coarseInitialLive := witness.coarseInitialLive
  coarseTerminalLive := witness.coarseTerminalLive
  coarseTotalVented := witness.coarseTotalVented
  coarseTotalRepairDebt := witness.coarseTotalRepairDebt
  fineContagious := witness.fineContagious
  coarseDeterministicCollapse := witness.coarseDeterministicCollapse
  supportPreservingQuotient := witness.supportPreserving
  survivorFaithfulQuotient := by
    intro hCollapse
    exact witness.survivorFaithful hCollapse
  contagionReflectingQuotient := by
    intro hZeroVent _ hCoarseForked
    exact witness.zeroVentReflectsRepair hZeroVent hCoarseForked

theorem FiniteCoarseningWitness.zero_vent_requires_repair
    (witness : FiniteCoarseningWitness) :
    witness.fineContagious ->
    witness.coarseTotalVented = 0 ->
    witness.coarseDeterministicCollapse ->
    0 < witness.coarseTotalRepairDebt := by
  intro hFine hZeroVent hCollapse
  exact
    interference_coarsening_zero_vent_requires_repair
      witness.toAssumptions
      hFine
      hZeroVent
      hFine
      hCollapse

theorem FiniteCoarseningWitness.schema_instantiated
    (witness : FiniteCoarseningWitness) :
    witness.fineContagious ->
    witness.coarseDeterministicCollapse ->
    0 < witness.coarseTotalVented \/ 0 < witness.coarseTotalRepairDebt := by
  intro hFine hCollapse
  exact
    interference_coarsening_schema
      witness.toAssumptions
      hFine
      hFine
      hCollapse

def twoByFourCollapseWitness : FiniteCoarseningWitness where
  fineInitialLive := 4
  coarseInitialLive := 2
  coarseTerminalLive := 1
  coarseTotalVented := 0
  coarseTotalRepairDebt := 1
  supportPreserving := by
    intro _
    decide
  survivorFaithful := by
    intro _
    rfl
  zeroVentReflectsRepair := by
    intro _ _
    exact Or.inl (by decide)

theorem two_by_four_zero_vent_forces_repair :
    0 < twoByFourCollapseWitness.coarseTotalRepairDebt := by
  exact
    twoByFourCollapseWitness.zero_vent_requires_repair
      (by
        unfold FiniteCoarseningWitness.fineContagious
        decide)
      rfl
      (by
        unfold FiniteCoarseningWitness.coarseDeterministicCollapse
        decide)

theorem two_by_four_schema_instantiated :
    0 < twoByFourCollapseWitness.coarseTotalVented \/
      0 < twoByFourCollapseWitness.coarseTotalRepairDebt := by
  exact
    twoByFourCollapseWitness.schema_instantiated
      (by
        unfold FiniteCoarseningWitness.fineContagious
        decide)
      (by
        unfold FiniteCoarseningWitness.coarseDeterministicCollapse
        decide)

end InterferenceCoarsening
end Gnosis
