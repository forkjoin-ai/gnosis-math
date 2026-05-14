import Gnosis.ThermodynamicRefinement
import Gnosis.MythOfInfinitePrecision

namespace Gnosis

/-!
# Landauer Buley

Finite Init-only restoration of the old Landauer bridge. The old sketch used
`Real`, `ENNReal`, `PMF`, big operators, and Mathlib entropy lemmas. This module
keeps the finite Rustic Church core:

* deterministic collapse of `n` live branches costs `n - 1` erasures;
* each erased branch costs at least one Bule;
* bracket refinements from the Real-like precision stack pay the same unit cost;
* infinite free precision is rejected by the sliver-width modules.
-/

namespace LandauerBuley

open BracketedSpace
open ForkRaceFoldMath
open ThermodynamicRefinement
open MythOfInfinitePrecision
open CausalDiamond

def deterministicCollapseFailureTax (liveBranches : Nat) : Nat :=
  liveBranches - 1

def landauerBuleLowerBound (erasedBranches : Nat) : Nat :=
  erasedBranches

def deterministicCollapseBuleCost (liveBranches : Nat) : Nat :=
  landauerBuleLowerBound (deterministicCollapseFailureTax liveBranches)

theorem collapse_tax_zero_of_empty :
    deterministicCollapseFailureTax 0 = 0 := by
  rfl

theorem collapse_tax_zero_of_singleton :
    deterministicCollapseFailureTax 1 = 0 := by
  rfl

theorem binary_failure_tax_one :
    deterministicCollapseFailureTax 2 = 1 := by
  rfl

theorem collapse_tax_positive_of_two_or_more
    {liveBranches : Nat}
    (hLive : 2 <= liveBranches) :
    0 < deterministicCollapseFailureTax liveBranches := by
  exact Nat.sub_pos_of_lt hLive

theorem collapse_tax_monotone
    {left right : Nat}
    (h : left <= right) :
    deterministicCollapseFailureTax left <= deterministicCollapseFailureTax right := by
  exact Nat.sub_le_sub_right h 1

theorem collapse_bule_cost_eq_tax
    (liveBranches : Nat) :
    deterministicCollapseBuleCost liveBranches =
      deterministicCollapseFailureTax liveBranches := by
  rfl

theorem collapse_bule_cost_monotone
    {left right : Nat}
    (h : left <= right) :
    deterministicCollapseBuleCost left <= deterministicCollapseBuleCost right := by
  exact collapse_tax_monotone h

structure FiniteErasureFrontier where
  liveBranches : Nat
  erasedBranches : Nat
  collapseWitness : erasedBranches = deterministicCollapseFailureTax liveBranches

namespace FiniteErasureFrontier

def heatLowerBound (frontier : FiniteErasureFrontier) : Nat :=
  landauerBuleLowerBound frontier.erasedBranches

theorem heat_eq_failure_tax
    (frontier : FiniteErasureFrontier) :
    frontier.heatLowerBound =
      deterministicCollapseFailureTax frontier.liveBranches := by
  rw [heatLowerBound, landauerBuleLowerBound, frontier.collapseWitness]

theorem heat_positive_of_two_or_more
    (frontier : FiniteErasureFrontier)
    (hLive : 2 <= frontier.liveBranches) :
    0 < frontier.heatLowerBound := by
  rw [frontier.heat_eq_failure_tax]
  exact collapse_tax_positive_of_two_or_more hLive

theorem heat_zero_of_singleton
    (frontier : FiniteErasureFrontier)
    (hLive : frontier.liveBranches = 1) :
    frontier.heatLowerBound = 0 := by
  rw [frontier.heat_eq_failure_tax, hLive]
  rfl

end FiniteErasureFrontier

structure RefinementHeatWitness where
  event : RefinementEvent
  widthDecreased : Q.lt event.posterior_bracket.width event.prior_bracket.width = true
  landauerBound : 1 <= refinement_cost event

namespace RefinementHeatWitness

def heatLowerBound (witness : RefinementHeatWitness) : Nat :=
  refinement_cost witness.event

theorem heat_at_least_one
    (witness : RefinementHeatWitness) :
    1 <= witness.heatLowerBound := by
  unfold heatLowerBound
  exact witness.landauerBound

theorem heat_positive
    (witness : RefinementHeatWitness) :
    0 < witness.heatLowerBound := by
  exact Nat.lt_of_lt_of_le (Nat.zero_lt_one) witness.heat_at_least_one

end RefinementHeatWitness

def phiRefinementEvent01 : RefinementEvent :=
  { prior_bracket := phiStep 0
  , posterior_bracket := phiStep 1
  , is_refinement := phi_refines_0_1 }

theorem phi_refinement_01_cost_one :
    refinement_cost phiRefinementEvent01 = 1 := by
  native_decide

theorem phi_refinement_01_matches_binary_erasure :
    refinement_cost phiRefinementEvent01 =
      deterministicCollapseBuleCost 2 := by
  native_decide

theorem information_gain_matches_phi_refinement_cost :
    let evt := phiRefinementEvent01
    information_gain evt = refinement_cost evt := by
  native_decide

theorem sliver_rejects_zero_cost_infinite_precision :
    isInfinitePrecision CausalDiamond.runtimeSliverDiamond = false := by
  exact runtime_myth_of_infinite_free_precision

structure LandauerBuleyCertificate where
  frontier : FiniteErasureFrontier
  refinement : RefinementHeatWitness

namespace LandauerBuleyCertificate

def totalHeatLowerBound (certificate : LandauerBuleyCertificate) : Nat :=
  certificate.frontier.heatLowerBound + certificate.refinement.heatLowerBound

theorem total_heat_dominates_frontier
    (certificate : LandauerBuleyCertificate) :
    certificate.frontier.heatLowerBound <= certificate.totalHeatLowerBound := by
  unfold totalHeatLowerBound
  exact Nat.le_add_right certificate.frontier.heatLowerBound
    certificate.refinement.heatLowerBound

theorem total_heat_dominates_refinement
    (certificate : LandauerBuleyCertificate) :
    certificate.refinement.heatLowerBound <= certificate.totalHeatLowerBound := by
  unfold totalHeatLowerBound
  exact Nat.le_add_left certificate.refinement.heatLowerBound
    certificate.frontier.heatLowerBound

theorem total_heat_positive_of_refinement
    (certificate : LandauerBuleyCertificate) :
    0 < certificate.totalHeatLowerBound := by
  exact Nat.lt_of_lt_of_le
    certificate.refinement.heat_positive
    certificate.total_heat_dominates_refinement

end LandauerBuleyCertificate

def binaryPhiCertificate : LandauerBuleyCertificate :=
  { frontier :=
      { liveBranches := 2
      , erasedBranches := 1
      , collapseWitness := by rfl }
  , refinement :=
      { event := phiRefinementEvent01
      , widthDecreased := by native_decide
      , landauerBound := by native_decide } }

theorem binary_phi_certificate_total_heat_positive :
    0 < binaryPhiCertificate.totalHeatLowerBound := by
  exact binaryPhiCertificate.total_heat_positive_of_refinement

theorem binary_phi_certificate_total_heat_two :
    binaryPhiCertificate.totalHeatLowerBound = 2 := by
  native_decide

theorem landauer_buley_restored_master :
    deterministicCollapseBuleCost 2 = 1 /\
      refinement_cost phiRefinementEvent01 = 1 /\
      information_gain phiRefinementEvent01 = refinement_cost phiRefinementEvent01 /\
      isInfinitePrecision CausalDiamond.runtimeSliverDiamond = false /\
      binaryPhiCertificate.totalHeatLowerBound = 2 := by
  exact
    ⟨ by native_decide
    , phi_refinement_01_cost_one
    , information_gain_matches_phi_refinement_cost
    , sliver_rejects_zero_cost_infinite_precision
    , binary_phi_certificate_total_heat_two
    ⟩

end LandauerBuley

end Gnosis
