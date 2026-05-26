import Gnosis.CalatravaBridge

/-
  BridgeLoadPath.lean
  ===================

  Named load-path surface for the Time Bridge. This is still not a stamped
  design: the numbers are finite witnesses. The important upgrade is structural:
  soundness depends on named dead, live pedestrian, and wind loads plus member
  capacities, not on anonymous demand numbers.

  Init-only surface: closed arithmetic uses `decide`; structural equalities use
  `rfl`; no Mathlib, no `omega`.
-/

namespace GnosisMath
namespace BridgeLoadPath

open GnosisMath.CalatravaBridge
open GnosisMath.Phyle

/-- Named service load cases for a pedestrian bridge. -/
structure BridgeLoadCases where
  deadLoad : Nat
  livePedestrianLoad : Nat
  windLoad : Nat

/-- Named member capacities for the main load-bearing systems. -/
structure MemberCapacities where
  deckCapacity : Nat
  stayCapacity : Nat
  mastCapacity : Nat
  foundationCapacity : Nat

/-- Integer safety factor shared by the finite load-path check. -/
structure SafetyPolicy where
  safetyFactor : Nat

/-- Deck demand carries dead load plus pedestrian live load. -/
def deckDemand (loads : BridgeLoadCases) : Nat :=
  loads.deadLoad + loads.livePedestrianLoad

/-- Stay demand carries the deck demand plus wind load. -/
def stayDemand (loads : BridgeLoadCases) : Nat :=
  deckDemand loads + loads.windLoad

/-- Mast demand carries the fan stay demand plus wind load. -/
def mastDemand (loads : BridgeLoadCases) : Nat :=
  stayDemand loads + loads.windLoad

/-- Foundation demand carries the mast demand plus dead load. -/
def foundationDemand (loads : BridgeLoadCases) : Nat :=
  mastDemand loads + loads.deadLoad

/-- Factored capacity check for one named member system. -/
def demandFitsCapacity (policy : SafetyPolicy) (demand capacity : Nat) : Prop :=
  demand * policy.safetyFactor ≤ capacity

/--
  Named load-path certificate. Every member check is stated against a named
  demand derived from dead/live/wind load cases.
-/
structure BridgeLoadPathCertificate where
  loads : BridgeLoadCases
  capacities : MemberCapacities
  policy : SafetyPolicy
  deckSafe :
    demandFitsCapacity policy (deckDemand loads) capacities.deckCapacity
  staysSafe :
    demandFitsCapacity policy (stayDemand loads) capacities.stayCapacity
  mastSafe :
    demandFitsCapacity policy (mastDemand loads) capacities.mastCapacity
  foundationSafe :
    demandFitsCapacity policy (foundationDemand loads) capacities.foundationCapacity
  phyleUsed : deckCellBars = phyleBars
  phyleStrictlyStronger : oldTriangleBars < phyleBars

/-- A finite toy load set: dead, pedestrian live, and wind load. -/
def toyPedestrianLoads : BridgeLoadCases where
  deadLoad := 10
  livePedestrianLoad := 20
  windLoad := 5

/-- A finite toy capacity set sized against the toy load path. -/
def toySteelCapacities : MemberCapacities where
  deckCapacity := 80
  stayCapacity := 100
  mastCapacity := 110
  foundationCapacity := 130

/-- A conservative finite toy policy: factor demands by two. -/
def factorTwoPolicy : SafetyPolicy where
  safetyFactor := 2

theorem toy_deck_demand_closed : deckDemand toyPedestrianLoads = 30 := by
  unfold deckDemand toyPedestrianLoads
  decide

theorem toy_stay_demand_closed : stayDemand toyPedestrianLoads = 35 := by
  unfold stayDemand deckDemand toyPedestrianLoads
  decide

theorem toy_mast_demand_closed : mastDemand toyPedestrianLoads = 40 := by
  unfold mastDemand stayDemand deckDemand toyPedestrianLoads
  decide

theorem toy_foundation_demand_closed : foundationDemand toyPedestrianLoads = 50 := by
  unfold foundationDemand mastDemand stayDemand deckDemand toyPedestrianLoads
  decide

theorem toy_deck_safe :
    demandFitsCapacity factorTwoPolicy
      (deckDemand toyPedestrianLoads) toySteelCapacities.deckCapacity := by
  unfold demandFitsCapacity factorTwoPolicy deckDemand toyPedestrianLoads toySteelCapacities
  decide

theorem toy_stays_safe :
    demandFitsCapacity factorTwoPolicy
      (stayDemand toyPedestrianLoads) toySteelCapacities.stayCapacity := by
  unfold demandFitsCapacity factorTwoPolicy stayDemand deckDemand toyPedestrianLoads toySteelCapacities
  decide

theorem toy_mast_safe :
    demandFitsCapacity factorTwoPolicy
      (mastDemand toyPedestrianLoads) toySteelCapacities.mastCapacity := by
  unfold demandFitsCapacity factorTwoPolicy mastDemand stayDemand deckDemand toyPedestrianLoads toySteelCapacities
  decide

theorem toy_foundation_safe :
    demandFitsCapacity factorTwoPolicy
      (foundationDemand toyPedestrianLoads) toySteelCapacities.foundationCapacity := by
  unfold demandFitsCapacity factorTwoPolicy foundationDemand mastDemand stayDemand deckDemand
    toyPedestrianLoads toySteelCapacities
  decide

/-- A finite toy load-path certificate. -/
def toyBridgeLoadPathCertificate : BridgeLoadPathCertificate where
  loads := toyPedestrianLoads
  capacities := toySteelCapacities
  policy := factorTwoPolicy
  deckSafe := toy_deck_safe
  staysSafe := toy_stays_safe
  mastSafe := toy_mast_safe
  foundationSafe := toy_foundation_safe
  phyleUsed := deck_cell_uses_phyle
  phyleStrictlyStronger := Phyle.phyle_inverts_old_triangle

/--
  The load-path bundle exposes each named load case and every named member
  capacity check.
-/
theorem bridge_load_path_bundle (cert : BridgeLoadPathCertificate) :
    demandFitsCapacity cert.policy (deckDemand cert.loads) cert.capacities.deckCapacity ∧
    demandFitsCapacity cert.policy (stayDemand cert.loads) cert.capacities.stayCapacity ∧
    demandFitsCapacity cert.policy (mastDemand cert.loads) cert.capacities.mastCapacity ∧
    demandFitsCapacity cert.policy (foundationDemand cert.loads) cert.capacities.foundationCapacity ∧
    deckCellBars = phyleBars ∧
    oldTriangleBars < phyleBars :=
  ⟨cert.deckSafe, cert.staysSafe, cert.mastSafe, cert.foundationSafe,
   cert.phyleUsed, cert.phyleStrictlyStronger⟩

end BridgeLoadPath
end GnosisMath
