import Gnosis.BridgeLoadPath

/-
  CalatravaBridgeSoundness.lean
  ==============================

  A Rustic Church safety gate for the Calatrava-style bridge motif. This file
  does not stamp a physical bridge. It only states the minimal honest shape of a
  physical certificate: a currently available material class plus a named
  load-path certificate with dead, pedestrian live, and wind load cases.

  Init-only surface: closed arithmetic uses `decide`; structural equalities use
  `rfl`; no Mathlib, no `omega`.
-/

namespace GnosisMath
namespace CalatravaBridgeSoundness

open GnosisMath.CalatravaBridge
open GnosisMath.BridgeLoadPath
open GnosisMath.Phyle

/--
  Material classes that are available in current bridge practice:

  * structural steel: ordinary primary bridge material;
  * reinforced concrete: ordinary deck/substructure material;
  * ultra-high-performance concrete: documented for bridge applications and
    prefabricated bridge element connections;
  * fiber-reinforced polymer: available for decks/repair/strengthening, but not
    treated here as the default primary Calatrava-style mast/stay material.
-/
inductive AvailableBridgeMaterial where
  | structuralSteel
  | reinforcedConcrete
  | ultraHighPerformanceConcrete
  | fiberReinforcedPolymer
deriving DecidableEq

/-- Steel is admitted as an available primary bridge material. -/
def primaryMaterialAdmitted : AvailableBridgeMaterial → Bool
  | AvailableBridgeMaterial.structuralSteel => true
  | AvailableBridgeMaterial.reinforcedConcrete => true
  | AvailableBridgeMaterial.ultraHighPerformanceConcrete => true
  | AvailableBridgeMaterial.fiberReinforcedPolymer => false

/-- FRP is admitted here as secondary deck/repair/strengthening material only. -/
def secondaryMaterialAdmitted : AvailableBridgeMaterial → Bool
  | AvailableBridgeMaterial.fiberReinforcedPolymer => true
  | _ => true

/--
  A pedestrian bridge soundness certificate must check every load path. The
  theorem surface deliberately requires a named load-path certificate; it does
  not infer physical soundness from motif counts.
-/
structure PedestrianBridgeSoundness where
  material : AvailableBridgeMaterial
  primaryMaterialOk : primaryMaterialAdmitted material = true
  loadPath : BridgeLoadPathCertificate

theorem steel_is_primary_material : primaryMaterialAdmitted AvailableBridgeMaterial.structuralSteel = true := rfl

/--
  A finite example that clears the soundness gate under explicit assumptions.
  This is a toy certificate, not a real-world design.
-/
def toySteelPedestrianBridgeSoundness : PedestrianBridgeSoundness where
  material := AvailableBridgeMaterial.structuralSteel
  primaryMaterialOk := steel_is_primary_material
  loadPath := toyBridgeLoadPathCertificate

/--
  The bridge is walkable only relative to an explicit soundness certificate:
  material admission plus named dead/live/wind load-path checks for deck, stays,
  mast, and foundation.
-/
theorem bridge_walkability_requires_soundness (cert : PedestrianBridgeSoundness) :
    primaryMaterialAdmitted cert.material = true ∧
    demandFitsCapacity cert.loadPath.policy
      (deckDemand cert.loadPath.loads) cert.loadPath.capacities.deckCapacity ∧
    demandFitsCapacity cert.loadPath.policy
      (stayDemand cert.loadPath.loads) cert.loadPath.capacities.stayCapacity ∧
    demandFitsCapacity cert.loadPath.policy
      (mastDemand cert.loadPath.loads) cert.loadPath.capacities.mastCapacity ∧
    demandFitsCapacity cert.loadPath.policy
      (foundationDemand cert.loadPath.loads) cert.loadPath.capacities.foundationCapacity ∧
    deckCellBars = phyleBars ∧
    oldTriangleBars < phyleBars :=
  ⟨cert.primaryMaterialOk, cert.loadPath.deckSafe, cert.loadPath.staysSafe,
   cert.loadPath.mastSafe, cert.loadPath.foundationSafe, cert.loadPath.phyleUsed,
   cert.loadPath.phyleStrictlyStronger⟩

/-- FRP alone is not admitted as the primary load path for this bridge gate. -/
theorem frp_not_primary_for_this_gate :
    primaryMaterialAdmitted AvailableBridgeMaterial.fiberReinforcedPolymer = false := rfl

end CalatravaBridgeSoundness
end GnosisMath
