import Gnosis.Witnesses.Bible.Galatians.GalatiansBondwomanFreewomanWitness
import Gnosis.Witnesses.Bible.Torah.GenesisHagarSarahPromiseWitness

namespace Gnosis.Witnesses.Bible.Torah
namespace TorahGalatiansHagarSarahTandemWitness

/-!
# Torah/Galatians Tandem -- Hagar/Sarah Source and Bondwoman/Freewoman Reading

Genesis owns the Hagar/Sarah and Ishmael/Isaac source events. Galatians owns the
allegorical covenant projection. This bridge records the semantic overlap
without duplicating source coverage.

No `sorry`, no new `axiom`.
-/

structure HagarSarahCoverageBoundary where
  genesisOwnsHouseholdSource : Bool := true
  genesisOwnsIsaacHeirBoundary : Bool := true
  galatiansOwnsAllegoricalProjection : Bool := true
  duplicateCoverageRejected : Bool := true
deriving DecidableEq, Repr

def hagarSarahCoverageBoundary : HagarSarahCoverageBoundary := {}

def hagarSarahNoDuplicateCoverage (b : HagarSarahCoverageBoundary) : Prop :=
  b.genesisOwnsHouseholdSource = true ∧
  b.genesisOwnsIsaacHeirBoundary = true ∧
  b.galatiansOwnsAllegoricalProjection = true ∧
  b.duplicateCoverageRejected = true

theorem torah_galatians_hagar_sarah_no_duplicate :
    hagarSarahNoDuplicateCoverage hagarSarahCoverageBoundary := by
  unfold hagarSarahNoDuplicateCoverage hagarSarahCoverageBoundary
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem torah_galatians_hagar_sarah_tandem_witness :
    GenesisHagarSarahPromiseWitness.hagarIshmaelAnchor
      GenesisHagarSarahPromiseWitness.hagarIshmaelSource ∧
    GenesisHagarSarahPromiseWitness.isaacHeirAnchor
      GenesisHagarSarahPromiseWitness.isaacHeirBoundary ∧
    Galatians.GalatiansBondwomanFreewomanWitness.covenantTopologyWitness
      Galatians.GalatiansBondwomanFreewomanWitness.twoSonsAllegory ∧
    Galatians.GalatiansBondwomanFreewomanWitness.promiseFreedomWitness
      Galatians.GalatiansBondwomanFreewomanWitness.promiseFreedomChildren ∧
    hagarSarahNoDuplicateCoverage hagarSarahCoverageBoundary := by
  exact ⟨GenesisHagarSarahPromiseWitness.genesis_hagar_ishmael_anchor,
    GenesisHagarSarahPromiseWitness.genesis_isaac_heir_anchor,
    Galatians.GalatiansBondwomanFreewomanWitness.galatians_covenant_topology,
    Galatians.GalatiansBondwomanFreewomanWitness.galatians_promise_freedom,
    torah_galatians_hagar_sarah_no_duplicate⟩

end TorahGalatiansHagarSarahTandemWitness
end Gnosis.Witnesses.Bible.Torah
