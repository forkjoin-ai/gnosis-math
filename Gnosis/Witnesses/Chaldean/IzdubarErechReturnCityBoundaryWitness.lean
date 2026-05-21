import Gnosis.Witnesses.Chaldean.BabelSpeechConfusionTowerWitness
import Gnosis.Witnesses.Chaldean.IzdubarCleansingCloakHealthWitness

namespace Gnosis.Witnesses.Chaldean
namespace IzdubarErechReturnCityBoundaryWitness

/-!
# Izdubar Erech Return City-Boundary Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter XII,
the return from Hasisadra/Urhamsi to Erech Suburi.

After healing, the text does not end in private recovery. The concealed story
and judgment of the gods are revealed, the account is carried, great stones are
collected and piled, the journey stages return to Erech, and Izdubar asks
Urhamsi to ascend where the wall of Erech will go. The city is measured as
three divisions: city circuit, plantations, and the boundary of the temple of
Nantur, the house of Ishtar.

The topology is reintegration through measured civic boundary. Healing returns
to place only when the account, wall, foundation, city, field, and temple
boundary can be named.

No `sorry`, no new `axiom`.
-/

structure AccountCarrierReturn where
  concealedStoryRevealed : Bool := true
  judgmentOfGodsRelated : Bool := true
  accountTakenInHeart : Bool := true
  greatStonesCollected : Bool := true
  accountCarried : Bool := true
deriving DecidableEq, Repr

def accountCarrierReturn : AccountCarrierReturn := {}

def accountReturnsWithWitness (a : AccountCarrierReturn) : Prop :=
  a.concealedStoryRevealed = true ∧
  a.judgmentOfGodsRelated = true ∧
  a.accountTakenInHeart = true ∧
  a.greatStonesCollected = true ∧
  a.accountCarried = true

structure StagedReturnToErech where
  tenKaspuStageNamed : Bool := true
  twentyKaspuStageNamed : Bool := true
  thirtyKaspuAscentNamed : Bool := true
  shipTouchesShore : Bool := true
  returnToMidstOfErech : Bool := true
deriving DecidableEq, Repr

def stagedReturnToErech : StagedReturnToErech := {}

def stagedReturnWitness (s : StagedReturnToErech) : Prop :=
  s.tenKaspuStageNamed = true ∧
  s.twentyKaspuStageNamed = true ∧
  s.thirtyKaspuAscentNamed = true ∧
  s.shipTouchesShore = true ∧
  s.returnToMidstOfErech = true

structure CityBoundarySurvey where
  wallOfErechNamed : Bool := true
  scatteredCylindersObserved : Bool := true
  casingBricksNotMade : Bool := true
  foundationNotLaidToHeight : Bool := true
  cityCircuitMeasured : Bool := true
  plantationsMeasured : Bool := true
  templeBoundaryMeasured : Bool := true
  threeMeasuresTogether : Bool := true
deriving DecidableEq, Repr

def cityBoundarySurvey : CityBoundarySurvey := {}

def erechBoundaryMeasured (c : CityBoundarySurvey) : Prop :=
  c.wallOfErechNamed = true ∧
  c.scatteredCylindersObserved = true ∧
  c.casingBricksNotMade = true ∧
  c.foundationNotLaidToHeight = true ∧
  c.cityCircuitMeasured = true ∧
  c.plantationsMeasured = true ∧
  c.templeBoundaryMeasured = true ∧
  c.threeMeasuresTogether = true

theorem izdubar_account_returns_with_witness :
    accountReturnsWithWitness accountCarrierReturn := by
  unfold accountReturnsWithWitness accountCarrierReturn
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_staged_return :
    stagedReturnWitness stagedReturnToErech := by
  unfold stagedReturnWitness stagedReturnToErech
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_erech_boundary_measured :
    erechBoundaryMeasured cityBoundarySurvey := by
  unfold erechBoundaryMeasured cityBoundarySurvey
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_inherits_health_return_road :
    IzdubarCleansingCloakHealthWitness.returnRoadRestoresPlace
      IzdubarCleansingCloakHealthWitness.returnRoadReintegration ∧
    stagedReturnWitness stagedReturnToErech ∧
    erechBoundaryMeasured cityBoundarySurvey := by
  exact ⟨IzdubarCleansingCloakHealthWitness.izdubar_return_road_restores_place,
    izdubar_staged_return,
    izdubar_erech_boundary_measured⟩

theorem izdubar_contrasts_babel_boundary_failure :
    BabelSpeechConfusionTowerWitness.namespaceBreakageWitness
      BabelSpeechConfusionTowerWitness.speechConfusionTopology ∧
    erechBoundaryMeasured cityBoundarySurvey := by
  exact ⟨BabelSpeechConfusionTowerWitness.babel_namespace_breakage,
    izdubar_erech_boundary_measured⟩

theorem izdubar_erech_return_city_boundary_witness :
    accountReturnsWithWitness accountCarrierReturn ∧
    stagedReturnWitness stagedReturnToErech ∧
    erechBoundaryMeasured cityBoundarySurvey := by
  exact ⟨izdubar_account_returns_with_witness,
    izdubar_staged_return,
    izdubar_erech_boundary_measured⟩

end IzdubarErechReturnCityBoundaryWitness
end Gnosis.Witnesses.Chaldean
