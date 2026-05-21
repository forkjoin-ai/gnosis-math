import Gnosis.Witnesses.Chaldean.AssyrianMonumentalContinuityWitness
import Gnosis.Witnesses.Chaldean.ErrorToTruthFragmentMethodWitness
import Gnosis.Witnesses.Chaldean.IzdubarErechReturnCityBoundaryWitness

namespace Gnosis.Witnesses.Chaldean
namespace IzdubarNimrodEmpireDissolutionWitness

/-!
# Izdubar-Nimrod Empire Dissolution Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, conclusion
and Chapter XI Nimrod/Izdubar synthesis.

Smith's identification of Izdubar with Nimrod remains theory-bound, but the
sovereignty topology is clear: hunter, deliverer of country, slayer of usurper,
empire extender, Assyrian colonizer, and Nineveh founder. The sovereign node
does not preserve the empire-body after death. The empire falls apart, while
Assyrian colonies grow powerful and Babylonia revives under Urukh of Ur.

That is the carrier lesson: a personal empire can dissolve while cities,
colonies, walls, seals, and later monumental programs preserve the witness. The
king-body fails; the built and image ledgers keep carrying.

Chapter XI adds the stronger city-list shape: Izdubar makes the first empire in
Asia from petty Euphrates-valley kingdoms; its center matches Shinar/Babel,
Erech, Accad, and Calneh; the Assyrian extension names Nineveh, Calah,
Rehobothair, and Resen. The point is not only a person; it is an empire graph.

No `sorry`, no new `axiom`.
-/

structure IzdubarNimrodIdentityReserve where
  identificationProbableNotClosed : Bool := true
  hazardousChronologyReserveInherited : Bool := true
  biblicalNimrodComparisonNamed : Bool := true
  sourceTheoryUsefulButRevisable : Bool := true
  topologySurvivesNameUncertainty : Bool := true
deriving DecidableEq, Repr

def izdubarNimrodIdentityReserve : IzdubarNimrodIdentityReserve := {}

def nimrodIdentityHeldUnderReserve (i : IzdubarNimrodIdentityReserve) : Prop :=
  i.identificationProbableNotClosed = true ∧
  i.hazardousChronologyReserveInherited = true ∧
  i.biblicalNimrodComparisonNamed = true ∧
  i.sourceTheoryUsefulButRevisable = true ∧
  i.topologySurvivesNameUncertainty = true

structure SovereignHunterLiberator where
  beginsAsHunter : Bool := true
  deliversCountryFromForeignDominion : Bool := true
  slaysUsurper : Bool := true
  becomesLeaderAndKing : Bool := true
  countryUnificationFunction : Bool := true
deriving DecidableEq, Repr

def sovereignHunterLiberator : SovereignHunterLiberator := {}

def hunterLiberatorKernel (s : SovereignHunterLiberator) : Prop :=
  s.beginsAsHunter = true ∧
  s.deliversCountryFromForeignDominion = true ∧
  s.slaysUsurper = true ∧
  s.becomesLeaderAndKing = true ∧
  s.countryUnificationFunction = true

structure ShinarEmpireGraph where
  pettyKingdomsUnified : Bool := true
  firstEmpireInAsiaClaimed : Bool := true
  shinarCenterNamed : Bool := true
  babelNamed : Bool := true
  erechNamed : Bool := true
  accadNamed : Bool := true
  calnehNamed : Bool := true
  cityListFunctionsAsEmpireGraph : Bool := true
deriving DecidableEq, Repr

def shinarEmpireGraph : ShinarEmpireGraph := {}

def shinarCityEmpireGraph (s : ShinarEmpireGraph) : Prop :=
  s.pettyKingdomsUnified = true ∧
  s.firstEmpireInAsiaClaimed = true ∧
  s.shinarCenterNamed = true ∧
  s.babelNamed = true ∧
  s.erechNamed = true ∧
  s.accadNamed = true ∧
  s.calnehNamed = true ∧
  s.cityListFunctionsAsEmpireGraph = true

structure AssyrianColonizationExtension where
  empireExtendedIntoAssyria : Bool := true
  assyriaColonized : Bool := true
  ninevehFounded : Bool := true
  calahFounded : Bool := true
  rehobothairFounded : Bool := true
  resenFounded : Bool := true
  cityCarrierOutlivesFounder : Bool := true
  colonyCarrierOutlivesEmpireBody : Bool := true
deriving DecidableEq, Repr

def assyrianColonizationExtension : AssyrianColonizationExtension := {}

def colonyCityCarrierExtension (c : AssyrianColonizationExtension) : Prop :=
  c.empireExtendedIntoAssyria = true ∧
  c.assyriaColonized = true ∧
  c.ninevehFounded = true ∧
  c.calahFounded = true ∧
  c.rehobothairFounded = true ∧
  c.resenFounded = true ∧
  c.cityCarrierOutlivesFounder = true ∧
  c.colonyCarrierOutlivesEmpireBody = true

structure EmpireDissolutionAfterDeath where
  empireFallsToPiecesAtDeath : Bool := true
  assyrianColoniesGrowPowerful : Bool := true
  babyloniaRevivesAfterBriefPeriod : Bool := true
  urukhOfUrMarksRevival : Bool := true
  monumentalEraCommences : Bool := true
  sovereigntyNotSameAsCarrierContinuity : Bool := true
deriving DecidableEq, Repr

def empireDissolutionAfterDeath : EmpireDissolutionAfterDeath := {}

def empireBodyDissolvesCarrierPersists (e : EmpireDissolutionAfterDeath) : Prop :=
  e.empireFallsToPiecesAtDeath = true ∧
  e.assyrianColoniesGrowPowerful = true ∧
  e.babyloniaRevivesAfterBriefPeriod = true ∧
  e.urukhOfUrMarksRevival = true ∧
  e.monumentalEraCommences = true ∧
  e.sovereigntyNotSameAsCarrierContinuity = true

theorem izdubar_nimrod_identity_held_under_reserve :
    nimrodIdentityHeldUnderReserve izdubarNimrodIdentityReserve := by
  unfold nimrodIdentityHeldUnderReserve izdubarNimrodIdentityReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_hunter_liberator_kernel :
    hunterLiberatorKernel sovereignHunterLiberator := by
  unfold hunterLiberatorKernel sovereignHunterLiberator
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_shinar_city_empire_graph :
    shinarCityEmpireGraph shinarEmpireGraph := by
  unfold shinarCityEmpireGraph shinarEmpireGraph
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_colony_city_carrier_extension :
    colonyCityCarrierExtension assyrianColonizationExtension := by
  unfold colonyCityCarrierExtension assyrianColonizationExtension
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_empire_body_dissolves_carrier_persists :
    empireBodyDissolvesCarrierPersists empireDissolutionAfterDeath := by
  unfold empireBodyDissolvesCarrierPersists empireDissolutionAfterDeath
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_inherits_error_to_truth_reserve :
    ErrorToTruthFragmentMethodWitness.boundedHazardousTheory
      ErrorToTruthFragmentMethodWitness.hazardousTheoryReserve ∧
    nimrodIdentityHeldUnderReserve izdubarNimrodIdentityReserve := by
  exact ⟨ErrorToTruthFragmentMethodWitness.error_to_truth_bounded_hazardous_theory,
    izdubar_nimrod_identity_held_under_reserve⟩

theorem izdubar_inherits_city_boundary_return :
    IzdubarErechReturnCityBoundaryWitness.erechBoundaryMeasured
      IzdubarErechReturnCityBoundaryWitness.cityBoundarySurvey ∧
    colonyCityCarrierExtension assyrianColonizationExtension := by
  exact ⟨IzdubarErechReturnCityBoundaryWitness.izdubar_erech_boundary_measured,
    izdubar_colony_city_carrier_extension⟩

theorem izdubar_inherits_monumental_continuity :
    AssyrianMonumentalContinuityWitness.oralToMonumentalCarrierShift
      AssyrianMonumentalContinuityWitness.monumentalEraTransition ∧
    AssyrianMonumentalContinuityWitness.monumentalImagesCarryLegends
      AssyrianMonumentalContinuityWitness.assyrianRevivalImageProgram ∧
    empireBodyDissolvesCarrierPersists empireDissolutionAfterDeath := by
  exact ⟨AssyrianMonumentalContinuityWitness.assyrian_oral_to_monumental_carrier_shift,
    AssyrianMonumentalContinuityWitness.assyrian_monumental_images_carry_legends,
    izdubar_empire_body_dissolves_carrier_persists⟩

theorem izdubar_nimrod_empire_dissolution_witness :
    nimrodIdentityHeldUnderReserve izdubarNimrodIdentityReserve ∧
    hunterLiberatorKernel sovereignHunterLiberator ∧
    shinarCityEmpireGraph shinarEmpireGraph ∧
    colonyCityCarrierExtension assyrianColonizationExtension ∧
    empireBodyDissolvesCarrierPersists empireDissolutionAfterDeath := by
  exact ⟨izdubar_nimrod_identity_held_under_reserve,
    izdubar_hunter_liberator_kernel,
    izdubar_shinar_city_empire_graph,
    izdubar_colony_city_carrier_extension,
    izdubar_empire_body_dissolves_carrier_persists⟩

end IzdubarNimrodEmpireDissolutionWitness
end Gnosis.Witnesses.Chaldean
