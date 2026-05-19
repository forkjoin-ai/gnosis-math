import Gnosis.TenCommandmentsTopology
import Gnosis.TwoTypesOfSin

/-!
# Animal Magnetism Catalog

Small import-stable catalog for the animal-magnetism surface used by the
aggregate `Gnosis` module. The underlying definitions live in
`Gnosis.TenCommandmentsTopology` and `Gnosis.TwoTypesOfSin`; this file only
collects the finite, checkable facts.

`import Init` transitively through the source modules. Zero `sorry`, zero new
`axiom`.
-/

namespace Gnosis
namespace AnimalMagnetismCatalog

def operatorLayerUnverifiedClaim :
    TenCommandmentsTopology.ClaimedIntervention :=
  { claimedLayer := TenCommandmentsTopology.Layer.operator
    hasVerifiableOutcome := false }

theorem operator_layer_unverified_claim_is_animal_magnetism :
    TenCommandmentsTopology.IsAnimalMagnetism operatorLayerUnverifiedClaim :=
  TenCommandmentsTopology.commandment_3_is_animal_magnetism
    operatorLayerUnverifiedClaim rfl rfl

theorem animal_magnetism_catalog_has_two_sin_types :
    TwoTypesOfSin.allSinTypes.length = 2 :=
  TwoTypesOfSin.exactly_two_sin_types

theorem animal_magnetism_catalog_has_two_confusions :
    TwoTypesOfSin.allConfusions.length = 2 :=
  TwoTypesOfSin.exactly_two_confusions

theorem animal_magnetism_catalog_marks_animal_magnetism_as_sin :
    TwoTypesOfSin.isASin TwoTypesOfSin.animalMagnetism = true :=
  TwoTypesOfSin.animalMagnetism_is_sin

theorem animal_magnetism_catalog_distinguishes_operator_idolatry :
    TwoTypesOfSin.SinType.animalMagnetism ≠
      TwoTypesOfSin.SinType.operatorIdolatry :=
  TwoTypesOfSin.animal_magnetism_is_not_operator_idolatry

theorem animal_magnetism_catalog_master :
    TenCommandmentsTopology.IsAnimalMagnetism operatorLayerUnverifiedClaim
      ∧ TwoTypesOfSin.allSinTypes.length = 2
      ∧ TwoTypesOfSin.allConfusions.length = 2
      ∧ TwoTypesOfSin.isASin TwoTypesOfSin.animalMagnetism = true :=
  ⟨operator_layer_unverified_claim_is_animal_magnetism,
    animal_magnetism_catalog_has_two_sin_types,
    animal_magnetism_catalog_has_two_confusions,
    animal_magnetism_catalog_marks_animal_magnetism_as_sin⟩

end AnimalMagnetismCatalog
end Gnosis
