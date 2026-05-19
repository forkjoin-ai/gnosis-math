import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticeMentalImageWitness

/-!
# Science and Health, Chapter XII -- Mental Images and Practice Boundaries

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:16380-16680`.

Bounded section: 395:24-402:30. This practice unit follows the danger of
holding disease as real into the positive method of effacing disease-images,
reversing accident-belief, binding mortal mind as the controlling "strong man,"
and preserving a practical boundary around surgery until Mind's supremacy is
more broadly acknowledged.
-/

inductive MentalImageMoment where
  | diseaseRealityFastensCase
  | brainLobesCannotKill
  | diseaseImagesEffaced
  | illnessTalkAvoided
  | materialSenseRefuted
  | beliefPowerExplained
  | diseaseDreamBroken
  | wrongMentalInfluenceInjures
  | accidentBeliefReversed
  | mindNotSkullCompressed
  | jesusNamesConcessionally
  | jesusOftenHealsUnnamed
  | homoeopathyFaithEffect
  | appetiteDiseaseInMortalMind
  | blindFaithTemporary
  | mindScienceRadicalCure
  | materialCombinationCannotAct
  | mortalMindTelegraphy
  | mortalMindNotEntity
  | strongManBoundFirst
  | diseaseImageEradicated
  | thoughtCreatesSuffering
  | sinfulThoughtNotHealer
  | chemicalizationTransformsError
  | medicineEffectMental
  | surgeryBoundaryRetained
  | mentalSurgeryRecords
  | lifeIndestructible
  | bodyManifestsMortalBelief
  | mesmerismBeliefWithoutCause
deriving DecidableEq, Repr

def mentalImageTrace : List MentalImageMoment :=
  [ MentalImageMoment.diseaseRealityFastensCase
  , MentalImageMoment.brainLobesCannotKill
  , MentalImageMoment.diseaseImagesEffaced
  , MentalImageMoment.illnessTalkAvoided
  , MentalImageMoment.materialSenseRefuted
  , MentalImageMoment.beliefPowerExplained
  , MentalImageMoment.diseaseDreamBroken
  , MentalImageMoment.wrongMentalInfluenceInjures
  , MentalImageMoment.accidentBeliefReversed
  , MentalImageMoment.mindNotSkullCompressed
  , MentalImageMoment.jesusNamesConcessionally
  , MentalImageMoment.jesusOftenHealsUnnamed
  , MentalImageMoment.homoeopathyFaithEffect
  , MentalImageMoment.appetiteDiseaseInMortalMind
  , MentalImageMoment.blindFaithTemporary
  , MentalImageMoment.mindScienceRadicalCure
  , MentalImageMoment.materialCombinationCannotAct
  , MentalImageMoment.mortalMindTelegraphy
  , MentalImageMoment.mortalMindNotEntity
  , MentalImageMoment.strongManBoundFirst
  , MentalImageMoment.diseaseImageEradicated
  , MentalImageMoment.thoughtCreatesSuffering
  , MentalImageMoment.sinfulThoughtNotHealer
  , MentalImageMoment.chemicalizationTransformsError
  , MentalImageMoment.medicineEffectMental
  , MentalImageMoment.surgeryBoundaryRetained
  , MentalImageMoment.mentalSurgeryRecords
  , MentalImageMoment.lifeIndestructible
  , MentalImageMoment.bodyManifestsMortalBelief
  , MentalImageMoment.mesmerismBeliefWithoutCause
  ]

structure PracticeMentalImage where
  diseaseImageMustBeEffaced : Bool
  accidentBeliefReversible : Bool
  mortalMindAndMatterOneFalseComplex : Bool
  faithCanShiftBeliefTemporarily : Bool
  strongManIsMortalMind : Bool
  chemicalizationSurfacesError : Bool
  surgeryBoundaryPragmatic : Bool
  lifeIndestructible : Bool
  mesmerismNotScientific : Bool
deriving DecidableEq, Repr

def practiceMentalImage : PracticeMentalImage where
  diseaseImageMustBeEffaced := true
  accidentBeliefReversible := true
  mortalMindAndMatterOneFalseComplex := true
  faithCanShiftBeliefTemporarily := true
  strongManIsMortalMind := true
  chemicalizationSurfacesError := true
  surgeryBoundaryPragmatic := true
  lifeIndestructible := true
  mesmerismNotScientific := true

theorem eddy_practice_mental_image_witness :
    mentalImageTrace.length = 30
    ∧ mentalImageTrace.head? =
      some MentalImageMoment.diseaseRealityFastensCase
    ∧ mentalImageTrace.getLast? =
      some MentalImageMoment.mesmerismBeliefWithoutCause
    ∧ practiceMentalImage.diseaseImageMustBeEffaced = true
    ∧ practiceMentalImage.accidentBeliefReversible = true
    ∧ practiceMentalImage.mortalMindAndMatterOneFalseComplex = true
    ∧ practiceMentalImage.faithCanShiftBeliefTemporarily = true
    ∧ practiceMentalImage.strongManIsMortalMind = true
    ∧ practiceMentalImage.chemicalizationSurfacesError = true
    ∧ practiceMentalImage.surgeryBoundaryPragmatic = true
    ∧ practiceMentalImage.lifeIndestructible = true
    ∧ practiceMentalImage.mesmerismNotScientific = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticeMentalImageWitness
end Gnosis.Witnesses.Eddy
