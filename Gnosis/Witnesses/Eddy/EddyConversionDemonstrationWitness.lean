import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyConversionDemonstrationWitness

/-!
# Science and Health, Chapter X -- Conversion, Demonstration, and Error

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:13580-13726`.

Bounded section: 326:16-329:30. This unit names right motive as the start,
uses Saul/Paul as conversion witness, rejects fear-punishment reform, insists
that Jesus' healing promise is perpetual, and defines mercy's pardon as the
destruction of error.
-/

inductive ConversionDemonstrationMoment where
  | rightMotiveStartsScience
  | saulConvertedBySpiritualSense
  | reformByNoPleasureInEvil
  | divineMindDestroysFalseAppetites
  | maliceLosesPleasureInWickedness
  | sinEscapedByCeasingSin
  | demandsSeemPeremptoryToSense
  | moralCourageRequired
  | reasonAwakensMoralObligation
  | errorsNotDestroyedByBelief
  | trueUnderstandingDestroysDelusions
  | healingPromiseDormantInHistory
  | jesusPromisePerpetual
  | littleUnderstandingProvesWhole
  | useOnlyWhatUnderstood
  | faithProvedByDemonstration
  | avoidOccasionUntilAble
  | principleImperativeNotMocked
  | pardonDestroysError
  | resistanceWeakensAsErrorYielded
deriving DecidableEq, Repr

def conversionDemonstrationTrace : List ConversionDemonstrationMoment :=
  [ ConversionDemonstrationMoment.rightMotiveStartsScience
  , ConversionDemonstrationMoment.saulConvertedBySpiritualSense
  , ConversionDemonstrationMoment.reformByNoPleasureInEvil
  , ConversionDemonstrationMoment.divineMindDestroysFalseAppetites
  , ConversionDemonstrationMoment.maliceLosesPleasureInWickedness
  , ConversionDemonstrationMoment.sinEscapedByCeasingSin
  , ConversionDemonstrationMoment.demandsSeemPeremptoryToSense
  , ConversionDemonstrationMoment.moralCourageRequired
  , ConversionDemonstrationMoment.reasonAwakensMoralObligation
  , ConversionDemonstrationMoment.errorsNotDestroyedByBelief
  , ConversionDemonstrationMoment.trueUnderstandingDestroysDelusions
  , ConversionDemonstrationMoment.healingPromiseDormantInHistory
  , ConversionDemonstrationMoment.jesusPromisePerpetual
  , ConversionDemonstrationMoment.littleUnderstandingProvesWhole
  , ConversionDemonstrationMoment.useOnlyWhatUnderstood
  , ConversionDemonstrationMoment.faithProvedByDemonstration
  , ConversionDemonstrationMoment.avoidOccasionUntilAble
  , ConversionDemonstrationMoment.principleImperativeNotMocked
  , ConversionDemonstrationMoment.pardonDestroysError
  , ConversionDemonstrationMoment.resistanceWeakensAsErrorYielded
  ]

structure ConversionDemonstration where
  motiveBeginsScience : Bool
  conversionChangesOutlook : Bool
  reformNeedsNoPleasureInEvil : Bool
  sinEscapedByCeasing : Bool
  promisePerpetual : Bool
  demonstrationRequired : Bool
  principleImperative : Bool
  pardonAsErrorDestruction : Bool
deriving DecidableEq, Repr

def conversionDemonstration : ConversionDemonstration where
  motiveBeginsScience := true
  conversionChangesOutlook := true
  reformNeedsNoPleasureInEvil := true
  sinEscapedByCeasing := true
  promisePerpetual := true
  demonstrationRequired := true
  principleImperative := true
  pardonAsErrorDestruction := true

theorem eddy_conversion_demonstration_witness :
    conversionDemonstrationTrace.length = 20
    ∧ conversionDemonstrationTrace.head? =
      some ConversionDemonstrationMoment.rightMotiveStartsScience
    ∧ conversionDemonstrationTrace.getLast? =
      some ConversionDemonstrationMoment.resistanceWeakensAsErrorYielded
    ∧ conversionDemonstration.motiveBeginsScience = true
    ∧ conversionDemonstration.conversionChangesOutlook = true
    ∧ conversionDemonstration.reformNeedsNoPleasureInEvil = true
    ∧ conversionDemonstration.sinEscapedByCeasing = true
    ∧ conversionDemonstration.promisePerpetual = true
    ∧ conversionDemonstration.demonstrationRequired = true
    ∧ conversionDemonstration.principleImperative = true
    ∧ conversionDemonstration.pardonAsErrorDestruction = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyConversionDemonstrationWitness
end Gnosis.Witnesses.Eddy
