import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticeDominionLawWitness

/-!
# Science and Health, Chapter XII -- Dominion over Material Law

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:15680-16020`.

Bounded section: 378:18-386:27. This practice unit denies disease any
intelligence or jurisdiction, treats fear as the danger behind supposed material
law, rebukes excessive hygiene, and frames climate, exposure, food, sleep, and
corporeal penalties as belief-governed rather than matter-governed.
-/

inductive DominionLawMoment where
  | hypnotismDruggingErroneousBases
  | diseaseNotIntelligence
  | godGivesMatterNoDisablingPower
  | mindJurisdictionAllCausation
  | imaginationCanKillByBelief
  | feverPicturesDrawnByMortalMind
  | truthAlwaysVictor
  | contendingForDiseaseDeniesMind
  | fearEffectIllustratesIllusion
  | divineMindProducesHealth
  | materialLawRenderedVoidByLife
  | fearOfDangerInducesEffects
  | onlyMoralSpiritualLawReal
  | godNotAuthorBarbarousCodes
  | dominionRequiresMindNotMatter
  | sicknessBanishedAsOutlaw
  | jesusAnnulsSupposedMatterLaws
  | hygieneAttentionExcessive
  | medicalTheoryHindersChildlikeReception
  | cleanMindKeepsBody
  | tobaccoBeliefIllusive
  | movementCureMistake
  | materialPenaltyAnnulledByProtest
  | exposureFearSubsidanceHeals
  | philanthropySupportedByDivineLaw
  | honestDutyNoHarm
  | sleepFoodBeliefSelfLaw
  | bodyInformationIllusion
  | climateEffectsFollowBelief
  | erroneousDispatchShowsBeliefCause
deriving DecidableEq, Repr

def dominionLawTrace : List DominionLawMoment :=
  [ DominionLawMoment.hypnotismDruggingErroneousBases
  , DominionLawMoment.diseaseNotIntelligence
  , DominionLawMoment.godGivesMatterNoDisablingPower
  , DominionLawMoment.mindJurisdictionAllCausation
  , DominionLawMoment.imaginationCanKillByBelief
  , DominionLawMoment.feverPicturesDrawnByMortalMind
  , DominionLawMoment.truthAlwaysVictor
  , DominionLawMoment.contendingForDiseaseDeniesMind
  , DominionLawMoment.fearEffectIllustratesIllusion
  , DominionLawMoment.divineMindProducesHealth
  , DominionLawMoment.materialLawRenderedVoidByLife
  , DominionLawMoment.fearOfDangerInducesEffects
  , DominionLawMoment.onlyMoralSpiritualLawReal
  , DominionLawMoment.godNotAuthorBarbarousCodes
  , DominionLawMoment.dominionRequiresMindNotMatter
  , DominionLawMoment.sicknessBanishedAsOutlaw
  , DominionLawMoment.jesusAnnulsSupposedMatterLaws
  , DominionLawMoment.hygieneAttentionExcessive
  , DominionLawMoment.medicalTheoryHindersChildlikeReception
  , DominionLawMoment.cleanMindKeepsBody
  , DominionLawMoment.tobaccoBeliefIllusive
  , DominionLawMoment.movementCureMistake
  , DominionLawMoment.materialPenaltyAnnulledByProtest
  , DominionLawMoment.exposureFearSubsidanceHeals
  , DominionLawMoment.philanthropySupportedByDivineLaw
  , DominionLawMoment.honestDutyNoHarm
  , DominionLawMoment.sleepFoodBeliefSelfLaw
  , DominionLawMoment.bodyInformationIllusion
  , DominionLawMoment.climateEffectsFollowBelief
  , DominionLawMoment.erroneousDispatchShowsBeliefCause
  ]

structure PracticeDominionLaw where
  diseaseNoIntelligence : Bool
  mindJurisdiction : Bool
  fearInducesEffects : Bool
  materialLawsVoid : Bool
  hygieneCanHinder : Bool
  corporealPenaltyBelief : Bool
  climateBeliefGoverned : Bool
  griefBeliefCause : Bool
deriving DecidableEq, Repr

def practiceDominionLaw : PracticeDominionLaw where
  diseaseNoIntelligence := true
  mindJurisdiction := true
  fearInducesEffects := true
  materialLawsVoid := true
  hygieneCanHinder := true
  corporealPenaltyBelief := true
  climateBeliefGoverned := true
  griefBeliefCause := true

theorem eddy_practice_dominion_law_witness :
    dominionLawTrace.length = 30
    ∧ dominionLawTrace.head? =
      some DominionLawMoment.hypnotismDruggingErroneousBases
    ∧ dominionLawTrace.getLast? =
      some DominionLawMoment.erroneousDispatchShowsBeliefCause
    ∧ practiceDominionLaw.diseaseNoIntelligence = true
    ∧ practiceDominionLaw.mindJurisdiction = true
    ∧ practiceDominionLaw.fearInducesEffects = true
    ∧ practiceDominionLaw.materialLawsVoid = true
    ∧ practiceDominionLaw.hygieneCanHinder = true
    ∧ practiceDominionLaw.corporealPenaltyBelief = true
    ∧ practiceDominionLaw.climateBeliefGoverned = true
    ∧ practiceDominionLaw.griefBeliefCause = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticeDominionLawWitness
end Gnosis.Witnesses.Eddy
