import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyReflectionIdentityWitness

/-!
# Science and Health, Chapter X -- Reflection and Spiritual Identity

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:12480-12780`.

Bounded section: 299:3-306:18. This unit centers reflection: angels guide
upward, material knowledge is known by its fruit, temporal and eternal do not
touch, man is image/idea rather than material substance, and Love cannot be
separated from its manifestation.
-/

inductive ReflectionIdentityMoment where
  | angelsGuideToPrinciple
  | materialKnowledgeKnownByFruit
  | truthNeverDestroysGodsIdea
  | materialManMirage
  | scientificStatementProvesNewMan
  | taresAndWheatNeverReallyMingle
  | soulNotInMatter
  | universeReflectsMind
  | spiritualManSubstantial
  | firstCommandmentRejectsOtherSubstance
  | invertedImageFromMaterialSense
  | identityNotLost
  | manForeverHarmoniousImmortal
  | governedBySoulNotSense
  | reproductionReflectsCreativePower
  | matterPropagationRejected
  | mixedSpiritualMaterialEvolutionContradictsTruth
  | errorDefinedAsMixedManCreatorClaim
  | spiritualManCannotBeSeparated
  | loveCannotLoseManifestation
  | harmonyNaturalDiscordUnreal
  | musicAnalogyRequiresUnderstanding
  | reflectionNotCorporeality
  | genderMortalMindQuality
  | mortalStagesDreamNotDivine
  | resurrectionNotMatterProducingSpirit
  | lifeDemonstratesLife
  | noSeparationOfSoulAndRepresentative
deriving DecidableEq, Repr

def reflectionIdentityTrace : List ReflectionIdentityMoment :=
  [ ReflectionIdentityMoment.angelsGuideToPrinciple
  , ReflectionIdentityMoment.materialKnowledgeKnownByFruit
  , ReflectionIdentityMoment.truthNeverDestroysGodsIdea
  , ReflectionIdentityMoment.materialManMirage
  , ReflectionIdentityMoment.scientificStatementProvesNewMan
  , ReflectionIdentityMoment.taresAndWheatNeverReallyMingle
  , ReflectionIdentityMoment.soulNotInMatter
  , ReflectionIdentityMoment.universeReflectsMind
  , ReflectionIdentityMoment.spiritualManSubstantial
  , ReflectionIdentityMoment.firstCommandmentRejectsOtherSubstance
  , ReflectionIdentityMoment.invertedImageFromMaterialSense
  , ReflectionIdentityMoment.identityNotLost
  , ReflectionIdentityMoment.manForeverHarmoniousImmortal
  , ReflectionIdentityMoment.governedBySoulNotSense
  , ReflectionIdentityMoment.reproductionReflectsCreativePower
  , ReflectionIdentityMoment.matterPropagationRejected
  , ReflectionIdentityMoment.mixedSpiritualMaterialEvolutionContradictsTruth
  , ReflectionIdentityMoment.errorDefinedAsMixedManCreatorClaim
  , ReflectionIdentityMoment.spiritualManCannotBeSeparated
  , ReflectionIdentityMoment.loveCannotLoseManifestation
  , ReflectionIdentityMoment.harmonyNaturalDiscordUnreal
  , ReflectionIdentityMoment.musicAnalogyRequiresUnderstanding
  , ReflectionIdentityMoment.reflectionNotCorporeality
  , ReflectionIdentityMoment.genderMortalMindQuality
  , ReflectionIdentityMoment.mortalStagesDreamNotDivine
  , ReflectionIdentityMoment.resurrectionNotMatterProducingSpirit
  , ReflectionIdentityMoment.lifeDemonstratesLife
  , ReflectionIdentityMoment.noSeparationOfSoulAndRepresentative
  ]

structure ReflectionIdentity where
  temporalEternalDoNotTouch : Bool
  soulNotInMatter : Bool
  manAsImageIdea : Bool
  identityNotLost : Bool
  matterPropagationRejected : Bool
  spiritualManInseparable : Bool
  loveKeepsManifestation : Bool
  harmonyNatural : Bool
  reflectionNotCorporeal : Bool
  lifeDemonstratesLife : Bool
deriving DecidableEq, Repr

def reflectionIdentity : ReflectionIdentity where
  temporalEternalDoNotTouch := true
  soulNotInMatter := true
  manAsImageIdea := true
  identityNotLost := true
  matterPropagationRejected := true
  spiritualManInseparable := true
  loveKeepsManifestation := true
  harmonyNatural := true
  reflectionNotCorporeal := true
  lifeDemonstratesLife := true

theorem eddy_reflection_identity_witness :
    reflectionIdentityTrace.length = 28
    ∧ reflectionIdentityTrace.head? =
      some ReflectionIdentityMoment.angelsGuideToPrinciple
    ∧ reflectionIdentityTrace.getLast? =
      some ReflectionIdentityMoment.noSeparationOfSoulAndRepresentative
    ∧ reflectionIdentity.temporalEternalDoNotTouch = true
    ∧ reflectionIdentity.soulNotInMatter = true
    ∧ reflectionIdentity.manAsImageIdea = true
    ∧ reflectionIdentity.identityNotLost = true
    ∧ reflectionIdentity.matterPropagationRejected = true
    ∧ reflectionIdentity.spiritualManInseparable = true
    ∧ reflectionIdentity.loveKeepsManifestation = true
    ∧ reflectionIdentity.harmonyNatural = true
    ∧ reflectionIdentity.reflectionNotCorporeal = true
    ∧ reflectionIdentity.lifeDemonstratesLife = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyReflectionIdentityWitness
end Gnosis.Witnesses.Eddy
