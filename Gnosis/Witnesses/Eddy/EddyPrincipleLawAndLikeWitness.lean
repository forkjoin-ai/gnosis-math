import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPrincipleLawAndLikeWitness

/-!
# Science and Health, Chapter X -- Principle, Law, and Like Producing Like

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:11397-11580`.

Bounded section: 272:19-277:11. This unit follows the discipleship bridge by
requiring Principle to interpret the universe. Its negative witness is sharp:
material law cannot annul spiritual law, mixed Mind/matter partnership is an
imaginary firm, and non-intelligence cannot generate intelligence.
-/

inductive PrincipleLawMoment where
  | spiritualizedLifeAttestsScience
  | principleMustInterpretUniverse
  | matterClaimsContraryToGod
  | noMaterialTruth
  | divineScienceReversesSense
  | materialLawsNeverMakeWhole
  | spiritualLawNotAnnulled
  | jesusOvercomesMaterialLawClaims
  | truthLoveAntidoteMentalMiasma
  | senseKnowledgeTemporal
  | spiritIdeasNotMaterialInferences
  | physicalSensesManifestMortalBelief
  | noHalfWayPosition
  | mindMatterPartnershipImaginary
  | spiritStartingPointAllInAll
  | divineSynonymsUnify
  | allRealityManifestationOfMind
  | oneMindUnfoldsHealing
  | harmonyRealDiscordUnreal
  | spiritualUnderstandingDestroysMaterialBelief
  | likeProducesLike
  | nonIntelligenceCannotSpringFromIntelligence
  | matterNeverProducesMind
deriving DecidableEq, Repr

def principleLawTrace : List PrincipleLawMoment :=
  [ PrincipleLawMoment.spiritualizedLifeAttestsScience
  , PrincipleLawMoment.principleMustInterpretUniverse
  , PrincipleLawMoment.matterClaimsContraryToGod
  , PrincipleLawMoment.noMaterialTruth
  , PrincipleLawMoment.divineScienceReversesSense
  , PrincipleLawMoment.materialLawsNeverMakeWhole
  , PrincipleLawMoment.spiritualLawNotAnnulled
  , PrincipleLawMoment.jesusOvercomesMaterialLawClaims
  , PrincipleLawMoment.truthLoveAntidoteMentalMiasma
  , PrincipleLawMoment.senseKnowledgeTemporal
  , PrincipleLawMoment.spiritIdeasNotMaterialInferences
  , PrincipleLawMoment.physicalSensesManifestMortalBelief
  , PrincipleLawMoment.noHalfWayPosition
  , PrincipleLawMoment.mindMatterPartnershipImaginary
  , PrincipleLawMoment.spiritStartingPointAllInAll
  , PrincipleLawMoment.divineSynonymsUnify
  , PrincipleLawMoment.allRealityManifestationOfMind
  , PrincipleLawMoment.oneMindUnfoldsHealing
  , PrincipleLawMoment.harmonyRealDiscordUnreal
  , PrincipleLawMoment.spiritualUnderstandingDestroysMaterialBelief
  , PrincipleLawMoment.likeProducesLike
  , PrincipleLawMoment.nonIntelligenceCannotSpringFromIntelligence
  , PrincipleLawMoment.matterNeverProducesMind
  ]

structure PrincipleLawAndLike where
  principleInterpretsUniverse : Bool
  matterContraryToGod : Bool
  noMaterialTruth : Bool
  scienceReversesSense : Bool
  noMaterialLawAgainstSpiritualLaw : Bool
  materialKnowledgeTemporal : Bool
  ideasBornOfSpirit : Bool
  noHalfWayPosition : Bool
  mindMatterPartnershipDestroyed : Bool
  allInAllStartingPoint : Bool
  oneMindHeals : Bool
  likeProducesLike : Bool
  matterNeverProducesMind : Bool
deriving DecidableEq, Repr

def principleLawAndLike : PrincipleLawAndLike where
  principleInterpretsUniverse := true
  matterContraryToGod := true
  noMaterialTruth := true
  scienceReversesSense := true
  noMaterialLawAgainstSpiritualLaw := true
  materialKnowledgeTemporal := true
  ideasBornOfSpirit := true
  noHalfWayPosition := true
  mindMatterPartnershipDestroyed := true
  allInAllStartingPoint := true
  oneMindHeals := true
  likeProducesLike := true
  matterNeverProducesMind := true

theorem eddy_principle_law_and_like_witness :
    principleLawTrace.length = 23
    ∧ principleLawTrace.head? =
      some PrincipleLawMoment.spiritualizedLifeAttestsScience
    ∧ principleLawTrace.getLast? =
      some PrincipleLawMoment.matterNeverProducesMind
    ∧ principleLawAndLike.principleInterpretsUniverse = true
    ∧ principleLawAndLike.matterContraryToGod = true
    ∧ principleLawAndLike.noMaterialTruth = true
    ∧ principleLawAndLike.scienceReversesSense = true
    ∧ principleLawAndLike.noMaterialLawAgainstSpiritualLaw = true
    ∧ principleLawAndLike.materialKnowledgeTemporal = true
    ∧ principleLawAndLike.ideasBornOfSpirit = true
    ∧ principleLawAndLike.noHalfWayPosition = true
    ∧ principleLawAndLike.mindMatterPartnershipDestroyed = true
    ∧ principleLawAndLike.allInAllStartingPoint = true
    ∧ principleLawAndLike.oneMindHeals = true
    ∧ principleLawAndLike.likeProducesLike = true
    ∧ principleLawAndLike.matterNeverProducesMind = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPrincipleLawAndLikeWitness
end Gnosis.Witnesses.Eddy
