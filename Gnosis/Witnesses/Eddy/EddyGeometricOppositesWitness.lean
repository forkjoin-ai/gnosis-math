import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyGeometricOppositesWitness

/-!
# Science and Health, Chapter X -- Geometric Opposites

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:11780-11980`.

Bounded section: 282:3-286:30. Eddy uses circle/sphere versus straight line
as a formal non-coincidence witness: eternal Mind and temporary material
existence do not unite in figure or fact. The passage then applies that
separation to causation, sense, individuality, salvation, and counterfeit
material thought.
-/

inductive GeometricOppositeMoment where
  | circleFiguresInfinite
  | lineFiguresFinite
  | mindAndMaterialExistenceNeverUnite
  | curveLineNoAdjustment
  | matterNoPlaceInSpirit
  | truthNoHomeInError
  | oppositesCannotMingle
  | matterNoInherentPower
  | truthNotInvertedFromError
  | mindSourceOfMovement
  | materialEffectsAreMortalMindStates
  | prevalentTheoriesConfuseLifeWithMaterialLife
  | geometryAnalogyRequiresAccurateStatement
  | infiniteCannotDwellInFiniteness
  | materialRecognitionOfSpiritNegated
  | sensesCannotProveGod
  | realSensesSpiritual
  | communicationGodToIdea
  | materialPersonalityCounterfeit
  | salvationThroughReformNotPardonOnly
  | understandingBetterThanBelief
  | physicalCausationPutAside
  | spiritualUniverseGood
  | temporalThoughtsCounterfeit
  | errorSelfDestroysByClaimingTruth
deriving DecidableEq, Repr

def geometricOppositeTrace : List GeometricOppositeMoment :=
  [ GeometricOppositeMoment.circleFiguresInfinite
  , GeometricOppositeMoment.lineFiguresFinite
  , GeometricOppositeMoment.mindAndMaterialExistenceNeverUnite
  , GeometricOppositeMoment.curveLineNoAdjustment
  , GeometricOppositeMoment.matterNoPlaceInSpirit
  , GeometricOppositeMoment.truthNoHomeInError
  , GeometricOppositeMoment.oppositesCannotMingle
  , GeometricOppositeMoment.matterNoInherentPower
  , GeometricOppositeMoment.truthNotInvertedFromError
  , GeometricOppositeMoment.mindSourceOfMovement
  , GeometricOppositeMoment.materialEffectsAreMortalMindStates
  , GeometricOppositeMoment.prevalentTheoriesConfuseLifeWithMaterialLife
  , GeometricOppositeMoment.geometryAnalogyRequiresAccurateStatement
  , GeometricOppositeMoment.infiniteCannotDwellInFiniteness
  , GeometricOppositeMoment.materialRecognitionOfSpiritNegated
  , GeometricOppositeMoment.sensesCannotProveGod
  , GeometricOppositeMoment.realSensesSpiritual
  , GeometricOppositeMoment.communicationGodToIdea
  , GeometricOppositeMoment.materialPersonalityCounterfeit
  , GeometricOppositeMoment.salvationThroughReformNotPardonOnly
  , GeometricOppositeMoment.understandingBetterThanBelief
  , GeometricOppositeMoment.physicalCausationPutAside
  , GeometricOppositeMoment.spiritualUniverseGood
  , GeometricOppositeMoment.temporalThoughtsCounterfeit
  , GeometricOppositeMoment.errorSelfDestroysByClaimingTruth
  ]

structure GeometricOpposites where
  circleLineNonCoincidence : Bool
  spiritMatterNoSharedPlace : Bool
  truthErrorNoSharedHome : Bool
  matterNoInherentPower : Bool
  mindSourceOfMovement : Bool
  materialSenseRecognitionNegated : Bool
  godToIdeaCommunication : Bool
  materialPersonalityCounterfeit : Bool
  reformOverPardonOnly : Bool
  beliefInsufficientForScience : Bool
  errorSelfDestructive : Bool
deriving DecidableEq, Repr

def geometricOpposites : GeometricOpposites where
  circleLineNonCoincidence := true
  spiritMatterNoSharedPlace := true
  truthErrorNoSharedHome := true
  matterNoInherentPower := true
  mindSourceOfMovement := true
  materialSenseRecognitionNegated := true
  godToIdeaCommunication := true
  materialPersonalityCounterfeit := true
  reformOverPardonOnly := true
  beliefInsufficientForScience := true
  errorSelfDestructive := true

theorem eddy_geometric_opposites_witness :
    geometricOppositeTrace.length = 25
    ∧ geometricOppositeTrace.head? =
      some GeometricOppositeMoment.circleFiguresInfinite
    ∧ geometricOppositeTrace.getLast? =
      some GeometricOppositeMoment.errorSelfDestroysByClaimingTruth
    ∧ geometricOpposites.circleLineNonCoincidence = true
    ∧ geometricOpposites.spiritMatterNoSharedPlace = true
    ∧ geometricOpposites.truthErrorNoSharedHome = true
    ∧ geometricOpposites.matterNoInherentPower = true
    ∧ geometricOpposites.mindSourceOfMovement = true
    ∧ geometricOpposites.materialSenseRecognitionNegated = true
    ∧ geometricOpposites.godToIdeaCommunication = true
    ∧ geometricOpposites.materialPersonalityCounterfeit = true
    ∧ geometricOpposites.reformOverPardonOnly = true
    ∧ geometricOpposites.beliefInsufficientForScience = true
    ∧ geometricOpposites.errorSelfDestructive = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyGeometricOppositesWitness
end Gnosis.Witnesses.Eddy
