import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyMindMatterOppositionWitness

/-!
# Science and Health, Chapter X -- Mind/Matter Opposition

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:11203-11283`.

Bounded section: 268:1-270:12. The passage opens "Science of Being" by
turning materialistic challenge into a layer test: semi-metaphysical systems
mix Mind and matter, therefore remain divided. The counterproof is the fork
itself: if matter and Mind are opposites, a coherent basis cannot grant both
the same reality and power.
-/

inductive ScienceOfBeingOpeningMoment where
  | materialThoughtFindsUsefulWonders
  | thoughtRisesTowardSpiritualCause
  | materialBasisYieldsToMetaphysicalBasis
  | materialisticHypothesesChallengeMetaphysics
  | semiMetaphysicalSystemsGiveNoAid
  | mixedMindMatterSystemsArePantheistic
  | serpentPhilosophyMinglesGoodAndEvil
  | jesusDemonstrationSiftsGoodFromEvil
  | metaphysicsAbovePhysics
  | divineMindOnlyBasis
  | materialSenseFoundationsAreReeds
  | matterEverythingTheoryRejected
  | mindMatterCooperationTheoryRejected
  | oneBasisForkMindOrMatter
  | onePowerEnablesScientificConclusion
deriving DecidableEq, Repr

def scienceOfBeingOpeningTrace : List ScienceOfBeingOpeningMoment :=
  [ ScienceOfBeingOpeningMoment.materialThoughtFindsUsefulWonders
  , ScienceOfBeingOpeningMoment.thoughtRisesTowardSpiritualCause
  , ScienceOfBeingOpeningMoment.materialBasisYieldsToMetaphysicalBasis
  , ScienceOfBeingOpeningMoment.materialisticHypothesesChallengeMetaphysics
  , ScienceOfBeingOpeningMoment.semiMetaphysicalSystemsGiveNoAid
  , ScienceOfBeingOpeningMoment.mixedMindMatterSystemsArePantheistic
  , ScienceOfBeingOpeningMoment.serpentPhilosophyMinglesGoodAndEvil
  , ScienceOfBeingOpeningMoment.jesusDemonstrationSiftsGoodFromEvil
  , ScienceOfBeingOpeningMoment.metaphysicsAbovePhysics
  , ScienceOfBeingOpeningMoment.divineMindOnlyBasis
  , ScienceOfBeingOpeningMoment.materialSenseFoundationsAreReeds
  , ScienceOfBeingOpeningMoment.matterEverythingTheoryRejected
  , ScienceOfBeingOpeningMoment.mindMatterCooperationTheoryRejected
  , ScienceOfBeingOpeningMoment.oneBasisForkMindOrMatter
  , ScienceOfBeingOpeningMoment.onePowerEnablesScientificConclusion
  ]

structure MindMatterOpposition where
  materialChallengeAcknowledged : Bool
  semiMetaphysicalMixtureRejected : Bool
  pantheisticHouseDivided : Bool
  matterExcludedFromMetaphysicalPremises : Bool
  divineMindAsOnlyBasis : Bool
  materialSenseFoundationRejected : Bool
  matterEverythingRejected : Bool
  mindMatterCooperationRejected : Bool
  oppositesCannotBothBeReal : Bool
  onePowerRequiredForScience : Bool
deriving DecidableEq, Repr

def mindMatterOpposition : MindMatterOpposition where
  materialChallengeAcknowledged := true
  semiMetaphysicalMixtureRejected := true
  pantheisticHouseDivided := true
  matterExcludedFromMetaphysicalPremises := true
  divineMindAsOnlyBasis := true
  materialSenseFoundationRejected := true
  matterEverythingRejected := true
  mindMatterCooperationRejected := true
  oppositesCannotBothBeReal := true
  onePowerRequiredForScience := true

theorem eddy_mind_matter_opposition_witness :
    scienceOfBeingOpeningTrace.length = 15
    ∧ scienceOfBeingOpeningTrace.head? =
      some ScienceOfBeingOpeningMoment.materialThoughtFindsUsefulWonders
    ∧ scienceOfBeingOpeningTrace.getLast? =
      some ScienceOfBeingOpeningMoment.onePowerEnablesScientificConclusion
    ∧ mindMatterOpposition.materialChallengeAcknowledged = true
    ∧ mindMatterOpposition.semiMetaphysicalMixtureRejected = true
    ∧ mindMatterOpposition.pantheisticHouseDivided = true
    ∧ mindMatterOpposition.matterExcludedFromMetaphysicalPremises = true
    ∧ mindMatterOpposition.divineMindAsOnlyBasis = true
    ∧ mindMatterOpposition.materialSenseFoundationRejected = true
    ∧ mindMatterOpposition.matterEverythingRejected = true
    ∧ mindMatterOpposition.mindMatterCooperationRejected = true
    ∧ mindMatterOpposition.oppositesCannotBothBeReal = true
    ∧ mindMatterOpposition.onePowerRequiredForScience = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyMindMatterOppositionWitness
end Gnosis.Witnesses.Eddy
