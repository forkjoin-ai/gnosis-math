import Init

namespace Gnosis.Witnesses.Eddy
namespace EddySubstanceSpiritPantheismWitness

/-!
# Science and Health, Chapter X -- Substance, Spirit, and Pantheism

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:11580-11780`.

Bounded section: 277:12-282:1. The passage tightens the substance argument:
matter is an error in the premise, Spirit has no opposite, pantheism seeks
cause in effect, and the many-minds branch repeats the serpent's finite-god
claim.
-/

inductive SubstanceSpiritMoment where
  | materialityCannotOutcomeFromGood
  | naturalHistoryPreservesKindOrder
  | errorReversesOrder
  | matterErrorOfStatement
  | spiritOnlySubstanceAndConsciousness
  | spiritHasNoOpposite
  | materialSubstanceRequiresTwoEternalCauses
  | matterDoomRejectsMindOrigin
  | ideasTangibleToImmortalConsciousness
  | spiritMatterCannotCooperate
  | pantheismInfectedSystems
  | oneBasisMindNotTwoBases
  | pantheismSeeksCauseInEffect
  | mindProductsBeautifulHarmlessIdeas
  | finiteBeliefCompressesMind
  | manyGodsFromDividedSoul
  | serpentArgumentFiniteForms
  | spiritMatterNoMoreCommingleThanLightDark
  | egoManReflectsEgoGod
  | skullBoneMindMyth
  | oldBeliefMustBeCastOut
deriving DecidableEq, Repr

def substanceSpiritTrace : List SubstanceSpiritMoment :=
  [ SubstanceSpiritMoment.materialityCannotOutcomeFromGood
  , SubstanceSpiritMoment.naturalHistoryPreservesKindOrder
  , SubstanceSpiritMoment.errorReversesOrder
  , SubstanceSpiritMoment.matterErrorOfStatement
  , SubstanceSpiritMoment.spiritOnlySubstanceAndConsciousness
  , SubstanceSpiritMoment.spiritHasNoOpposite
  , SubstanceSpiritMoment.materialSubstanceRequiresTwoEternalCauses
  , SubstanceSpiritMoment.matterDoomRejectsMindOrigin
  , SubstanceSpiritMoment.ideasTangibleToImmortalConsciousness
  , SubstanceSpiritMoment.spiritMatterCannotCooperate
  , SubstanceSpiritMoment.pantheismInfectedSystems
  , SubstanceSpiritMoment.oneBasisMindNotTwoBases
  , SubstanceSpiritMoment.pantheismSeeksCauseInEffect
  , SubstanceSpiritMoment.mindProductsBeautifulHarmlessIdeas
  , SubstanceSpiritMoment.finiteBeliefCompressesMind
  , SubstanceSpiritMoment.manyGodsFromDividedSoul
  , SubstanceSpiritMoment.serpentArgumentFiniteForms
  , SubstanceSpiritMoment.spiritMatterNoMoreCommingleThanLightDark
  , SubstanceSpiritMoment.egoManReflectsEgoGod
  , SubstanceSpiritMoment.skullBoneMindMyth
  , SubstanceSpiritMoment.oldBeliefMustBeCastOut
  ]

structure SubstanceSpiritPantheism where
  matterErrorPremise : Bool
  spiritOnlySubstance : Bool
  spiritHasNoOpposite : Bool
  twoEternalCausesRejected : Bool
  matterNotMindOriginated : Bool
  spiritMatterCannotCooperate : Bool
  pantheismMindInMatterRejected : Bool
  oneBasisMind : Bool
  manyMindsSerpentBranch : Bool
  oldBeliefMustBeCastOut : Bool
deriving DecidableEq, Repr

def substanceSpiritPantheism : SubstanceSpiritPantheism where
  matterErrorPremise := true
  spiritOnlySubstance := true
  spiritHasNoOpposite := true
  twoEternalCausesRejected := true
  matterNotMindOriginated := true
  spiritMatterCannotCooperate := true
  pantheismMindInMatterRejected := true
  oneBasisMind := true
  manyMindsSerpentBranch := true
  oldBeliefMustBeCastOut := true

theorem eddy_substance_spirit_pantheism_witness :
    substanceSpiritTrace.length = 21
    ∧ substanceSpiritTrace.head? =
      some SubstanceSpiritMoment.materialityCannotOutcomeFromGood
    ∧ substanceSpiritTrace.getLast? =
      some SubstanceSpiritMoment.oldBeliefMustBeCastOut
    ∧ substanceSpiritPantheism.matterErrorPremise = true
    ∧ substanceSpiritPantheism.spiritOnlySubstance = true
    ∧ substanceSpiritPantheism.spiritHasNoOpposite = true
    ∧ substanceSpiritPantheism.twoEternalCausesRejected = true
    ∧ substanceSpiritPantheism.matterNotMindOriginated = true
    ∧ substanceSpiritPantheism.spiritMatterCannotCooperate = true
    ∧ substanceSpiritPantheism.pantheismMindInMatterRejected = true
    ∧ substanceSpiritPantheism.oneBasisMind = true
    ∧ substanceSpiritPantheism.manyMindsSerpentBranch = true
    ∧ substanceSpiritPantheism.oldBeliefMustBeCastOut = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddySubstanceSpiritPantheismWitness
end Gnosis.Witnesses.Eddy
