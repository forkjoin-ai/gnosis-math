import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraTrialSteadfastnessWitness

/-!
# Quran 2:153-157, Al-Baqara -- Trial, Steadfastness, Return

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1467-1486`.

This bounded witness tracks the trial and steadfastness unit:

  * believers seek help through steadfastness and prayer;
  * God is with the steadfast;
  * those killed in God's cause are not to be called dead;
  * testing comes through fear, hunger, property loss, life loss, and crop loss;
  * steadfast people receive good news;
  * calamity is answered by belonging to God and returning to Him;
  * blessings, mercy, and guidance close the unit.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive TrialSteadfastnessMoment
  | helpThroughSteadfastnessPrayer
  | godWithSteadfast
  | killedNotDead
  | trialsNamed
  | goodNewsToSteadfast
  | belongAndReturn
  | blessingsMercyGuidance
deriving DecidableEq, Repr

def trialSteadfastnessMoments : List TrialSteadfastnessMoment :=
  [ TrialSteadfastnessMoment.helpThroughSteadfastnessPrayer
  , TrialSteadfastnessMoment.godWithSteadfast
  , TrialSteadfastnessMoment.killedNotDead
  , TrialSteadfastnessMoment.trialsNamed
  , TrialSteadfastnessMoment.goodNewsToSteadfast
  , TrialSteadfastnessMoment.belongAndReturn
  , TrialSteadfastnessMoment.blessingsMercyGuidance
  ]

structure SteadfastHelpPattern where
  believersAddressed : Bool
  helpThroughSteadfastness : Bool
  helpThroughPrayer : Bool
  godWithSteadfast : Bool
  killedInGodCause : Bool
  notDead : Bool
  aliveButUnrealized : Bool
deriving DecidableEq, Repr

def steadfastHelpPattern : SteadfastHelpPattern where
  believersAddressed := true
  helpThroughSteadfastness := true
  helpThroughPrayer := true
  godWithSteadfast := true
  killedInGodCause := true
  notDead := true
  aliveButUnrealized := true

structure TrialReturnPattern where
  fearTest : Bool
  hungerTest : Bool
  propertyLossTest : Bool
  lifeLossTest : Bool
  cropLossTest : Bool
  goodNewsGiven : Bool
  calamityAfflicts : Bool
  belongToGod : Bool
  returnToGod : Bool
deriving DecidableEq, Repr

def trialReturnPattern : TrialReturnPattern where
  fearTest := true
  hungerTest := true
  propertyLossTest := true
  lifeLossTest := true
  cropLossTest := true
  goodNewsGiven := true
  calamityAfflicts := true
  belongToGod := true
  returnToGod := true

structure MercyGuidancePattern where
  blessingsFromLord : Bool
  mercyFromLord : Bool
  rightlyGuided : Bool
deriving DecidableEq, Repr

def mercyGuidancePattern : MercyGuidancePattern where
  blessingsFromLord := true
  mercyFromLord := true
  rightlyGuided := true

theorem quran_al_baqara_trial_steadfastness_witness :
    trialSteadfastnessMoments.length = 7
    ∧ trialSteadfastnessMoments.head? =
        some TrialSteadfastnessMoment.helpThroughSteadfastnessPrayer
    ∧ trialSteadfastnessMoments.getLast? =
        some TrialSteadfastnessMoment.blessingsMercyGuidance
    ∧ steadfastHelpPattern.believersAddressed = true
    ∧ steadfastHelpPattern.helpThroughSteadfastness = true
    ∧ steadfastHelpPattern.helpThroughPrayer = true
    ∧ steadfastHelpPattern.godWithSteadfast = true
    ∧ steadfastHelpPattern.killedInGodCause = true
    ∧ steadfastHelpPattern.notDead = true
    ∧ steadfastHelpPattern.aliveButUnrealized = true
    ∧ trialReturnPattern.fearTest = true
    ∧ trialReturnPattern.hungerTest = true
    ∧ trialReturnPattern.propertyLossTest = true
    ∧ trialReturnPattern.lifeLossTest = true
    ∧ trialReturnPattern.cropLossTest = true
    ∧ trialReturnPattern.calamityAfflicts = true
    ∧ trialReturnPattern.belongToGod = true
    ∧ trialReturnPattern.returnToGod = true
    ∧ mercyGuidancePattern.blessingsFromLord = true
    ∧ mercyGuidancePattern.mercyFromLord = true
    ∧ mercyGuidancePattern.rightlyGuided = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraTrialSteadfastnessWitness
end Gnosis.Witnesses.Islam
