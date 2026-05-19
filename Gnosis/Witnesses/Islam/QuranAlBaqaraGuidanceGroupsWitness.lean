import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraGuidanceGroupsWitness

/-!
# Quran 2:1-20, Al-Baqara -- Guidance Groups

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:921-964`.

This bounded witness tracks the opening response to Al-Fatiha's guidance request:

  * the Scripture has no doubt and contains guidance for the mindful;
  * the mindful believe in the unseen, keep prayer, give from provision, believe
    in revelation, and have firm faith in the Hereafter;
  * disbelievers are not changed by warning, with hearts/ears sealed and eyes covered;
  * hypocrites claim belief while deceiving only themselves;
  * their corruption, mockery, bad trade, and darkness images are named.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive BaqaraOpeningGroup
  | mindfulGuided
  | sealedDisbelievers
  | hypocritesDiseased
deriving DecidableEq, Repr

def baqaraOpeningGroups : List BaqaraOpeningGroup :=
  [ BaqaraOpeningGroup.mindfulGuided
  , BaqaraOpeningGroup.sealedDisbelievers
  , BaqaraOpeningGroup.hypocritesDiseased
  ]

structure ScriptureGuidancePattern where
  scriptureNoDoubt : Bool
  guidanceForMindful : Bool
  believeUnseen : Bool
  keepPrayer : Bool
  giveFromProvision : Bool
  believeRevelationSentDownAndBefore : Bool
  firmFaithHereafter : Bool
  followingLordGuidance : Bool
  prosper : Bool
deriving DecidableEq, Repr

def scriptureGuidancePattern : ScriptureGuidancePattern where
  scriptureNoDoubt := true
  guidanceForMindful := true
  believeUnseen := true
  keepPrayer := true
  giveFromProvision := true
  believeRevelationSentDownAndBefore := true
  firmFaithHereafter := true
  followingLordGuidance := true
  prosper := true

structure SealedDisbelieverPattern where
  warningNoDifference : Bool
  willNotBelieve : Bool
  heartsSealed : Bool
  earsSealed : Bool
  eyesCovered : Bool
  greatTorment : Bool
deriving DecidableEq, Repr

def sealedDisbelieverPattern : SealedDisbelieverPattern where
  warningNoDifference := true
  willNotBelieve := true
  heartsSealed := true
  earsSealed := true
  eyesCovered := true
  greatTorment := true

structure HypocritePattern where
  claimBeliefGodLastDay : Bool
  reallyDoNotBelieve : Bool
  deceiveOnlyThemselves : Bool
  diseaseInHearts : Bool
  causeCorruptionWhileClaimingRepair : Bool
  mockBelieversWithEvilOnes : Bool
  boughtErrorForGuidance : Bool
  darknessDeafDumbBlind : Bool
  stormFearAndWandering : Bool
deriving DecidableEq, Repr

def hypocritePattern : HypocritePattern where
  claimBeliefGodLastDay := true
  reallyDoNotBelieve := true
  deceiveOnlyThemselves := true
  diseaseInHearts := true
  causeCorruptionWhileClaimingRepair := true
  mockBelieversWithEvilOnes := true
  boughtErrorForGuidance := true
  darknessDeafDumbBlind := true
  stormFearAndWandering := true

theorem quran_al_baqara_guidance_groups_witness :
    baqaraOpeningGroups.length = 3
    ∧ baqaraOpeningGroups.head? = some BaqaraOpeningGroup.mindfulGuided
    ∧ baqaraOpeningGroups.getLast? = some BaqaraOpeningGroup.hypocritesDiseased
    ∧ scriptureGuidancePattern.scriptureNoDoubt = true
    ∧ scriptureGuidancePattern.guidanceForMindful = true
    ∧ scriptureGuidancePattern.believeUnseen = true
    ∧ scriptureGuidancePattern.keepPrayer = true
    ∧ scriptureGuidancePattern.giveFromProvision = true
    ∧ scriptureGuidancePattern.firmFaithHereafter = true
    ∧ scriptureGuidancePattern.prosper = true
    ∧ sealedDisbelieverPattern.warningNoDifference = true
    ∧ sealedDisbelieverPattern.heartsSealed = true
    ∧ sealedDisbelieverPattern.greatTorment = true
    ∧ hypocritePattern.claimBeliefGodLastDay = true
    ∧ hypocritePattern.reallyDoNotBelieve = true
    ∧ hypocritePattern.diseaseInHearts = true
    ∧ hypocritePattern.causeCorruptionWhileClaimingRepair = true
    ∧ hypocritePattern.boughtErrorForGuidance = true
    ∧ hypocritePattern.darknessDeafDumbBlind = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end QuranAlBaqaraGuidanceGroupsWitness
end Gnosis.Witnesses.Islam
