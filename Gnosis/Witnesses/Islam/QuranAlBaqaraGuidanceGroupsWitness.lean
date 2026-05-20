import Gnosis.ArchaeologicalInfinityAccess

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

Sat/unseen reading:

The passage is a classifier, not a mere catalogue of religious groups. It answers
Al-Fatiha's guidance request by showing that guidance becomes visible only with
negative samples beside it: mindful reception, sealed refusal, and hypocritical
simulation. That makes this opening an archaeological access witness. The Sat is
not a flat "guidance exists" claim; it is the phase split where one path receives
guidance and two failed branches expose the boundary conditions.

Uses `Gnosis.ArchaeologicalInfinityAccess`. Zero new `axiom`, no Mathlib.
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

/-- Archaeological access over the opening classifier: one positive path, two gap paths. -/
def baqaraGuidanceAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 2:1-20 classifies guidance by positive and negative samples"
    positiveSamples := [1]
    negativeSamples := [2, 3] }

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

/-- The two failed groups are useful negative witnesses, not expendable scenery. -/
def negativeGroupsExposeGuidanceBoundary
    (sealed : SealedDisbelieverPattern)
    (hypocrite : HypocritePattern) : Prop :=
  sealed.warningNoDifference = true ∧
  sealed.heartsSealed = true ∧
  hypocrite.reallyDoNotBelieve = true ∧
  hypocrite.causeCorruptionWhileClaimingRepair = true ∧
  hypocrite.darknessDeafDumbBlind = true

theorem baqara_negative_groups_expose_boundary :
    negativeGroupsExposeGuidanceBoundary sealedDisbelieverPattern hypocritePattern := by
  unfold negativeGroupsExposeGuidanceBoundary sealedDisbelieverPattern hypocritePattern
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem baqara_guidance_access_archaeological :
    baqaraGuidanceAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

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
    ∧ hypocritePattern.darknessDeafDumbBlind = true
    ∧ negativeGroupsExposeGuidanceBoundary sealedDisbelieverPattern hypocritePattern
    ∧ baqaraGuidanceAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
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
  · exact baqara_negative_groups_expose_boundary
  · exact baqara_guidance_access_archaeological

end QuranAlBaqaraGuidanceGroupsWitness
end Gnosis.Witnesses.Islam
