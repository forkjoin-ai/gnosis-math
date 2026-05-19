import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraAdamGuidanceWitness

/-!
# Quran 2:30-39, Al-Baqara -- Adam, Knowledge, Guidance

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1031-1056`.

This bounded witness tracks the Adamic succession unit before the Children of
Israel address begins:

  * God announces a successor on earth;
  * the angels ask about damage and bloodshed while naming praise and holiness;
  * Adam is taught the names and demonstrates them;
  * divine knowledge includes what is hidden, revealed, and concealed;
  * the angels bow while Iblis refuses in arrogance;
  * Adam and his wife are given the garden command, slip, and descend;
  * Adam receives words and repentance is accepted;
  * guidance from God yields no fear or grief for those who follow it;
  * denial of the messages yields the Fire outcome.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive AdamGuidanceMoment
  | successorAnnounced
  | angelicQuestion
  | namesTaught
  | adamNamesDisplayed
  | hiddenRevealedConcealedKnown
  | angelsBowIblisRefuses
  | gardenCommandAndSlip
  | repentanceAccepted
  | guidanceNoFearNoGrief
  | denialFireOutcome
deriving DecidableEq, Repr

def adamGuidanceMoments : List AdamGuidanceMoment :=
  [ AdamGuidanceMoment.successorAnnounced
  , AdamGuidanceMoment.angelicQuestion
  , AdamGuidanceMoment.namesTaught
  , AdamGuidanceMoment.adamNamesDisplayed
  , AdamGuidanceMoment.hiddenRevealedConcealedKnown
  , AdamGuidanceMoment.angelsBowIblisRefuses
  , AdamGuidanceMoment.gardenCommandAndSlip
  , AdamGuidanceMoment.repentanceAccepted
  , AdamGuidanceMoment.guidanceNoFearNoGrief
  , AdamGuidanceMoment.denialFireOutcome
  ]

structure SuccessionKnowledgePattern where
  successorOnEarth : Bool
  angelsNameDamageAndBloodshed : Bool
  angelsCelebratePraise : Bool
  angelsProclaimHoliness : Bool
  divineKnowledgeExceedsAngels : Bool
  adamTaughtNames : Bool
  angelsAdmitTaughtKnowledgeOnly : Bool
  adamDisplaysNames : Bool
  hiddenHeavenEarthKnown : Bool
  revealedAndConcealedKnown : Bool
deriving DecidableEq, Repr

def successionKnowledgePattern : SuccessionKnowledgePattern where
  successorOnEarth := true
  angelsNameDamageAndBloodshed := true
  angelsCelebratePraise := true
  angelsProclaimHoliness := true
  divineKnowledgeExceedsAngels := true
  adamTaughtNames := true
  angelsAdmitTaughtKnowledgeOnly := true
  adamDisplaysNames := true
  hiddenHeavenEarthKnown := true
  revealedAndConcealedKnown := true

structure RefusalFallRepentancePattern where
  angelsCommandedToBow : Bool
  angelsBowed : Bool
  iblisRefused : Bool
  iblisArrogant : Bool
  iblisDisobedient : Bool
  gardenResidenceGranted : Bool
  treeBoundaryGiven : Bool
  satanMadeThemSlip : Bool
  descentWithMutualEnmity : Bool
  earthlyStayAndLivelihood : Bool
  wordsReceivedFromLord : Bool
  repentanceAccepted : Bool
  mercifulRelentingNamed : Bool
deriving DecidableEq, Repr

def refusalFallRepentancePattern : RefusalFallRepentancePattern where
  angelsCommandedToBow := true
  angelsBowed := true
  iblisRefused := true
  iblisArrogant := true
  iblisDisobedient := true
  gardenResidenceGranted := true
  treeBoundaryGiven := true
  satanMadeThemSlip := true
  descentWithMutualEnmity := true
  earthlyStayAndLivelihood := true
  wordsReceivedFromLord := true
  repentanceAccepted := true
  mercifulRelentingNamed := true

structure GuidanceOutcomePattern where
  guidanceCertainlyComesFromGod : Bool
  followersOfGuidanceHaveNoFear : Bool
  followersOfGuidanceDoNotGrieve : Bool
  disbelieversDenyMessages : Bool
  fireInhabitantsRemain : Bool
deriving DecidableEq, Repr

def guidanceOutcomePattern : GuidanceOutcomePattern where
  guidanceCertainlyComesFromGod := true
  followersOfGuidanceHaveNoFear := true
  followersOfGuidanceDoNotGrieve := true
  disbelieversDenyMessages := true
  fireInhabitantsRemain := true

theorem quran_al_baqara_adam_guidance_witness :
    adamGuidanceMoments.length = 10
    ∧ adamGuidanceMoments.head? = some AdamGuidanceMoment.successorAnnounced
    ∧ adamGuidanceMoments.getLast? = some AdamGuidanceMoment.denialFireOutcome
    ∧ successionKnowledgePattern.successorOnEarth = true
    ∧ successionKnowledgePattern.angelsNameDamageAndBloodshed = true
    ∧ successionKnowledgePattern.divineKnowledgeExceedsAngels = true
    ∧ successionKnowledgePattern.adamTaughtNames = true
    ∧ successionKnowledgePattern.angelsAdmitTaughtKnowledgeOnly = true
    ∧ successionKnowledgePattern.adamDisplaysNames = true
    ∧ successionKnowledgePattern.hiddenHeavenEarthKnown = true
    ∧ successionKnowledgePattern.revealedAndConcealedKnown = true
    ∧ refusalFallRepentancePattern.angelsCommandedToBow = true
    ∧ refusalFallRepentancePattern.angelsBowed = true
    ∧ refusalFallRepentancePattern.iblisRefused = true
    ∧ refusalFallRepentancePattern.iblisArrogant = true
    ∧ refusalFallRepentancePattern.treeBoundaryGiven = true
    ∧ refusalFallRepentancePattern.satanMadeThemSlip = true
    ∧ refusalFallRepentancePattern.descentWithMutualEnmity = true
    ∧ refusalFallRepentancePattern.repentanceAccepted = true
    ∧ guidanceOutcomePattern.guidanceCertainlyComesFromGod = true
    ∧ guidanceOutcomePattern.followersOfGuidanceHaveNoFear = true
    ∧ guidanceOutcomePattern.followersOfGuidanceDoNotGrieve = true
    ∧ guidanceOutcomePattern.disbelieversDenyMessages = true
    ∧ guidanceOutcomePattern.fireInhabitantsRemain = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraAdamGuidanceWitness
end Gnosis.Witnesses.Islam
