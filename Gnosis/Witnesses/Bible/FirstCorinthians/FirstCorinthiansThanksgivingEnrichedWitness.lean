import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansThanksgivingEnrichedWitness

/-!
# 1 Corinthians 1:4-9 (KJV) -- Thanksgiving, Enrichment, and Faithful Calling

This unit gives one bounded thanksgiving topology:

  * Paul thanks God for grace given by Jesus Christ;
  * the Corinthians are enriched in every thing, in utterance and knowledge;
  * the testimony of Christ is confirmed in them;
  * they come behind in no gift while waiting for the coming of Christ;
  * Christ confirms them to the end, blameless in his day;
  * God is faithful and calls them to fellowship of his Son.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- 1 Corinthians 1:4-9 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def first_corinthians_1_4_9_quote : String :=
  "1:4 I thank my God always on your behalf, for the grace of God which " ++
  "is given you by Jesus Christ; 1:5 That in every thing ye are enriched " ++
  "by him, in all utterance, and in all knowledge; 1:6 Even as the " ++
  "testimony of Christ was confirmed in you: 1:7 So that ye come behind " ++
  "in no gift; waiting for the coming of our Lord Jesus Christ: 1:8 Who " ++
  "shall also confirm you unto the end, that ye may be blameless in the " ++
  "day of our Lord Jesus Christ. 1:9 God is faithful, by whom ye were " ++
  "called unto the fellowship of his Son Jesus Christ our Lord."

/-! ## Section 1: Grace and enrichment -/

/-- The thanksgiving and enrichment pattern in 1 Corinthians 1:4-5. -/
structure ThanksgivingEnrichment where
  thanksGodAlways : Bool
  graceGivenByJesusChrist : Bool
  enrichedInEveryThing : Bool
  enrichedInUtterance : Bool
  enrichedInKnowledge : Bool
deriving DecidableEq, Repr

/-- Grace given by Christ enriches in utterance and knowledge. -/
def thanksgivingEnrichment : ThanksgivingEnrichment where
  thanksGodAlways := true
  graceGivenByJesusChrist := true
  enrichedInEveryThing := true
  enrichedInUtterance := true
  enrichedInKnowledge := true

/-! ## Section 2: Confirmation and gift -/

/-- The confirmation/no-gift-lack pattern in 1 Corinthians 1:6-8. -/
structure ConfirmationGiftPattern where
  testimonyOfChristConfirmed : Bool
  comeBehindInNoGift : Bool
  waitingForComingOfChrist : Bool
  confirmedUntoEnd : Bool
  blamelessInDayOfChrist : Bool
deriving DecidableEq, Repr

/-- The testimony is confirmed and the recipients are confirmed to the end. -/
def confirmationGiftPattern : ConfirmationGiftPattern where
  testimonyOfChristConfirmed := true
  comeBehindInNoGift := true
  waitingForComingOfChrist := true
  confirmedUntoEnd := true
  blamelessInDayOfChrist := true

/-! ## Section 3: Faithful calling -/

/-- The faithful-calling pattern in 1 Corinthians 1:9. -/
structure FaithfulCallingPattern where
  godFaithful : Bool
  calledToFellowship : Bool
  fellowshipOfSonJesusChrist : Bool
deriving DecidableEq, Repr

/-- God is faithful and calls into fellowship of his Son. -/
def faithfulCallingPattern : FaithfulCallingPattern where
  godFaithful := true
  calledToFellowship := true
  fellowshipOfSonJesusChrist := true

/-! ## Section 4: Master witness -/

/-- The bounded 1 Corinthians 1:4-9 witness. -/
theorem first_corinthians_thanksgiving_enriched_witness :
    thanksgivingEnrichment.thanksGodAlways = true
    ∧ thanksgivingEnrichment.graceGivenByJesusChrist = true
    ∧ thanksgivingEnrichment.enrichedInEveryThing = true
    ∧ thanksgivingEnrichment.enrichedInUtterance = true
    ∧ thanksgivingEnrichment.enrichedInKnowledge = true
    ∧ confirmationGiftPattern.testimonyOfChristConfirmed = true
    ∧ confirmationGiftPattern.comeBehindInNoGift = true
    ∧ confirmationGiftPattern.waitingForComingOfChrist = true
    ∧ confirmationGiftPattern.confirmedUntoEnd = true
    ∧ confirmationGiftPattern.blamelessInDayOfChrist = true
    ∧ faithfulCallingPattern.godFaithful = true
    ∧ faithfulCallingPattern.calledToFellowship = true
    ∧ faithfulCallingPattern.fellowshipOfSonJesusChrist = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansThanksgivingEnrichedWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
