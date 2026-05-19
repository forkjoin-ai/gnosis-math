import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlNisaHouseholdTrustsAuthorityWitness

/-!
# Quran 4:34-59, An-Nisa -- Household Care, Worship Ethics, Scripture, Trusts, and Authority

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2921-3018`.

This bounded witness tracks Quran 4:34-59:

  * household care, devout guarding, correction, and family arbitration are named;
  * worship of God alone is joined to goodness toward parents, kin, orphans, needy,
    near and far neighbours, travellers, and slaves;
  * arrogance, miserliness, hidden bounty, show-spending, and Satanic companionship
    are opposed to faith, charity, and doubled good deeds;
  * each community has a witness, and the Prophet is a witness against his people;
  * prayer is restricted during intoxication and major impurity until the named remedy;
  * clean earth substitutes when water is unavailable in illness, journey, relieving,
    or intercourse;
  * some given Scripture purchase misguidance, distort words, and disparage religion;
  * People of the Book are called to believe what confirms what they have;
  * partner-joining is not forgiven, while lesser sins may be forgiven as God wills;
  * self-purity claims, invented lies, idols, evil powers, envy, Fire, Garden, and shade
    are contrasted;
  * trusts must be returned to their owners and judgment must be just;
  * believers obey God, the Messenger, and those in authority, and refer disputes to God
    and the Messenger.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive HouseholdTrustsAuthorityMoment
  | householdCare
  | familyArbitration
  | worshipAndSocialGood
  | arroganceMiserlinessShow
  | communityWitness
  | prayerPurity
  | scriptureDistortion
  | partnerJoiningWarning
  | envyFireGarden
  | trustsReturned
  | justJudgment
  | authorityDisputeReferral
deriving DecidableEq, Repr

def householdTrustsAuthorityMoments : List HouseholdTrustsAuthorityMoment :=
  [ HouseholdTrustsAuthorityMoment.householdCare
  , HouseholdTrustsAuthorityMoment.familyArbitration
  , HouseholdTrustsAuthorityMoment.worshipAndSocialGood
  , HouseholdTrustsAuthorityMoment.arroganceMiserlinessShow
  , HouseholdTrustsAuthorityMoment.communityWitness
  , HouseholdTrustsAuthorityMoment.prayerPurity
  , HouseholdTrustsAuthorityMoment.scriptureDistortion
  , HouseholdTrustsAuthorityMoment.partnerJoiningWarning
  , HouseholdTrustsAuthorityMoment.envyFireGarden
  , HouseholdTrustsAuthorityMoment.trustsReturned
  , HouseholdTrustsAuthorityMoment.justJudgment
  , HouseholdTrustsAuthorityMoment.authorityDisputeReferral
  ]

structure HouseholdTrustsAuthorityPattern where
  householdCareNamed : Bool
  arbitersFromBothFamilies : Bool
  worshipGodAlone : Bool
  socialGoodCommanded : Bool
  arroganceMiserlinessShowCondemned : Bool
  prophetAsWitness : Bool
  prayerPurityBounded : Bool
  earthSubstituteNamed : Bool
  scriptureDistortionNamed : Bool
  partnerJoiningTremendousSin : Bool
  envyAndAbrahamicBountyNamed : Bool
  fireAndGardenContrasted : Bool
  trustsReturnedToOwners : Bool
  judgmentWithJustice : Bool
  obeyGodMessengerAuthority : Bool
  disputesReferredToGodMessenger : Bool
deriving DecidableEq, Repr

def householdTrustsAuthorityPattern : HouseholdTrustsAuthorityPattern where
  householdCareNamed := true
  arbitersFromBothFamilies := true
  worshipGodAlone := true
  socialGoodCommanded := true
  arroganceMiserlinessShowCondemned := true
  prophetAsWitness := true
  prayerPurityBounded := true
  earthSubstituteNamed := true
  scriptureDistortionNamed := true
  partnerJoiningTremendousSin := true
  envyAndAbrahamicBountyNamed := true
  fireAndGardenContrasted := true
  trustsReturnedToOwners := true
  judgmentWithJustice := true
  obeyGodMessengerAuthority := true
  disputesReferredToGodMessenger := true

theorem quran_al_nisa_household_trusts_authority_witness :
    householdTrustsAuthorityMoments.length = 12
    ∧ householdTrustsAuthorityMoments.head? = some HouseholdTrustsAuthorityMoment.householdCare
    ∧ householdTrustsAuthorityMoments.getLast? = some HouseholdTrustsAuthorityMoment.authorityDisputeReferral
    ∧ householdTrustsAuthorityPattern.householdCareNamed = true
    ∧ householdTrustsAuthorityPattern.arbitersFromBothFamilies = true
    ∧ householdTrustsAuthorityPattern.worshipGodAlone = true
    ∧ householdTrustsAuthorityPattern.socialGoodCommanded = true
    ∧ householdTrustsAuthorityPattern.arroganceMiserlinessShowCondemned = true
    ∧ householdTrustsAuthorityPattern.prophetAsWitness = true
    ∧ householdTrustsAuthorityPattern.prayerPurityBounded = true
    ∧ householdTrustsAuthorityPattern.earthSubstituteNamed = true
    ∧ householdTrustsAuthorityPattern.scriptureDistortionNamed = true
    ∧ householdTrustsAuthorityPattern.partnerJoiningTremendousSin = true
    ∧ householdTrustsAuthorityPattern.envyAndAbrahamicBountyNamed = true
    ∧ householdTrustsAuthorityPattern.fireAndGardenContrasted = true
    ∧ householdTrustsAuthorityPattern.trustsReturnedToOwners = true
    ∧ householdTrustsAuthorityPattern.judgmentWithJustice = true
    ∧ householdTrustsAuthorityPattern.obeyGodMessengerAuthority = true
    ∧ householdTrustsAuthorityPattern.disputesReferredToGodMessenger = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlNisaHouseholdTrustsAuthorityWitness
end Gnosis.Witnesses.Islam
