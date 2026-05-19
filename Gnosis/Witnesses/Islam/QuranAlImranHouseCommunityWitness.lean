import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlImranHouseCommunityWitness

/-!
# Quran 3:93-120, Al Imran -- Food, House, Rope, and Community

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2412-2501`.

This bounded witness tracks Quran 3:93-120:

  * food was lawful before Torah except what Israel made unlawful for himself;
  * false attribution to God is rejected and Abraham's religion is followed;
  * the first House at Bakka is blessed guidance with clear signs and Abraham's place;
  * pilgrimage is a duty for those able, while God needs none;
  * People of the Book are challenged for rejecting revelations and turning believers
    from God's path;
  * believers are warned not to yield to those who would make them revert;
  * God's revelations and Messenger are among them, and holding fast to God gives a
    straight path;
  * believers hold together to God's rope, remember hearts joined, and avoid division;
  * a community calls to good, orders right, and forbids wrong;
  * faces brighten or darken on the Day;
  * the best community is named by ordering right, forbidding wrong, and believing in God;
  * upright People of the Book recite at night, bow, believe, and do good;
  * disbelievers' possessions and children do not help them;
  * harmful outsider intimacy is warned against, including hidden hatred and scheming.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive HouseCommunityMoment
  | foodBeforeTorah
  | abrahamReligion
  | firstHouseBakka
  | pilgrimageDuty
  | pathObstructionWarning
  | holdFastToGod
  | ropeTogether
  | communityCallsGood
  | facesDay
  | bestCommunity
  | uprightPeopleBook
  | disbelieversNotHelped
  | outsiderIntimatesWarning
deriving DecidableEq, Repr

def houseCommunityMoments : List HouseCommunityMoment :=
  [ HouseCommunityMoment.foodBeforeTorah
  , HouseCommunityMoment.abrahamReligion
  , HouseCommunityMoment.firstHouseBakka
  , HouseCommunityMoment.pilgrimageDuty
  , HouseCommunityMoment.pathObstructionWarning
  , HouseCommunityMoment.holdFastToGod
  , HouseCommunityMoment.ropeTogether
  , HouseCommunityMoment.communityCallsGood
  , HouseCommunityMoment.facesDay
  , HouseCommunityMoment.bestCommunity
  , HouseCommunityMoment.uprightPeopleBook
  , HouseCommunityMoment.disbelieversNotHelped
  , HouseCommunityMoment.outsiderIntimatesWarning
  ]

structure HouseCommunityPattern where
  torahFoodBoundaryNamed : Bool
  abrahamReligionFollowed : Bool
  firstHouseBlessedGuidance : Bool
  pilgrimageDutyNamed : Bool
  godNeedsNoOne : Bool
  pathObstructionCondemned : Bool
  revelationsAndMessengerPresent : Bool
  ropeHeldTogether : Bool
  heartsJoined : Bool
  goodCommandingCommunity : Bool
  facesBrightenDarken : Bool
  bestCommunityNamed : Bool
  uprightPeopleBookNamed : Bool
  possessionsChildrenNoHelp : Bool
  outsiderIntimacyWarned : Bool
deriving DecidableEq, Repr

def houseCommunityPattern : HouseCommunityPattern where
  torahFoodBoundaryNamed := true
  abrahamReligionFollowed := true
  firstHouseBlessedGuidance := true
  pilgrimageDutyNamed := true
  godNeedsNoOne := true
  pathObstructionCondemned := true
  revelationsAndMessengerPresent := true
  ropeHeldTogether := true
  heartsJoined := true
  goodCommandingCommunity := true
  facesBrightenDarken := true
  bestCommunityNamed := true
  uprightPeopleBookNamed := true
  possessionsChildrenNoHelp := true
  outsiderIntimacyWarned := true

theorem quran_al_imran_house_community_witness :
    houseCommunityMoments.length = 13
    ∧ houseCommunityMoments.head? = some HouseCommunityMoment.foodBeforeTorah
    ∧ houseCommunityMoments.getLast? = some HouseCommunityMoment.outsiderIntimatesWarning
    ∧ houseCommunityPattern.torahFoodBoundaryNamed = true
    ∧ houseCommunityPattern.abrahamReligionFollowed = true
    ∧ houseCommunityPattern.firstHouseBlessedGuidance = true
    ∧ houseCommunityPattern.pilgrimageDutyNamed = true
    ∧ houseCommunityPattern.godNeedsNoOne = true
    ∧ houseCommunityPattern.pathObstructionCondemned = true
    ∧ houseCommunityPattern.revelationsAndMessengerPresent = true
    ∧ houseCommunityPattern.ropeHeldTogether = true
    ∧ houseCommunityPattern.heartsJoined = true
    ∧ houseCommunityPattern.goodCommandingCommunity = true
    ∧ houseCommunityPattern.facesBrightenDarken = true
    ∧ houseCommunityPattern.bestCommunityNamed = true
    ∧ houseCommunityPattern.uprightPeopleBookNamed = true
    ∧ houseCommunityPattern.possessionsChildrenNoHelp = true
    ∧ houseCommunityPattern.outsiderIntimacyWarned = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlImranHouseCommunityWitness
end Gnosis.Witnesses.Islam
