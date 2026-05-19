import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraAbrahamCovenantWitness

/-!
# Quran 2:122-124, Al-Baqara -- Israel Reminder and Abrahamic Covenant

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1342-1349`.

This bounded witness tracks the transition from Israel's remembered favor to
Abraham's tested covenant:

  * Children of Israel are again told to remember blessing and favor;
  * the Day of accountability allows no substitution, compensation, intercession, or help;
  * Abraham is tested by commandments and fulfills them;
  * leadership for people is promised;
  * Abraham asks about his descendants;
  * the pledge does not hold for evildoers.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive AbrahamCovenantMoment
  | israelFavorRemembered
  | accountabilityDay
  | abrahamTested
  | commandmentsFulfilled
  | leadershipPromised
  | descendantsAsked
  | evildoersExcluded
deriving DecidableEq, Repr

def abrahamCovenantMoments : List AbrahamCovenantMoment :=
  [ AbrahamCovenantMoment.israelFavorRemembered
  , AbrahamCovenantMoment.accountabilityDay
  , AbrahamCovenantMoment.abrahamTested
  , AbrahamCovenantMoment.commandmentsFulfilled
  , AbrahamCovenantMoment.leadershipPromised
  , AbrahamCovenantMoment.descendantsAsked
  , AbrahamCovenantMoment.evildoersExcluded
  ]

structure IsraelAccountabilityPattern where
  childrenIsraelAddressed : Bool
  blessingRemembered : Bool
  favoredOverOtherPeople : Bool
  bewareDay : Bool
  noSoulStandsForAnother : Bool
  noCompensationAccepted : Bool
  noIntercessionUseful : Bool
  noHelpGiven : Bool
deriving DecidableEq, Repr

def israelAccountabilityPattern : IsraelAccountabilityPattern where
  childrenIsraelAddressed := true
  blessingRemembered := true
  favoredOverOtherPeople := true
  bewareDay := true
  noSoulStandsForAnother := true
  noCompensationAccepted := true
  noIntercessionUseful := true
  noHelpGiven := true

structure AbrahamLeadershipPattern where
  abrahamNamed : Bool
  lordTestedAbraham : Bool
  commandmentsGiven : Bool
  commandmentsFulfilled : Bool
  leaderOfPeoplePromised : Bool
  descendantsLeadershipAsked : Bool
  pledgeNamed : Bool
  evildoersExcluded : Bool
deriving DecidableEq, Repr

def abrahamLeadershipPattern : AbrahamLeadershipPattern where
  abrahamNamed := true
  lordTestedAbraham := true
  commandmentsGiven := true
  commandmentsFulfilled := true
  leaderOfPeoplePromised := true
  descendantsLeadershipAsked := true
  pledgeNamed := true
  evildoersExcluded := true

theorem quran_al_baqara_abraham_covenant_witness :
    abrahamCovenantMoments.length = 7
    ∧ abrahamCovenantMoments.head? = some AbrahamCovenantMoment.israelFavorRemembered
    ∧ abrahamCovenantMoments.getLast? = some AbrahamCovenantMoment.evildoersExcluded
    ∧ israelAccountabilityPattern.childrenIsraelAddressed = true
    ∧ israelAccountabilityPattern.blessingRemembered = true
    ∧ israelAccountabilityPattern.favoredOverOtherPeople = true
    ∧ israelAccountabilityPattern.bewareDay = true
    ∧ israelAccountabilityPattern.noSoulStandsForAnother = true
    ∧ israelAccountabilityPattern.noCompensationAccepted = true
    ∧ israelAccountabilityPattern.noIntercessionUseful = true
    ∧ israelAccountabilityPattern.noHelpGiven = true
    ∧ abrahamLeadershipPattern.abrahamNamed = true
    ∧ abrahamLeadershipPattern.lordTestedAbraham = true
    ∧ abrahamLeadershipPattern.commandmentsGiven = true
    ∧ abrahamLeadershipPattern.commandmentsFulfilled = true
    ∧ abrahamLeadershipPattern.leaderOfPeoplePromised = true
    ∧ abrahamLeadershipPattern.descendantsLeadershipAsked = true
    ∧ abrahamLeadershipPattern.pledgeNamed = true
    ∧ abrahamLeadershipPattern.evildoersExcluded = true := by
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

end QuranAlBaqaraAbrahamCovenantWitness
end Gnosis.Witnesses.Islam
