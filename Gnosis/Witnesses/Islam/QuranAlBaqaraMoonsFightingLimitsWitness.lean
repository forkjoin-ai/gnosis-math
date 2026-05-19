import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraMoonsFightingLimitsWitness

/-!
# Quran 2:189-190, Al-Baqara -- Moons, Piety, Fighting Limits

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1618-1625`.

This bounded witness tracks calendrical signs and bounded fighting:

  * crescent moons mark appointed times for people and pilgrimage;
  * goodness is not entering houses by the back door;
  * true goodness is mindfulness of God;
  * entering houses by their main doors and mindfulness aim at prospering;
  * fighting in God's cause is bounded to those who fight you;
  * overstepping limits is forbidden because God does not love those who overstep.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive MoonsFightingLimitsMoment
  | crescentMoonsAsked
  | appointedTimes
  | pilgrimageTiming
  | practicalPiety
  | mainDoorsMindfulness
  | boundedFighting
  | noOverstepping
deriving DecidableEq, Repr

def moonsFightingLimitsMoments : List MoonsFightingLimitsMoment :=
  [ MoonsFightingLimitsMoment.crescentMoonsAsked
  , MoonsFightingLimitsMoment.appointedTimes
  , MoonsFightingLimitsMoment.pilgrimageTiming
  , MoonsFightingLimitsMoment.practicalPiety
  , MoonsFightingLimitsMoment.mainDoorsMindfulness
  , MoonsFightingLimitsMoment.boundedFighting
  , MoonsFightingLimitsMoment.noOverstepping
  ]

structure MoonPietyPattern where
  crescentMoonsAsked : Bool
  appointedTimesForPeople : Bool
  appointedTimesForPilgrimage : Bool
  goodnessNotBackDoorEntry : Bool
  goodPersonMindfulOfGod : Bool
  enterByMainDoors : Bool
  mindfulnessCommand : Bool
  prosperAim : Bool
deriving DecidableEq, Repr

def moonPietyPattern : MoonPietyPattern where
  crescentMoonsAsked := true
  appointedTimesForPeople := true
  appointedTimesForPilgrimage := true
  goodnessNotBackDoorEntry := true
  goodPersonMindfulOfGod := true
  enterByMainDoors := true
  mindfulnessCommand := true
  prosperAim := true

structure FightingLimitPattern where
  fightInGodsCause : Bool
  fightThoseWhoFightYou : Bool
  doNotOverstepLimits : Bool
  godDoesNotLoveOversteppers : Bool
deriving DecidableEq, Repr

def fightingLimitPattern : FightingLimitPattern where
  fightInGodsCause := true
  fightThoseWhoFightYou := true
  doNotOverstepLimits := true
  godDoesNotLoveOversteppers := true

theorem quran_al_baqara_moons_fighting_limits_witness :
    moonsFightingLimitsMoments.length = 7
    ∧ moonsFightingLimitsMoments.head? =
        some MoonsFightingLimitsMoment.crescentMoonsAsked
    ∧ moonsFightingLimitsMoments.getLast? =
        some MoonsFightingLimitsMoment.noOverstepping
    ∧ moonPietyPattern.crescentMoonsAsked = true
    ∧ moonPietyPattern.appointedTimesForPeople = true
    ∧ moonPietyPattern.appointedTimesForPilgrimage = true
    ∧ moonPietyPattern.goodnessNotBackDoorEntry = true
    ∧ moonPietyPattern.goodPersonMindfulOfGod = true
    ∧ moonPietyPattern.enterByMainDoors = true
    ∧ moonPietyPattern.mindfulnessCommand = true
    ∧ moonPietyPattern.prosperAim = true
    ∧ fightingLimitPattern.fightInGodsCause = true
    ∧ fightingLimitPattern.fightThoseWhoFightYou = true
    ∧ fightingLimitPattern.doNotOverstepLimits = true
    ∧ fightingLimitPattern.godDoesNotLoveOversteppers = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end QuranAlBaqaraMoonsFightingLimitsWitness
end Gnosis.Witnesses.Islam
