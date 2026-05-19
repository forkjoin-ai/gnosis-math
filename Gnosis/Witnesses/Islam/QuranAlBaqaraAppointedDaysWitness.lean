import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraAppointedDaysWitness

/-!
# Quran 2:203, Al-Baqara -- Appointed Days and Gathering

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1699-1702`.

This bounded witness tracks appointed remembrance days after the pilgrimage conduct unit:

  * God is remembered on appointed days;
  * leaving after two days carries no blame;
  * staying on carries no blame when joined to mindfulness;
  * mindfulness of God is repeated;
  * gathering to God is remembered.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive AppointedDaysMoment
  | rememberAppointedDays
  | leaveAfterTwoNoBlame
  | stayNoBlame
  | mindfulCondition
  | gatheredToGod
deriving DecidableEq, Repr

def appointedDaysMoments : List AppointedDaysMoment :=
  [ AppointedDaysMoment.rememberAppointedDays
  , AppointedDaysMoment.leaveAfterTwoNoBlame
  , AppointedDaysMoment.stayNoBlame
  , AppointedDaysMoment.mindfulCondition
  , AppointedDaysMoment.gatheredToGod
  ]

structure AppointedDaysPattern where
  rememberGod : Bool
  appointedDays : Bool
  hurryAfterTwoDaysNoBlame : Bool
  stayOnNoBlame : Bool
  mindfulCondition : Bool
  mindfulOfGod : Bool
  gatheredToGodRemembered : Bool
deriving DecidableEq, Repr

def appointedDaysPattern : AppointedDaysPattern where
  rememberGod := true
  appointedDays := true
  hurryAfterTwoDaysNoBlame := true
  stayOnNoBlame := true
  mindfulCondition := true
  mindfulOfGod := true
  gatheredToGodRemembered := true

theorem quran_al_baqara_appointed_days_witness :
    appointedDaysMoments.length = 5
    ∧ appointedDaysMoments.head? = some AppointedDaysMoment.rememberAppointedDays
    ∧ appointedDaysMoments.getLast? = some AppointedDaysMoment.gatheredToGod
    ∧ appointedDaysPattern.rememberGod = true
    ∧ appointedDaysPattern.appointedDays = true
    ∧ appointedDaysPattern.hurryAfterTwoDaysNoBlame = true
    ∧ appointedDaysPattern.stayOnNoBlame = true
    ∧ appointedDaysPattern.mindfulCondition = true
    ∧ appointedDaysPattern.mindfulOfGod = true
    ∧ appointedDaysPattern.gatheredToGodRemembered = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end QuranAlBaqaraAppointedDaysWitness
end Gnosis.Witnesses.Islam
