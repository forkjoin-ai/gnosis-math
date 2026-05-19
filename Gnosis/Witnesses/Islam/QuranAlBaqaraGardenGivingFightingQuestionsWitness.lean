import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraGardenGivingFightingQuestionsWitness

/-!
# Quran 2:214-220, Al-Baqara -- Trial, Giving, Fighting, Intoxicants, Orphans

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1740-1775`.

This witness tracks Garden entry through affliction, giving to parents and needy,
ordained fighting despite dislike, prohibited-month fighting weighed against
persecution and expulsion, mercy for believers who migrate and strive, intoxicants
and gambling, spare giving, reflection on both worlds, and setting right orphan
property.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive GardenGivingFightingQuestionsMoment
  | afflictionBeforeGarden
  | godsHelpNear
  | givingRecipients
  | fightingOrdained
  | godKnowsYouDoNot
  | prohibitedMonthQuestion
  | persecutionWorseThanKilling
  | apostasyFireWarning
  | beliefMigrationStrivingMercy
  | intoxicantsGambling
  | spareGivingReflection
  | orphanAffairsSetRight
deriving DecidableEq, Repr

def gardenGivingFightingQuestionsMoments : List GardenGivingFightingQuestionsMoment :=
  [ .afflictionBeforeGarden, .godsHelpNear, .givingRecipients, .fightingOrdained
  , .godKnowsYouDoNot, .prohibitedMonthQuestion, .persecutionWorseThanKilling
  , .apostasyFireWarning, .beliefMigrationStrivingMercy, .intoxicantsGambling
  , .spareGivingReflection, .orphanAffairsSetRight ]

theorem quran_al_baqara_garden_giving_fighting_questions_witness :
    gardenGivingFightingQuestionsMoments.length = 12
    ∧ gardenGivingFightingQuestionsMoments.head? = some .afflictionBeforeGarden
    ∧ gardenGivingFightingQuestionsMoments.getLast? = some .orphanAffairsSetRight := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraGardenGivingFightingQuestionsWitness
end Gnosis.Witnesses.Islam
