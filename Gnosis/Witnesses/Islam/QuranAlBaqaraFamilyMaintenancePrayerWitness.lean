import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraFamilyMaintenancePrayerWitness

/-!
# Quran 2:233-242, Al-Baqara -- Nursing, Widows, Provision, Prayer

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1844-1896`.

This witness tracks nursing for two years, fair maintenance, no parental harm,
mutual-consent weaning, wet nurse payment, widow waiting, honorable proposal,
unconsummated divorce provision, half bride-gift and generosity, guarding prayer
even in danger, widow bequest and maintenance, fair divorced-women maintenance,
and revelations made clear for understanding.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive FamilyMaintenancePrayerMoment
  | nursingTermMaintenance
  | noParentalHarm
  | mutualWeaningWetNurse
  | widowWaitingProposal
  | unconsummatedProvision
  | halfGiftGenerosity
  | prayersGuarded
  | dangerPrayer
  | widowYearMaintenance
  | divorcedWomenMaintenance
  | revelationsForUnderstanding
deriving DecidableEq, Repr

def familyMaintenancePrayerMoments : List FamilyMaintenancePrayerMoment :=
  [ .nursingTermMaintenance, .noParentalHarm, .mutualWeaningWetNurse
  , .widowWaitingProposal, .unconsummatedProvision, .halfGiftGenerosity
  , .prayersGuarded, .dangerPrayer, .widowYearMaintenance
  , .divorcedWomenMaintenance, .revelationsForUnderstanding ]

theorem quran_al_baqara_family_maintenance_prayer_witness :
    familyMaintenancePrayerMoments.length = 11
    ∧ familyMaintenancePrayerMoments.head? = some .nursingTermMaintenance
    ∧ familyMaintenancePrayerMoments.getLast? = some .revelationsForUnderstanding := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraFamilyMaintenancePrayerWitness
end Gnosis.Witnesses.Islam
