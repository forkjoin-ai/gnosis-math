import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraLifeLoanReturnWitness

/-!
# Quran 2:243-245, Al-Baqara -- Life, Fighting, Good Loan, Return

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1897-1904`.

This witness tracks those who fled death, divine death and revival, ingratitude
despite favor, fighting in God's cause, all-hearing/all-knowing witness, the good
loan multiplied many times, God's withholding and abundant giving, and return to Him.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive LifeLoanReturnMoment
  | fledDeath
  | dieAndRevive
  | favorIngratitude
  | fightGodsCause
  | hearingKnowing
  | goodLoanMultiplied
  | withholdsAndGives
  | returnToGod
deriving DecidableEq, Repr

def lifeLoanReturnMoments : List LifeLoanReturnMoment :=
  [ .fledDeath, .dieAndRevive, .favorIngratitude, .fightGodsCause
  , .hearingKnowing, .goodLoanMultiplied, .withholdsAndGives, .returnToGod ]

theorem quran_al_baqara_life_loan_return_witness :
    lifeLoanReturnMoments.length = 8
    ∧ lifeLoanReturnMoments.head? = some .fledDeath
    ∧ lifeLoanReturnMoments.getLast? = some .returnToGod := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraLifeLoanReturnWitness
end Gnosis.Witnesses.Islam
