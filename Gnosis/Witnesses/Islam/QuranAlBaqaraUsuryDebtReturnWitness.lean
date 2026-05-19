import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraUsuryDebtReturnWitness

/-!
# Quran 2:275-281, Al-Baqara -- Usury, Debt Mercy, Return

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2052-2072`.

This witness tracks usury rising under Satan's touch, trade allowed and usury
forbidden, stopping after warning, Fire for return to usury, usury blighted and
charity increased, reward for faith/prayer/alms, giving up outstanding usury,
war warning from God and Messenger, capital without loss or causing loss, debtor
difficulty delay, charitable write-off, and the Day of return and full payment.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive UsuryDebtReturnMoment
  | usuryResurrectionImage
  | tradeAllowedUsuryForbidden
  | stopAfterWarning
  | fireForReturn
  | usuryBlightedCharityBlessed
  | faithPrayerAlmsReward
  | giveUpOutstandingUsury
  | warWarning
  | capitalNoLoss
  | debtorDelayCharity
  | returnDayFullPayment
deriving DecidableEq, Repr

def usuryDebtReturnMoments : List UsuryDebtReturnMoment :=
  [ .usuryResurrectionImage, .tradeAllowedUsuryForbidden, .stopAfterWarning
  , .fireForReturn, .usuryBlightedCharityBlessed, .faithPrayerAlmsReward
  , .giveUpOutstandingUsury, .warWarning, .capitalNoLoss, .debtorDelayCharity
  , .returnDayFullPayment ]

theorem quran_al_baqara_usury_debt_return_witness :
    usuryDebtReturnMoments.length = 11
    ∧ usuryDebtReturnMoments.head? = some .usuryResurrectionImage
    ∧ usuryDebtReturnMoments.getLast? = some .returnDayFullPayment := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraUsuryDebtReturnWitness
end Gnosis.Witnesses.Islam
