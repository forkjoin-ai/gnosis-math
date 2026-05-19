import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraDebtWitnessAccountWitness

/-!
# Quran 2:282-284, Al-Baqara -- Debt Writing, Witnesses, Trust, Account

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2073-2103`.

This witness tracks writing stated-term debts, just scribes, debtor dictation,
guardian dictation for incapacity, witnesses, no refusal, small/large debts and
due time, trade exception, no harm to scribe or witness, mindfulness and divine
teaching, journey security, trust fulfillment, no concealed evidence, sinful heart,
God's full awareness, ownership of heavens and earth, revealed/concealed thoughts
called to account, forgiveness/punishment by will, and power over all things.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive DebtWitnessAccountMoment
  | debtWritten
  | justScribe
  | debtorOrGuardianDictates
  | witnessesCalled
  | noWitnessRefusal
  | smallLargeDueRecorded
  | tradeException
  | noScribeWitnessHarm
  | journeySecurityTrust
  | evidenceNotConcealed
  | heavensEarthGods
  | thoughtsAccounted
  | forgivePunishPower
deriving DecidableEq, Repr

def debtWitnessAccountMoments : List DebtWitnessAccountMoment :=
  [ .debtWritten, .justScribe, .debtorOrGuardianDictates, .witnessesCalled
  , .noWitnessRefusal, .smallLargeDueRecorded, .tradeException, .noScribeWitnessHarm
  , .journeySecurityTrust, .evidenceNotConcealed, .heavensEarthGods
  , .thoughtsAccounted, .forgivePunishPower ]

theorem quran_al_baqara_debt_witness_account_witness :
    debtWitnessAccountMoments.length = 13
    ∧ debtWitnessAccountMoments.head? = some .debtWritten
    ∧ debtWitnessAccountMoments.getLast? = some .forgivePunishPower := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraDebtWitnessAccountWitness
end Gnosis.Witnesses.Islam
