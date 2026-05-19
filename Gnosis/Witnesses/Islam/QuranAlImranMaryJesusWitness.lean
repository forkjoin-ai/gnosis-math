import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlImranMaryJesusWitness

/-!
# Quran 3:33-64, Al Imran -- Mary, Jesus, Disciples, and Common Word

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2235-2327`.

This bounded witness tracks Quran 3:33-64:

  * Adam, Noah, Abraham's family, and Imran's family are chosen;
  * Imran's wife dedicates what is in her womb, Mary is born and commended to God,
    and Zachariah finds provision with her;
  * Zachariah prays and receives the announcement of John, with silence as a sign;
  * Mary is chosen, purified, and commanded to devotion;
  * unseen lots and disputes over Mary's care are named;
  * Jesus son of Mary is announced as a Word from God, Messiah, honored here and near
    in the Hereafter;
  * Jesus speaks in infancy and maturity, receives Scripture, wisdom, Torah, and Gospel,
    and brings signs by God's permission;
  * Jesus confirms Torah, makes some things lawful, and points to God as Lord;
  * disciples answer as helpers devoted to God;
  * God raises Jesus, purifies him from disbelievers, judges differences, and rewards
    belief;
  * Jesus is compared to Adam by creation from dust and command;
  * disputed claims are answered by truth, mutual invocation, and a common word:
    worship God alone, assign no partner, and take no lords beside God.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive MaryJesusMoment
  | chosenFamilies
  | maryDedicated
  | zachariahProvisionPrayer
  | johnSign
  | maryChosenPurified
  | unseenLots
  | jesusWordAnnounced
  | jesusSigns
  | disciplesHelpers
  | raisedAndJudged
  | adamComparison
  | commonWord
deriving DecidableEq, Repr

def maryJesusMoments : List MaryJesusMoment :=
  [ MaryJesusMoment.chosenFamilies
  , MaryJesusMoment.maryDedicated
  , MaryJesusMoment.zachariahProvisionPrayer
  , MaryJesusMoment.johnSign
  , MaryJesusMoment.maryChosenPurified
  , MaryJesusMoment.unseenLots
  , MaryJesusMoment.jesusWordAnnounced
  , MaryJesusMoment.jesusSigns
  , MaryJesusMoment.disciplesHelpers
  , MaryJesusMoment.raisedAndJudged
  , MaryJesusMoment.adamComparison
  , MaryJesusMoment.commonWord
  ]

structure MaryJesusPattern where
  chosenFamiliesNamed : Bool
  maryDedicatedBeforeBirth : Bool
  maryCommendedToGod : Bool
  zachariahFindsProvision : Bool
  johnAnnounced : Bool
  silenceSignGiven : Bool
  maryChosenAndPurified : Bool
  unseenAccountNamed : Bool
  jesusWordFromGod : Bool
  jesusSignsByPermission : Bool
  disciplesDeclareDevotion : Bool
  jesusRaisedAndPurified : Bool
  jesusLikeAdam : Bool
  commonWordWorshipAlone : Bool
  noPartnersNoLords : Bool
deriving DecidableEq, Repr

def maryJesusPattern : MaryJesusPattern where
  chosenFamiliesNamed := true
  maryDedicatedBeforeBirth := true
  maryCommendedToGod := true
  zachariahFindsProvision := true
  johnAnnounced := true
  silenceSignGiven := true
  maryChosenAndPurified := true
  unseenAccountNamed := true
  jesusWordFromGod := true
  jesusSignsByPermission := true
  disciplesDeclareDevotion := true
  jesusRaisedAndPurified := true
  jesusLikeAdam := true
  commonWordWorshipAlone := true
  noPartnersNoLords := true

theorem quran_al_imran_mary_jesus_witness :
    maryJesusMoments.length = 12
    ∧ maryJesusMoments.head? = some MaryJesusMoment.chosenFamilies
    ∧ maryJesusMoments.getLast? = some MaryJesusMoment.commonWord
    ∧ maryJesusPattern.chosenFamiliesNamed = true
    ∧ maryJesusPattern.maryDedicatedBeforeBirth = true
    ∧ maryJesusPattern.maryCommendedToGod = true
    ∧ maryJesusPattern.zachariahFindsProvision = true
    ∧ maryJesusPattern.johnAnnounced = true
    ∧ maryJesusPattern.silenceSignGiven = true
    ∧ maryJesusPattern.maryChosenAndPurified = true
    ∧ maryJesusPattern.unseenAccountNamed = true
    ∧ maryJesusPattern.jesusWordFromGod = true
    ∧ maryJesusPattern.jesusSignsByPermission = true
    ∧ maryJesusPattern.disciplesDeclareDevotion = true
    ∧ maryJesusPattern.jesusRaisedAndPurified = true
    ∧ maryJesusPattern.jesusLikeAdam = true
    ∧ maryJesusPattern.commonWordWorshipAlone = true
    ∧ maryJesusPattern.noPartnersNoLords = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlImranMaryJesusWitness
end Gnosis.Witnesses.Islam
