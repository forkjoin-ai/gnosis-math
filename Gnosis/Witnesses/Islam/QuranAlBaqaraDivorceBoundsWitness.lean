import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraDivorceBoundsWitness

/-!
# Quran 2:229-232, Al-Baqara -- Divorce Bounds and Fair Release

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1818-1843`.

This witness tracks twice-divorce, acceptable keeping or good release, no taking
back gifts except where God's bounds cannot be maintained, release compensation,
not overstepping bounds, remarriage after another marriage, fair keeping/release,
no harmful holding, no mockery of revelations, remembrance of favor, Scripture
and wisdom, and not preventing fair remarriage.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive DivorceBoundsMoment
  | divorceTwice
  | keepOrReleaseWell
  | noTakingBackExceptBounds
  | releaseCompensation
  | godsBoundsNoOverstep
  | thirdDivorceRemarriageCondition
  | fairSetTimeChoice
  | noHarmfulHolding
  | revelationsNotMocked
  | fairRemarriageNotBlocked
deriving DecidableEq, Repr

def divorceBoundsMoments : List DivorceBoundsMoment :=
  [ .divorceTwice, .keepOrReleaseWell, .noTakingBackExceptBounds
  , .releaseCompensation, .godsBoundsNoOverstep, .thirdDivorceRemarriageCondition
  , .fairSetTimeChoice, .noHarmfulHolding, .revelationsNotMocked
  , .fairRemarriageNotBlocked ]

theorem quran_al_baqara_divorce_bounds_witness :
    divorceBoundsMoments.length = 10
    ∧ divorceBoundsMoments.head? = some .divorceTwice
    ∧ divorceBoundsMoments.getLast? = some .fairRemarriageNotBlocked := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraDivorceBoundsWitness
end Gnosis.Witnesses.Islam
