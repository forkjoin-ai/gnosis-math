import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraDisbeliefRejectionWitness

/-!
# Quran 2:161-162, Al-Baqara -- Disbelief, Rejection, No Reprieve

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1495-1498`.

This bounded witness tracks the short no-reprieve warning:

  * those who disbelieve and die as disbelievers are rejected by God, angels, and all people;
  * they remain in that rejection;
  * punishment is not lightened;
  * no reprieve is given.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive DisbeliefRejectionMoment
  | dieAsDisbelievers
  | godRejects
  | angelsAndPeopleReject
  | remainRejected
  | punishmentNotLightened
  | noReprieve
deriving DecidableEq, Repr

def disbeliefRejectionMoments : List DisbeliefRejectionMoment :=
  [ DisbeliefRejectionMoment.dieAsDisbelievers
  , DisbeliefRejectionMoment.godRejects
  , DisbeliefRejectionMoment.angelsAndPeopleReject
  , DisbeliefRejectionMoment.remainRejected
  , DisbeliefRejectionMoment.punishmentNotLightened
  , DisbeliefRejectionMoment.noReprieve
  ]

structure DisbeliefRejectionPattern where
  disbelieve : Bool
  dieAsDisbelievers : Bool
  godRejects : Bool
  angelsReject : Bool
  allPeopleReject : Bool
  remainInRejection : Bool
  punishmentNotLightened : Bool
  notReprieved : Bool
deriving DecidableEq, Repr

def disbeliefRejectionPattern : DisbeliefRejectionPattern where
  disbelieve := true
  dieAsDisbelievers := true
  godRejects := true
  angelsReject := true
  allPeopleReject := true
  remainInRejection := true
  punishmentNotLightened := true
  notReprieved := true

theorem quran_al_baqara_disbelief_rejection_witness :
    disbeliefRejectionMoments.length = 6
    ∧ disbeliefRejectionMoments.head? = some DisbeliefRejectionMoment.dieAsDisbelievers
    ∧ disbeliefRejectionMoments.getLast? = some DisbeliefRejectionMoment.noReprieve
    ∧ disbeliefRejectionPattern.disbelieve = true
    ∧ disbeliefRejectionPattern.dieAsDisbelievers = true
    ∧ disbeliefRejectionPattern.godRejects = true
    ∧ disbeliefRejectionPattern.angelsReject = true
    ∧ disbeliefRejectionPattern.allPeopleReject = true
    ∧ disbeliefRejectionPattern.remainInRejection = true
    ∧ disbeliefRejectionPattern.punishmentNotLightened = true
    ∧ disbeliefRejectionPattern.notReprieved = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end QuranAlBaqaraDisbeliefRejectionWitness
end Gnosis.Witnesses.Islam
