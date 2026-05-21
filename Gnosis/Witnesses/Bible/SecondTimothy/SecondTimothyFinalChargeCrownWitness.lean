import Init

namespace Gnosis.Witnesses.Bible.SecondTimothy
namespace SecondTimothyFinalChargeCrownWitness

/-!
# 2 Timothy 4 -- Final Charge, Finished Course, Abandonment, and Deliverance

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95739-95804`.

The final charge holds under ear-driven drift. Paul names his offering, completed
course, crown, desertion, books and parchments, enemy resistance, abandonment at
first defense, and the Lord's strengthening presence.

No `sorry`, no new `axiom`.
-/

structure FinalCharge where
  judgeQuickDeadAppearingKingdom : Bool := true
  preachWordInOutSeason : Bool := true
  reproveRebukeExhortDoctrine : Bool := true
  itchingEarsSoundDoctrineRefused : Bool := true
  truthTurnedToFables : Bool := true
  watchEndureEvangelistProof : Bool := true
deriving DecidableEq, Repr

def finalCharge : FinalCharge := {}

def finalChargeWitness (c : FinalCharge) : Prop :=
  c.judgeQuickDeadAppearingKingdom = true ∧
  c.preachWordInOutSeason = true ∧
  c.reproveRebukeExhortDoctrine = true ∧
  c.itchingEarsSoundDoctrineRefused = true ∧
  c.truthTurnedToFables = true ∧
  c.watchEndureEvangelistProof = true

structure CrownDeliverance where
  readyOfferedDepartureNear : Bool := true
  foughtFinishedKeptFaith : Bool := true
  crownForLoveAppearing : Bool := true
  demasLovedPresentWorld : Bool := true
  markProfitableForMinistry : Bool := true
  booksParchmentsRequested : Bool := true
  alexanderWithstoodWords : Bool := true
  firstDefenseForsaken : Bool := true
  lordStoodStrengthenedPreaching : Bool := true
  deliveredAndPreservedKingdom : Bool := true
  finalGraceWithSpirit : Bool := true
deriving DecidableEq, Repr

def crownDeliverance : CrownDeliverance := {}

def crownDeliveranceWitness (d : CrownDeliverance) : Prop :=
  d.readyOfferedDepartureNear = true ∧
  d.foughtFinishedKeptFaith = true ∧
  d.crownForLoveAppearing = true ∧
  d.demasLovedPresentWorld = true ∧
  d.markProfitableForMinistry = true ∧
  d.booksParchmentsRequested = true ∧
  d.alexanderWithstoodWords = true ∧
  d.firstDefenseForsaken = true ∧
  d.lordStoodStrengthenedPreaching = true ∧
  d.deliveredAndPreservedKingdom = true ∧
  d.finalGraceWithSpirit = true

theorem second_timothy_final_charge :
    finalChargeWitness finalCharge := by
  unfold finalChargeWitness finalCharge
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_timothy_crown_deliverance :
    crownDeliveranceWitness crownDeliverance := by
  unfold crownDeliveranceWitness crownDeliverance
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_timothy_final_charge_crown_witness :
    finalChargeWitness finalCharge ∧
    crownDeliveranceWitness crownDeliverance := by
  exact ⟨second_timothy_final_charge,
    second_timothy_crown_deliverance⟩

end SecondTimothyFinalChargeCrownWitness
end Gnosis.Witnesses.Bible.SecondTimothy
