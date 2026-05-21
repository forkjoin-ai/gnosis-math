import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansLibertyCircumcisionDebtWitness

/-!
# Galatians 5:1-6 -- Liberty, Circumcision Debt, and Faith Working by Love

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93868-93885`.

Galatians turns freewoman heirship into an operational command: stand in liberty
and do not re-enter the yoke. Circumcision as justification strategy is modeled
as total-law debt and grace-fall; the live invariant is faith working by love.

No `sorry`, no new `axiom`.
-/

structure LibertyBoundary where
  christMadeFree : Bool := true
  standFastInLiberty : Bool := true
  yokeOfBondageRejected : Bool := true
deriving DecidableEq, Repr

def libertyBoundary : LibertyBoundary := {}

def libertyAgainstBondage (b : LibertyBoundary) : Prop :=
  b.christMadeFree = true ∧
  b.standFastInLiberty = true ∧
  b.yokeOfBondageRejected = true

structure CircumcisionDebt where
  circumcisionMakesChristProfitNothing : Bool := true
  circumcisedDebtorToWholeLaw : Bool := true
  lawJustificationMakesChristNoEffect : Bool := true
  fallenFromGrace : Bool := true
deriving DecidableEq, Repr

def circumcisionDebt : CircumcisionDebt := {}

def circumcisionDebtBoundary (d : CircumcisionDebt) : Prop :=
  d.circumcisionMakesChristProfitNothing = true ∧
  d.circumcisedDebtorToWholeLaw = true ∧
  d.lawJustificationMakesChristNoEffect = true ∧
  d.fallenFromGrace = true

structure FaithWorkingLove where
  spiritWaitsForRighteousnessHope : Bool := true
  hopeByFaith : Bool := true
  circumcisionAvailsNothing : Bool := true
  uncircumcisionAvailsNothing : Bool := true
  faithWorksByLove : Bool := true
deriving DecidableEq, Repr

def faithWorkingLove : FaithWorkingLove := {}

def faithLoveInvariant (f : FaithWorkingLove) : Prop :=
  f.spiritWaitsForRighteousnessHope = true ∧
  f.hopeByFaith = true ∧
  f.circumcisionAvailsNothing = true ∧
  f.uncircumcisionAvailsNothing = true ∧
  f.faithWorksByLove = true

theorem galatians_liberty_against_bondage :
    libertyAgainstBondage libertyBoundary := by
  unfold libertyAgainstBondage libertyBoundary
  exact ⟨rfl, rfl, rfl⟩

theorem galatians_circumcision_debt_boundary :
    circumcisionDebtBoundary circumcisionDebt := by
  unfold circumcisionDebtBoundary circumcisionDebt
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_faith_love_invariant :
    faithLoveInvariant faithWorkingLove := by
  unfold faithLoveInvariant faithWorkingLove
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_liberty_circumcision_debt_witness :
    libertyAgainstBondage libertyBoundary ∧
    circumcisionDebtBoundary circumcisionDebt ∧
    faithLoveInvariant faithWorkingLove := by
  exact ⟨galatians_liberty_against_bondage,
    galatians_circumcision_debt_boundary,
    galatians_faith_love_invariant⟩

end GalatiansLibertyCircumcisionDebtWitness
end Gnosis.Witnesses.Bible.Galatians
