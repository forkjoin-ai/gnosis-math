import Init

namespace Gnosis.Witnesses.Bible.Titus
namespace TitusRegenerationGoodWorksWitness

/-!
# Titus 3 -- Regeneration Mercy, Profitable Good Works, and Vain Questions Avoided

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95885-95941`.

The final chapter grounds civic gentleness and good works in mercy, not works of
righteousness already done. The counterproof is foolish questions, genealogies,
law-strife, and self-condemned divisiveness.

No `sorry`, no new `axiom`.
-/

structure RegenerationMercy where
  subjectReadyGoodWork : Bool := true
  noEvilGentleMeekAll : Bool := true
  formerFoolishHatefulState : Bool := true
  kindnessLoveAppeared : Bool := true
  notByRighteousWorks : Bool := true
  mercySavedByRegenerationRenewing : Bool := true
  justifiedByGraceHeirsHope : Bool := true
deriving DecidableEq, Repr

def regenerationMercy : RegenerationMercy := {}

def regenerationMercyWitness (r : RegenerationMercy) : Prop :=
  r.subjectReadyGoodWork = true ∧ r.noEvilGentleMeekAll = true ∧
  r.formerFoolishHatefulState = true ∧ r.kindnessLoveAppeared = true ∧
  r.notByRighteousWorks = true ∧ r.mercySavedByRegenerationRenewing = true ∧
  r.justifiedByGraceHeirsHope = true

structure ProfitableWorksBoundary where
  believersMaintainGoodWorks : Bool := true
  goodProfitableUntoMen : Bool := true
  foolishQuestionsAvoided : Bool := true
  genealogiesContentionsLawStrifeVain : Bool := true
  hereticAfterAdmonitionRejected : Bool := true
  subvertedSelfCondemned : Bool := true
  necessaryUsesNotUnfruitful : Bool := true
  graceClosing : Bool := true
deriving DecidableEq, Repr

def profitableWorksBoundary : ProfitableWorksBoundary := {}

def profitableWorksWitness (p : ProfitableWorksBoundary) : Prop :=
  p.believersMaintainGoodWorks = true ∧ p.goodProfitableUntoMen = true ∧
  p.foolishQuestionsAvoided = true ∧ p.genealogiesContentionsLawStrifeVain = true ∧
  p.hereticAfterAdmonitionRejected = true ∧ p.subvertedSelfCondemned = true ∧
  p.necessaryUsesNotUnfruitful = true ∧ p.graceClosing = true

theorem titus_regeneration_mercy :
    regenerationMercyWitness regenerationMercy := by
  unfold regenerationMercyWitness regenerationMercy
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem titus_profitable_works :
    profitableWorksWitness profitableWorksBoundary := by
  unfold profitableWorksWitness profitableWorksBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem titus_regeneration_good_works_witness :
    regenerationMercyWitness regenerationMercy ∧
    profitableWorksWitness profitableWorksBoundary := by
  exact ⟨titus_regeneration_mercy, titus_profitable_works⟩

end TitusRegenerationGoodWorksWitness
end Gnosis.Witnesses.Bible.Titus
