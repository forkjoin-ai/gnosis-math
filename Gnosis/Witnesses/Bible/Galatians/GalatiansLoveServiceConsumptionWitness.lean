import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansLoveServiceConsumptionWitness

/-!
# Galatians 5:13-15 -- Liberty for Love-Service, Not Flesh Occasion

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93901-93910`.

Freedom has a misuse mode. Galatians rejects liberty as an occasion to flesh and
marks love-service as the law-fulfilling path. Mutual biting and devouring is
the antitheorem: freedom collapsed into intra-body consumption.

No `sorry`, no new `axiom`.
-/

structure LibertyUse where
  calledUntoLiberty : Bool := true
  libertyNotOccasionToFlesh : Bool := true
  byLoveServeOneAnother : Bool := true
deriving DecidableEq, Repr

def libertyUse : LibertyUse := {}

def libertyForLoveService (l : LibertyUse) : Prop :=
  l.calledUntoLiberty = true ∧
  l.libertyNotOccasionToFlesh = true ∧
  l.byLoveServeOneAnother = true

structure LawFulfilledLove where
  allLawFulfilledInOneWord : Bool := true
  loveNeighborAsSelf : Bool := true
  bitingAndDevouringWarned : Bool := true
  mutualConsumptionThreatNamed : Bool := true
deriving DecidableEq, Repr

def lawFulfilledLove : LawFulfilledLove := {}

def lovePreventsConsumption (l : LawFulfilledLove) : Prop :=
  l.allLawFulfilledInOneWord = true ∧
  l.loveNeighborAsSelf = true ∧
  l.bitingAndDevouringWarned = true ∧
  l.mutualConsumptionThreatNamed = true

theorem galatians_liberty_for_love_service :
    libertyForLoveService libertyUse := by
  unfold libertyForLoveService libertyUse
  exact ⟨rfl, rfl, rfl⟩

theorem galatians_love_prevents_consumption :
    lovePreventsConsumption lawFulfilledLove := by
  unfold lovePreventsConsumption lawFulfilledLove
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_love_service_consumption_witness :
    libertyForLoveService libertyUse ∧
    lovePreventsConsumption lawFulfilledLove := by
  exact ⟨galatians_liberty_for_love_service,
    galatians_love_prevents_consumption⟩

end GalatiansLoveServiceConsumptionWitness
end Gnosis.Witnesses.Bible.Galatians
