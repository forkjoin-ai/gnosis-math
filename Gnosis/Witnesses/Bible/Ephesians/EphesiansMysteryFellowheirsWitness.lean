import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansMysteryFellowheirsWitness

/-!
# Ephesians 3:1-13 -- Mystery, Fellowheirs, and Manifold Wisdom

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94104-94131`.

The hidden mystery becomes public topology: Gentiles are fellowheirs, same body,
and partakers of promise. The church becomes the disclosure surface for manifold
wisdom to powers.

No `sorry`, no new `axiom`.
-/

structure MysteryFellowheirs where
  prisonerForGentiles : Bool := true
  mysteryMadeKnownByRevelation : Bool := true
  nowRevealedBySpirit : Bool := true
  gentilesFellowheirs : Bool := true
  gentilesSameBody : Bool := true
  gentilesPromisePartakers : Bool := true
  ministerByGracePower : Bool := true
deriving DecidableEq, Repr

def mysteryFellowheirs : MysteryFellowheirs := {}

def fellowheirMysteryWitness (m : MysteryFellowheirs) : Prop :=
  m.prisonerForGentiles = true ∧ m.mysteryMadeKnownByRevelation = true ∧
  m.nowRevealedBySpirit = true ∧ m.gentilesFellowheirs = true ∧
  m.gentilesSameBody = true ∧ m.gentilesPromisePartakers = true ∧
  m.ministerByGracePower = true

structure ManifoldWisdom where
  leastSaintPreachesRiches : Bool := true
  fellowshipOfMysterySeen : Bool := true
  hiddenInCreatorGod : Bool := true
  wisdomKnownByChurch : Bool := true
  principalitiesAndPowersAddressed : Bool := true
  eternalPurposeInChrist : Bool := true
  boldAccessByFaith : Bool := true
  tribulationsNotFaintingGlory : Bool := true
deriving DecidableEq, Repr

def manifoldWisdom : ManifoldWisdom := {}

def manifoldWisdomWitness (w : ManifoldWisdom) : Prop :=
  w.leastSaintPreachesRiches = true ∧ w.fellowshipOfMysterySeen = true ∧
  w.hiddenInCreatorGod = true ∧ w.wisdomKnownByChurch = true ∧
  w.principalitiesAndPowersAddressed = true ∧ w.eternalPurposeInChrist = true ∧
  w.boldAccessByFaith = true ∧ w.tribulationsNotFaintingGlory = true

theorem ephesians_fellowheir_mystery :
    fellowheirMysteryWitness mysteryFellowheirs := by
  unfold fellowheirMysteryWitness mysteryFellowheirs
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_manifold_wisdom :
    manifoldWisdomWitness manifoldWisdom := by
  unfold manifoldWisdomWitness manifoldWisdom
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_mystery_fellowheirs_witness :
    fellowheirMysteryWitness mysteryFellowheirs ∧
    manifoldWisdomWitness manifoldWisdom := by
  exact ⟨ephesians_fellowheir_mystery, ephesians_manifold_wisdom⟩

end EphesiansMysteryFellowheirsWitness
end Gnosis.Witnesses.Bible.Ephesians
