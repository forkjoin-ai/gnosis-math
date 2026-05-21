import Init

namespace Gnosis.Witnesses.Bible.Philippians
namespace PhilippiansBondsPreachingWitness

/-!
# Philippians 1:12-18 -- Bonds Further the Gospel and Christ Is Preached

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94384-94409`.

Paul reads imprisonment as gospel propagation rather than blockage. Even impure
preaching motives are classified by the decisive output: Christ is preached.

No `sorry`, no new `axiom`.
-/

structure BondsFurtherance where
  eventsFurtherGospel : Bool := true
  bondsManifestInChrist : Bool := true
  brethrenBoldWithoutFear : Bool := true
deriving DecidableEq, Repr

def bondsFurtherance : BondsFurtherance := {}

def bondsFurtheranceWitness (b : BondsFurtherance) : Prop :=
  b.eventsFurtherGospel = true ∧ b.bondsManifestInChrist = true ∧
  b.brethrenBoldWithoutFear = true

structure MixedMotivePreaching where
  envyStrifePreachingNamed : Bool := true
  goodWillPreachingNamed : Bool := true
  contentionAddsAffliction : Bool := true
  loveKnowsDefenseOfGospel : Bool := true
  pretenceOrTruthChristPreached : Bool := true
  rejoicingInPreachedChrist : Bool := true
deriving DecidableEq, Repr

def mixedMotivePreaching : MixedMotivePreaching := {}

def outputOverMotiveWitness (m : MixedMotivePreaching) : Prop :=
  m.envyStrifePreachingNamed = true ∧ m.goodWillPreachingNamed = true ∧
  m.contentionAddsAffliction = true ∧ m.loveKnowsDefenseOfGospel = true ∧
  m.pretenceOrTruthChristPreached = true ∧ m.rejoicingInPreachedChrist = true

theorem philippians_bonds_furtherance :
    bondsFurtheranceWitness bondsFurtherance := by
  unfold bondsFurtheranceWitness bondsFurtherance
  exact ⟨rfl, rfl, rfl⟩

theorem philippians_output_over_motive :
    outputOverMotiveWitness mixedMotivePreaching := by
  unfold outputOverMotiveWitness mixedMotivePreaching
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_bonds_preaching_witness :
    bondsFurtheranceWitness bondsFurtherance ∧
    outputOverMotiveWitness mixedMotivePreaching := by
  exact ⟨philippians_bonds_furtherance, philippians_output_over_motive⟩

end PhilippiansBondsPreachingWitness
end Gnosis.Witnesses.Bible.Philippians
