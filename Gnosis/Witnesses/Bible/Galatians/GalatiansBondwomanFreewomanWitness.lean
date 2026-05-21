import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansBondwomanFreewomanWitness

/-!
# Galatians 4:21-31 -- Bondwoman, Freewoman, and Promise Children

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93837-93866`.

Galatians reads the two sons as a covenant topology: flesh-birth and bondage on
one side, promise-birth and freedom on the other. This module covers the
Galatians argument layer; Genesis source anchors live in the Torah witness.

No `sorry`, no new `axiom`.
-/

structure TwoSonsAllegory where
  lawHearersQuestioned : Bool := true
  abrahamTwoSonsNamed : Bool := true
  bondmaidSonAfterFlesh : Bool := true
  freewomanSonByPromise : Bool := true
  twoCovenantsAllegoryNamed : Bool := true
  sinaiGeneratesBondage : Bool := true
  jerusalemAboveFreeMother : Bool := true
deriving DecidableEq, Repr

def twoSonsAllegory : TwoSonsAllegory := {}

def covenantTopologyWitness (a : TwoSonsAllegory) : Prop :=
  a.lawHearersQuestioned = true ∧
  a.abrahamTwoSonsNamed = true ∧
  a.bondmaidSonAfterFlesh = true ∧
  a.freewomanSonByPromise = true ∧
  a.twoCovenantsAllegoryNamed = true ∧
  a.sinaiGeneratesBondage = true ∧
  a.jerusalemAboveFreeMother = true

structure PromiseFreedomChildren where
  barrenRejoicingQuoted : Bool := true
  isaacPatternPromiseChildren : Bool := true
  fleshPersecutesSpiritPattern : Bool := true
  bondwomanCastOutQuoted : Bool := true
  bondwomanSonNotHeir : Bool := true
  notBondwomanChildrenButFree : Bool := true
deriving DecidableEq, Repr

def promiseFreedomChildren : PromiseFreedomChildren := {}

def promiseFreedomWitness (p : PromiseFreedomChildren) : Prop :=
  p.barrenRejoicingQuoted = true ∧
  p.isaacPatternPromiseChildren = true ∧
  p.fleshPersecutesSpiritPattern = true ∧
  p.bondwomanCastOutQuoted = true ∧
  p.bondwomanSonNotHeir = true ∧
  p.notBondwomanChildrenButFree = true

theorem galatians_covenant_topology :
    covenantTopologyWitness twoSonsAllegory := by
  unfold covenantTopologyWitness twoSonsAllegory
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_promise_freedom :
    promiseFreedomWitness promiseFreedomChildren := by
  unfold promiseFreedomWitness promiseFreedomChildren
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_bondwoman_freewoman_witness :
    covenantTopologyWitness twoSonsAllegory ∧
    promiseFreedomWitness promiseFreedomChildren := by
  exact ⟨galatians_covenant_topology,
    galatians_promise_freedom⟩

end GalatiansBondwomanFreewomanWitness
end Gnosis.Witnesses.Bible.Galatians
