import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansCrucifiedWithChristWitness

/-!
# Galatians 2:17-21 -- Crucified With Christ and Grace Not Frustrated

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93687-93699`.

The chapter closes by refusing a law-rebuild after grace: rebuilding what was
destroyed makes the agent a transgressor. The positive invariant is cruciform
life: not-I, Christ lives in me, and righteousness by law would make Christ's
death vain.

No `sorry`, no new `axiom`.
-/

structure LawRebuildCounterproof where
  christNotMinisterOfSin : Bool := true
  rebuildingDestroyedThingsTransgresses : Bool := true
  throughLawDeadToLaw : Bool := true
  liveUntoGod : Bool := true
deriving DecidableEq, Repr

def lawRebuildCounterproof : LawRebuildCounterproof := {}

def lawRebuildFrustratesGraceBoundary (l : LawRebuildCounterproof) : Prop :=
  l.christNotMinisterOfSin = true ∧
  l.rebuildingDestroyedThingsTransgresses = true ∧
  l.throughLawDeadToLaw = true ∧
  l.liveUntoGod = true

structure CruciformLife where
  crucifiedWithChrist : Bool := true
  neverthelessLive : Bool := true
  notIButChristLivesInMe : Bool := true
  liveByFaithOfSonOfGod : Bool := true
  sonLovedAndGaveHimself : Bool := true
deriving DecidableEq, Repr

def cruciformLife : CruciformLife := {}

def christLivesInMeInvariant (c : CruciformLife) : Prop :=
  c.crucifiedWithChrist = true ∧
  c.neverthelessLive = true ∧
  c.notIButChristLivesInMe = true ∧
  c.liveByFaithOfSonOfGod = true ∧
  c.sonLovedAndGaveHimself = true

structure GraceNotFrustrated where
  graceOfGodNotFrustrated : Bool := true
  righteousnessByLawRejected : Bool := true
  christDeadInVainCounterfactual : Bool := true
deriving DecidableEq, Repr

def graceNotFrustrated : GraceNotFrustrated := {}

def righteousnessByLawWouldVoidCross (g : GraceNotFrustrated) : Prop :=
  g.graceOfGodNotFrustrated = true ∧
  g.righteousnessByLawRejected = true ∧
  g.christDeadInVainCounterfactual = true

theorem galatians_law_rebuild_counterproof :
    lawRebuildFrustratesGraceBoundary lawRebuildCounterproof := by
  unfold lawRebuildFrustratesGraceBoundary lawRebuildCounterproof
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_cruciform_life :
    christLivesInMeInvariant cruciformLife := by
  unfold christLivesInMeInvariant cruciformLife
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_grace_not_frustrated :
    righteousnessByLawWouldVoidCross graceNotFrustrated := by
  unfold righteousnessByLawWouldVoidCross graceNotFrustrated
  exact ⟨rfl, rfl, rfl⟩

theorem galatians_crucified_with_christ_witness :
    lawRebuildFrustratesGraceBoundary lawRebuildCounterproof ∧
    christLivesInMeInvariant cruciformLife ∧
    righteousnessByLawWouldVoidCross graceNotFrustrated := by
  exact ⟨galatians_law_rebuild_counterproof,
    galatians_cruciform_life,
    galatians_grace_not_frustrated⟩

end GalatiansCrucifiedWithChristWitness
end Gnosis.Witnesses.Bible.Galatians
