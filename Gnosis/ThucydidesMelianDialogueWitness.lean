/-
  ThucydidesMelianDialogueWitness.lean
  ====================================

  Thucydides, *History of the Peloponnesian War* (c. 400 BC manuscript tradition;
  the Melian Dialogue book is the usual locus), Athenian thesis (one English gloss):

    “The strong do what they can and the weak suffer what they must.”

  Greek tag (transliteration): *hōs de dynata men hoi prouchontes prassousin hoi de
  astheneis xynchōrousin* (accent / spelling varies by edition).

  Hard culture / geopolitics: Thucydides states the collision of powers as
  the invariant beneath moral appeal — not that “justice is false,” but that, in
  the dialogue’s brutal frame, justice does not compile into outcomes when
  capability is asymmetric. Power is read here as capacity, not as a
  right; suffering as dependency outcome, not as a guaranteed verdict of
  “injustice” in the opponent’s mouth.

  Chaotic-neutral thread: after `StirnerEgoAndOwnWitness` (individual sovereignty)
  and `SchopenhauerPendulumWitness` (inner kinetics), this witness is collective:
  the mechanical settlement of forces.

  Repo cousins: `MarkVineyardTenantsWitness` (tenant revolt / rent collision
  — narrative parable tags a Thucydidean floor here, not
  a proof link); `HobbesLeviathanStateOfNatureWitness` (no arbiter ⇒ civil deadlock —
  domestic floor to the same distrust);
  `MachiavelliPrinceOughtIsWitness` (Is-kernel / preservation talk);
  `ProtagorasManIsMeasureWitness` (local measure of “what is”); `TenCommandmentsTopology`
  (layer hygiene — do not confuse moral language with operator outcomes);
  `GoodhartsLaw` (proxy distortion under pressure — distant cousin).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace ThucydidesMelianDialogueWitness

/-- Capacity register — what the strong *can* do (not a “right” slot). -/
abbrev Capability (can : Prop) : Prop :=
  can

/-- Dependency outcome register — what the weak *must* bear (not a moral verdict slot). -/
abbrev DependencyOutcome (must : Prop) : Prop :=
  must

/--
  Bundle the Melian thesis: admit both the capability story and the dependency
  story without pretending they are the same `Prop` as “justice.”
-/
structure MelianCollisionWitness (strongCan weakMust : Prop) where
  strongDoes : Capability strongCan
  weakSuffers : DependencyOutcome weakMust

theorem both_halves (S W : Prop) (w : MelianCollisionWitness S W) : S ∧ W :=
  And.intro w.strongDoes w.weakSuffers

def buildWitness (S W : Prop) (hS : S) (hW : W) : MelianCollisionWitness S W :=
  ⟨hS, hW⟩

end ThucydidesMelianDialogueWitness
