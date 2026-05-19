import Init

/-
  HobbesLeviathanStateOfNatureWitness.lean
  =======================================

  Thomas Hobbes, *Leviathan* (1651), state-of-nature litany (one English gloss —
  punctuation normalized):

    “In such condition there is no place for industry… no knowledge of the face of
    the earth; no account of time; no arts; no letters; no society; and which is
    worst of all, continual fear, and danger of violent death; and the life of man,
    solitary, poor, nasty, brutish, and short.”

  Hard culture / social contract floor: without a common power to enforce
  parity of fear (the Leviathan operator in Hobbes’ own idiom), the human
  network defaults to high-concurrency mutual threat — pure agency at every
  node against every other. Productive invariants (industry, arts, letters)
  are non-computable in the fable register because the security dependency never
  closes: a deadlock of distrust, not because humans “lack goodness,” but because
  no arbiter is assumed.

  Natural state as bug: Hobbes negates the romance of spontaneous social virtue
  under total decentralization of force — the same chaotic-neutral honesty as
  `ThucydidesMelianDialogueWitness` (collision without justice compiling), but here the
  stress is domestic / civil order, not inter-polis diplomacy alone.

  Repo cousins: `DaliSoftConstructionCivilWarWitness` (1936 canvas — private
  war as auto-strangulation; visual kin, not a proof of Hobbes);
  `ThucydidesMelianDialogueWitness`; `MachiavelliPrinceOughtIsWitness`;
  `TenCommandmentsTopology` (layer hygiene — Leviathan as claimed operator must be
  typed honestly); `StirnerEgoAndOwnWitness` (sovereignty talk — different solution,
  same distrust substrate).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace HobbesLeviathanStateOfNatureWitness

/-- The “no industry / no arts…” bundle — user supplies the collapsed `Prop`. -/
abbrev NaturalStateBug (horror : Prop) : Prop :=
  horror

/-- The common power / arbiter slot Hobbes says is required for productive peace. -/
abbrev LeviathanArbiter (arbiter : Prop) : Prop :=
  arbiter

/--
  Witness: you admit both the natural-state failure mode and the arbiter
  dependency (no identification of the two `Prop`s).
-/
structure LeviathanFloorWitness (stateOfNature arbiter : Prop) where
  decentralizedHell : NaturalStateBug stateOfNature
  parityOperator : LeviathanArbiter arbiter

theorem both_claims (S A : Prop) (w : LeviathanFloorWitness S A) : S ∧ A :=
  And.intro w.decentralizedHell w.parityOperator

def buildWitness (S A : Prop) (hS : S) (hA : A) : LeviathanFloorWitness S A :=
  ⟨hS, hA⟩

end HobbesLeviathanStateOfNatureWitness
