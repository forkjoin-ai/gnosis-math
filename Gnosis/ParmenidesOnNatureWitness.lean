import Init

/-
  ParmenidesOnNatureWitness.lean
  ==============================

  Parmenides of Elea (Greek, c. 475 BC), *On Nature* (Περὶ φύσεως), gateway
  fragment (one English lineation):

    “It is; / for it is not possible / for nothing / to be.”

  Zero-axiom floor (prose): in-repo this is read as the identity invariant
  at the base of the ontology stack: Being is typed as non-empty — there is
  no legitimate witness that Nothing (`Empty`) is in the same sense. Lean’s
  Init layer already agrees: there is no `Nonempty Empty`, and there is no
  “activity” of nothing except vacuous function space (`Empty → α` is unique).
  This file does not import metaphysics modules; it only packages a few Init
  tautologies the poem is analogous to.

  Shape: the identity invariant — `rfl` on a witness you already hold;
  refusal of a contradictory witness for non-being.

  Repo cousins: `HeraclitusBowLifeDeathWitness` (linguistic tension on one
  implement); `HeraclitusUpDownPathWitness` (B60 path vs observer metadata);
  `LaoziBowlVoidFunctionWitness` (Ch.11 productive void vs Eleatic `Empty`);
  `RigVedaNasadiyaSuktaWitness` (neither existence nor “nothingness” at t₀);
  `HeartTongueTotalNegationWitness` (twin denials of interface myths);
  `PhilosophicalAllegories` (allegory spine); `ParticlesExist` (later “something is”
  science stack — different file, same broad direction).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace ParmenidesOnNatureWitness

/-- Parmenidean “It is”: Being carries at least one witness (`Nonempty α`). -/
abbrev ItIs (α : Type) [Nonempty α] : Nonempty α :=
  inferInstance

/-- “Nothing” cannot be — no witness for `Nonempty Empty`. -/
theorem impossible_for_nothing_to_be : ¬ Nonempty Empty := by
  intro ⟨x⟩
  exact nomatch x

/-- Identity invariant on any witness you already possess. -/
theorem identity_invariant {α : Type} (a : α) : a = a :=
  rfl

/-- Every arrow out of `Empty` is definitionally the vacuous map (no active operator). -/
theorem empty_arrow_unique {α : Type} (f g : Empty → α) : f = g := by
  funext e
  cases e

end ParmenidesOnNatureWitness
