import Init

/-
  LaoziBowlVoidFunctionWitness.lean
  =================================

  Laozi (老子), *Dao De Jing* / *Tao Te Ching*, Chapter 11 (one English gloss):

    “The bowl is most useful where it is empty.”

  Why it stings: as a witness against object-only thinking (clay / surface /
  “the class you can instantiate” as the whole story): utility is typed by the
  cavity — the null space is not a defect to patch out, but the primary
  functional requirement. “Nothing” here is not logical non-being; it is the
  honest use-site you design around.

  Parmenides fence: do not conflate this with `ParmenidesOnNatureWitness`
  (`¬ Nonempty Empty`). The Eleatic gate refuses a witness for sheer non-being;
  the Taoist bowl refuses the fantasy that solid without void could carry the
  same use. Different negations, different jobs.

  Repo cousins: `CummingsLeafFallsParenthesisWitness` (interior typed inside
  a word-shell — metaphor rhyme only); `CohenAnthemWitness` (crack admits light — popular rhyme
  with productive imperfection, not the Daoist lemma proved
  here); `MenckenConscienceShadowWitness` (shadow-metric on “inner voice”);
  `EpicurusTetrapharmakosWitness` (atoms / sensation “Is”, gods non-operators);
  `ParmenidesOnNatureWitness`; `ShipOfTheseusWitness`
  (material vs form registers on one object); `RigVedaNasadiyaSuktaWitness`
  (neither/nor at the cosmogonic verge); `HeraclitusBowLifeDeathWitness`
  (tension between name and work); `HeartTongueTotalNegationWitness` (collision:
  bowl says void = use; heart/tongue says organ ≠ generator — “black hole”
  to the bowl’s productive null space); `SemanticPolysemySieve` (meaning pressure at boundaries).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace LaoziBowlVoidFunctionWitness

/-- The material story: walls exist (the “object” you can point at). -/
abbrev ClayShell (shell : Prop) : Prop :=
  shell

/--
  The null space as *positive* design fact: emptiness is where the function lives
  (the “hard” requirement, not an absence to eliminate).
-/
abbrev CavityAsUseSite (voidFunctional : Prop) : Prop :=
  voidFunctional

/--
  Chapter 11 bowl witness: both shell and cavity are asserted — utility is not
  reducible to clay alone.
-/
structure BowlVoidFunctionWitness (clay voidFunctional : Prop) where
  hasShell : ClayShell clay
  voidCarriesUse : CavityAsUseSite voidFunctional

theorem shell_and_void_together (c v : Prop) (w : BowlVoidFunctionWitness c v) : c ∧ v :=
  And.intro w.hasShell w.voidCarriesUse

def buildWitness (c v : Prop) (hc : c) (hv : v) : BowlVoidFunctionWitness c v :=
  ⟨hc, hv⟩

end LaoziBowlVoidFunctionWitness
