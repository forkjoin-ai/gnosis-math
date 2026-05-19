import Init

/-
  OrwellNineteenEightyFourWitness.lean
  ====================================

  George Orwell, *Nineteen Eighty-Four* (first UK edition 8 June 1949 — composition
  1948; this file uses the 1949 publication hook the operator gave).

  Hard-culture floor (in-repo English): Orwell names a joint floor of political
  and cognitive independence — not “being edgy,” but refusing the closure of
  thought under social proof and coerced speech. In the witness stack here, that
  stance contrasts Mencken’s reduction of conscience to social telemetry
  (`MenckenConscienceShadowWitness`): telemetry can be true as sociology while still
  being fatal as a total theory of mind if it leaves no room for bedrock
  speech about shared arithmetic reality.

  Quotation (Winston’s notebook line, novel English):

    “Freedom is the freedom to say that two plus two make four. If that is granted, all else follows.”

  Lean hook: we prove the concrete `Nat` fact `2 + 2 = 4` (no axioms). The
  speech / permission half remains a tag you discharge in your political layer —
  this file does not prove a theory of rights.

  Repo cousins: `FuckNazis` (big-lie / repetition
  hazard — contrast anchor for forced narrative vs bedrock
  speech here); `GoyaSleepOfReasonWitness` (sleep of reason — prose gloss:
  suspends the operator commitment tagged “Orwellian” objective fact
  speech; parallel layer, not a proof that Goya implies this
  novel); `WildeDecayOfLyingSincerityWitness` (style / sincerity sieve — tension
  with “external fact sovereignty,” not a cancellation of `2 + 2`); `ProtagorasManIsMeasureWitness`
  (measure-man — different epistemic hazard); `ObjectivityIsIllusion` (title-level tension — not imported here);
  `JungAionShadowSuppressionWitness` (suppression — different axis).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace OrwellNineteenEightyFourWitness

/-- Concrete arithmetic bedrock used in the novel’s “2+2” idiom. -/
theorem two_plus_two_is_four : (2 : Nat) + 2 = 4 :=
  rfl

/-- Tag: “freedom to say the bedrock fact” — you supply the `Prop` (policy / jurisprudence / norm). -/
abbrev freedomToAffirmArithmetic (claim : Prop) : Prop :=
  claim

/--
  Bundles the proved `Nat` fact with a permission tag — “if that is granted…” is
  not formalized as implication here (would smuggle a whole moral logic into Init).
-/
structure CognitiveIndependenceFloorWitness (speechGranted : Prop) where
  arithmeticFact : (2 : Nat) + 2 = 4
  speechTag : freedomToAffirmArithmetic speechGranted

theorem granted_speech (S : Prop) (w : CognitiveIndependenceFloorWitness S) : S :=
  w.speechTag

def buildFloorWitness (S : Prop) (hS : S) : CognitiveIndependenceFloorWitness S :=
  ⟨two_plus_two_is_four, hS⟩

end OrwellNineteenEightyFourWitness
