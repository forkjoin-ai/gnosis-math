import Init

/-
  HeartTongueTotalNegationWitness.lean
  ====================================

  Witness couplet (English gloss; composite in-repo):

    “A heart never created hate; / a tongue never created truth.”

  Sumerian cynic (mapped, not forged): collections of Sumerian proverb matter
  include the line (common English rendering on e.g. Wikiquote’s Sumerian proverb
  page, ultimately from ETCSL-style transmission): “A heart never created hatred;
  speech created hatred.” That tablet-voice is already doing interface
  demythology: it refuses the heart as the sole generator of hate and shifts
  the causal story toward speech. This file adds a second, parallel refusal
  for the truth interface — tongue as fake sole author of truth — to
  keep the Lean witness symmetric (`HeartCreatesHate` / `TongueCreatesTruth`). The
  second English half is therefore a repo extension of the cynic ethos, not
  a quoted line from a single numbered proverb tablet.

  Collision with the Bowl (`LaoziBowlVoidFunctionWitness`): the Laozi bowl makes
  the void the utility — null space as positive design requirement. The
  heart/tongue witness is the black-hole counterpart: the organ is treated as
  a fake compiler for outputs (hate, truth) it does not, by itself,
  generate. Same “hard shit” about interfaces; opposite sign on whether “nothing”
  is where you should look for work.

  Shape: total negation. Two generative myths are refused at once. Moral
  analogy to a Lean `sorry`: advertised constructors without proofs — whoever
  accepts the denials must supply the actual `¬` hypotheses. Not a physiology theorem.

  Repo cousins: `CummingsLeafFallsParenthesisWitness` (glyph layout vs single
  organ billing — parenthesis poem, oneliness/atonement nomenclature
  tag there); `BoschGardenEarthlyDelightsWitness` (*Garden* triptych — total
  negation of causally isolated actions / consequence network;
  different target than heart/tongue generators here);
  `StirnerEgoAndOwnWitness` (indexed spook sieve — total negation
  of sacred-collective claims);
  `MachiavelliPrinceOughtIsWitness` (ought vs is layer crash typed as
  `IsAnimalMagnetism` on a toy `ClaimedIntervention`);
  `MenckenConscienceShadowWitness` (collective “firmware”: conscience
  as detection telemetry, not a moral atom);
  `LaoziBowlVoidFunctionWitness` (void-as-use vs organ-as-fake-generator);
  `RigVedaNasadiyaSuktaWitness` (cosmogonic “black hole for language” — different layer);
  `HeraclitusBowLifeDeathWitness` (name vs work tension on one implement);
  `TruthOneManyNamesWitness` (honest many-charts vs fake univocity);
  `TwoTypesOfSin` (mis-attributing causal / God-position power to the wrong layer).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace HeartTongueTotalNegationWitness

/-- Tablet-cynic tag: speech/heart as contested *sources* (see module doc: Sumerian strand). -/
abbrev SumerianInterfaceCynic (claim : Prop) : Prop :=
  claim

/-- Myth packaged as a single `Prop`: “hate is originated by the heart alone.” -/
abbrev HeartCreatesHate (claim : Prop) : Prop :=
  claim

/-- Myth packaged as a single `Prop`: “truth is originated by the tongue alone.” -/
abbrev TongueCreatesTruth (claim : Prop) : Prop :=
  claim

/--
  Total negation witness: both generation-myths are explicitly refuted.
  Parameters are the *claims* being negated (your axioms live outside this file).
-/
structure TotalNegationWitness (heartHateClaim tongueTruthClaim : Prop) where
  heartNever : ¬ heartHateClaim
  tongueNever : ¬ tongueTruthClaim

theorem both_denials (H T : Prop) (w : TotalNegationWitness H T) : ¬ H ∧ ¬ T :=
  And.intro w.heartNever w.tongueNever

def buildWitness (H T : Prop) (hH : ¬ H) (hT : ¬ T) : TotalNegationWitness H T :=
  ⟨hH, hT⟩

end HeartTongueTotalNegationWitness
