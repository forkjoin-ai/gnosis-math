import Init

/-
  MumonkanGatelessGateWitness.lean
  =================================

  Zen Wúménguān (無門關), *Mumonkan* / *Gateless Gate* (compiled c. 1228 CE;
  the sentiment is older), opening of Case 1 (one English couplet):

    “The Great Way is gateless, / Approached by a thousand paths.”

  Why it stings: there is no privileged single “door” type that exhausts the
  Way — practice arrives along many honest indices. This rhymes with
  `TruthOneManyNamesWitness` (many charts, one referent), but the Zen stress here is
  pedagogy: stop hunting for the one latch to force; the “gate” was never
  installed as a separate `import`.

  Repo braids (not imported here — Init-only witness): the monorepo already
  stacks many paths into one closure in `Gnosis.Braided.BraidedTower` (tower
  phases closing on the `BraidedInfinity` family) and names pursuit / limit
  structure in `Gnosis.AchillesTortoiseLadder` (Achilles / tortoise on the ladder).
  Those modules are different mathematics; this file only points at them as
  structural cousins of “many approaches, one asymptotic spine.”

  See also: `RigVedaNasadiyaSuktaWitness` (neither/nor at the verge — opposite
  mood, same honesty about what language cannot fix as a single latch).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace MumonkanGatelessGateWitness

variable {ι : Type}

/-- One index among many approach-paths (“thousand paths”). -/
abbrev ApproachAlong (paths : ι → Prop) (i : ι) : Prop :=
  paths i

/-- User-supplied gloss that the Way is not exhausted by one exclusive gate-story. -/
abbrev GreatWayGateless (claim : Prop) : Prop :=
  claim

/--
  Bundle: a gateless tag you accept, plus every indexed path proposition you
  require at once (Init-only scaffolding).
-/
structure GreatWayThousandPathsWitness (paths : ι → Prop) (gateless : Prop) where
  gatelessWay : GreatWayGateless gateless
  eachPath : ∀ i, ApproachAlong paths i

theorem path_at (paths : ι → Prop) (gateless : Prop) (w : GreatWayThousandPathsWitness paths gateless) (i : ι) :
    paths i :=
  w.eachPath i

def buildWitness (paths : ι → Prop) (gateless : Prop) (hg : gateless) (hp : ∀ i, paths i) :
    GreatWayThousandPathsWitness paths gateless :=
  ⟨hg, hp⟩

end MumonkanGatelessGateWitness
