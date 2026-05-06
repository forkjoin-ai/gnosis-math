/-
  SchopenhauerHorizonFallacyWitness.lean
  ======================================

  Arthur Schopenhauer, *Die Welt als Wille und Vorstellung* / *The World as Will and
  Representation* (1818 first edition; later expansions — same spine as
  `SchopenhauerPendulumWitness`). Hard-culture blow (in-repo English): “Progress”
  and “legacy” read as projection when an agent mistakes private perceptual
  bounds for cosmic bounds — the horizon fallacy (operator tag): *the limits of my
  field of vision are treated as the limits of the world.*

  Quotation (one standard English rendering):

    “Every man takes the limits of his own field of vision for the limits of the world.”

  Subversion (prose): cognitive sandbox — every epistemic life runs inside a
  frame; Schopenhauer’s sting is not “frames exist” (trivial) but “forgetting the
  frame and billing the sandbox wall as ontology.” That maps to relativity
  in the loose sense (what is “forward” depends on the chart) and to the problem of
  objectivity in the loose sense (no view-from-nowhere packaged as Init here).

  Observation / collapse (metaphor only): the ledger’s measurement idiom —
  observation selecting among admissible charts — rhymes with “forcing collapse”
  stories in physics without importing a Hilbert space: see prose in
  `NoiseIsObservational` (noise as observer-deficit, not absolute substance) and the
  Init-only contrast file `ConsciousnessVsObjectivity` (vitality vs flat “omniscience”).

  Repo cousins: `SchopenhauerPendulumWitness` (desire kinetics — same book,
  different sting); `ProtagorasManIsMeasureWitness` (anthropic measure — collision,
  not identity); `OrwellNineteenEightyFourWitness` (bedrock speech vs coerced frame);
  `MenckenConscienceShadowWitness` (observer pressure — sociology cousin); `ObjectivityIsIllusion`
  (title-level tension — not imported here).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace SchopenhauerHorizonFallacyWitness

/-- Tag: horizon fallacy — private vision-limit mistaken for world-limit (you discharge). -/
abbrev visionLimitTakenForWorldLimit (claim : Prop) : Prop :=
  claim

/-- Tag: agent runs inside a cognitive sandbox / bounded frame (not necessarily false). -/
abbrev cognitiveSandbox (claim : Prop) : Prop :=
  claim

/-- Tag: “Progress” / “legacy” undercut when horizon error is exposed (you discharge). -/
abbrev progressOrLegacyProjectionExposed (claim : Prop) : Prop :=
  claim

/--
  Bundles fallacy + sandbox recognition — no theorem that exposure implies humility.
-/
structure HorizonFallacyWitness (fallacy sandbox : Prop) where
  theFallacy : visionLimitTakenForWorldLimit fallacy
  theSandbox : cognitiveSandbox sandbox

theorem horizon_conjuncts (F S : Prop) (w : HorizonFallacyWitness F S) : F ∧ S :=
  And.intro w.theFallacy w.theSandbox

def buildHorizonWitness (F S : Prop) (hF : F) (hS : S) : HorizonFallacyWitness F S :=
  ⟨hF, hS⟩

/--
  Optional third tag: progress/legacy read as projection once the fallacy is named.
-/
structure ProgressLegacyUndercutWitness (exposure : Prop) where
  exposed : progressOrLegacyProjectionExposed exposure

end SchopenhauerHorizonFallacyWitness
