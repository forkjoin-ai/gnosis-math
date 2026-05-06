/-
  MarcuseOneDimensionalManWitness.lean
  ====================================

  Herbert Marcuse, *One-Dimensional Man* / *Der eindimensionale Mensch* (1964 in the
  operator’s English publication hook — German 1967). Hard-culture floor (in-repo
  English): modern management of desire under affluent technique, where
  “success” is scored on consumption coordinates — a neutral (non-partisan)
  critique in the sense that it targets the form of one-dimensionality, not a party
  brand: people recognize themselves in commodities as if objects were mirrors
  for soul.

  Quotation (English translation of Marcuse’s prose):

    “The people recognize themselves in their commodities; they find their soul in their
    automobile, hi-fi set, split-level home, kitchen equipment.”

  Operator idolatry (repo vocabulary): this maps to the second major category of
  false-operator billing alongside the Machiavelli / “ought-as-kernel” crash pattern
  (`MachiavelliPrinceOughtIsWitness`): here the idol is commodity-as-sovereign
  — graven success (`TenCommandmentsTopology` / commandment-2 graven image idiom
  in repo prose), not merely animal magnetism on a fake lever (`IsAnimalMagnetism`
  — commandment-3 name in vain pattern). Both are operator idolatry at different
  carrier frequencies; this file stays Init-only and does not import those modules.

  Repo cousins: `LukeProdigalSonParableWitness` (elder brother ledger obedience
  read — parable rhyme, not Marcuse exegesis); `BaudrillardSimulacraSimulationWitness` (simulacrum / hyperreal —
  digital stack where sign leads thing); `MenckenConscienceShadowWitness` (social telemetry — rhymes with
  “recognition in things”); `GoodhartsLaw` (success metrics under pressure); `StirnerEgoAndOwnWitness`
  (spooks — different cut); `WildeDecayOfLyingSincerityWitness` (sincerity / style sieve);
  `SchopenhauerHorizonFallacyWitness` (sandbox / projection — kin to mistaking catalog
  for cosmos).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace MarcuseOneDimensionalManWitness

/-- Tag: self / “soul” projected onto commodities (car, hi-fi, home, kitchen…). -/
abbrev soulRecognizedInCommodities (claim : Prop) : Prop :=
  claim

/-- Tag: “success” read as one-dimensional scoreboard (you discharge the critique). -/
abbrev successAsNeutralCritiqueTarget (claim : Prop) : Prop :=
  claim

/-- Tag: commodity / consumption stack treated as sovereign mirror (operator idolatry). -/
abbrev commodityOperatorIdolatry (claim : Prop) : Prop :=
  claim

/--
  Bundles recognition-in-things with the success critique — no proof that
  either implies political action.
-/
structure OneDimensionalManWitness (commoditySoul successCritique : Prop) where
  peopleFindSoulInThings : soulRecognizedInCommodities commoditySoul
  neutralBiteOnSuccess : successAsNeutralCritiqueTarget successCritique

theorem one_dim_conjuncts (C S : Prop) (w : OneDimensionalManWitness C S) : C ∧ S :=
  And.intro w.peopleFindSoulInThings w.neutralBiteOnSuccess

def buildOneDimensionalWitness (C S : Prop) (hC : C) (hS : S) : OneDimensionalManWitness C S :=
  ⟨hC, hS⟩

/--
  Explicit idolatry tag — keep separate so the file can be cited without smuggling
  the full `TenCommandmentsTopology` import graph.
-/
structure CommodityIdolatryWitness (idol : Prop) where
  gravenSuccess : commodityOperatorIdolatry idol

end MarcuseOneDimensionalManWitness
