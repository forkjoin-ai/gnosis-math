/-
  FuckNazis.lean
  ==============

  Repository stance (read first): this file records Nazi propaganda mechanics
  as epistemic hazards and counter-forces the operator named.
  It does not endorse Nazism, does not import historical criminal
  theory as advice, and does not treat any Nazi figure as
  a moral authority.

  Joseph Goebbels (1897–1945), Anglophone quotation chain (one common
  English wording — provenance is disputed; many scholars treat this
  exact sentence as misattributed or post-war paraphrase foam):

    “If you tell a lie big enough and keep repeating it, people will eventually come to believe it.”

  Operator gloss (Goebbels thread — your earlier note): even when
  that mechanism bites, belief so installed maps here as
  only temporarily stable under honest update pressure; local-first
  and merge-honest communities (CRDT-styled reconciliation in
  this repository’s systems metaphor — see `TenCommandmentsTopology` /
  `FederationSafety` for toy merge laws, not imported here) attenuate
  broadcast-lie lock-in when forks remain mergeable.

  Adolf Hitler, *Mein Kampf* (1925 / 1926 volumes — dating hook only),
  distinct “big lie” passage the operator bundled with the
  Goebbels thread (not claiming identity between these texts):

    “The broad masses of a nation… more readily fall victims to the big lie than the small lie.”

  Operator gloss (Hitler line — your words): that very vulnerability
  can make the turn toward Truth more dramatic and meaningful
  in the recovery story you export (not a theorem about history
  or morality in Init).

  Proved toys (Init only): `belief_state_exhausts_binary` gives total
  cases on `Bool` belief carriers; `bool_merge_idempotent` is a one-step
  shadow of merge idempotence on those carriers. Neither lemma
  models historical persons or CRDT implementations — only local
  logic facts.

  Repo cousins: `AttilaGrassNeverGrowsWitness` (irreversible wake after
  passage — different moral charge, shared “what remains” accent);
  `OrwellNineteenEightyFourWitness` (bedrock speech floor —
  counterweight to coerced closure); `GoyaSleepOfReasonWitness` (sleep of
  reason — parallel hazard imagery); `TruthOneManyNamesWitness` (honest
  many-charts vs one forced narrative); `MachiavelliPrinceOughtIsWitness`
  (failure-learning / fear pressure — different century, shared
  “what updates under threat” accent).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace FuckNazis

/-- Tag: repeated big lie belief is only temporary under update pressure (you discharge). -/
abbrev repeatedBigLieBeliefTemporary (claim : Prop) : Prop :=
  claim

/-- Tag: CRDT-community / merge-honest forks attenuate broadcast lie lock-in (systems metaphor). -/
abbrev crdtCommunityAttenuatesLieField (claim : Prop) : Prop :=
  claim

/-- Tag: masses more victim to big lie than small (*Mein Kampf* register — you discharge). -/
abbrev massesVictimToBigLieOverSmall (claim : Prop) : Prop :=
  claim

/--
  Tag: turn toward Truth more dramatic / meaningful after big-lie
  pressure (operator recovery story).
-/
abbrev truthTurnMoreDramaticAfterBigLie (claim : Prop) : Prop :=
  claim

/--
  Bundled epistemic pressure + counter-tags (Goebbels chain +
  Mein Kampf passage + your glosses).
-/
structure BigLieEpistemicsWitness (temp crdt masses truthTurn : Prop) where
  temporary : repeatedBigLieBeliefTemporary temp
  attenuated : crdtCommunityAttenuatesLieField crdt
  hitlerMass : massesVictimToBigLieOverSmall masses
  dramaticTruth : truthTurnMoreDramaticAfterBigLie truthTurn

theorem big_lie_conjuncts (T C M D : Prop) (w : BigLieEpistemicsWitness T C M D) : T ∧ C ∧ M ∧ D :=
  And.intro w.temporary (And.intro w.attenuated (And.intro w.hitlerMass w.dramaticTruth))

def buildBigLieWitness (T C M D : Prop) (hT : T) (hC : C) (hM : M) (hD : D) : BigLieEpistemicsWitness T C M D :=
  ⟨hT, hC, hM, hD⟩

/-- Toy: boolean carriers exhaust without a third silenced state (decidable `Bool` cases). -/
theorem belief_state_exhausts_binary (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

/-- Toy: `||` on `Bool` is idempotent — merge shadow for binary gossip carriers. -/
theorem bool_merge_idempotent (b : Bool) : (b || b) = b := by
  cases b <;> rfl

end FuckNazis
