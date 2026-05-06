/-
  BowieChangesWitness.lean
  ========================

  David Bowie (1947–2016), “Changes” (released 1971 on *Hunky Dory*).

  Hard-culture floor (in-repo English): Heraclitean flux maps here to
  the primary driver of the individual — self as sequence under
  revision, not a frozen SKU in time (compare `HeraclitusRiverTwiceWitness`;
  this file does not prove Bowie read DK fragments in Lean).

  Quotation (bridge / tag lines, English as commonly printed):

    “Time may change me /
    But I can’t trace time.”

  Lyric register: the speaker tags inability to read the clock
  back from inside the change — phenomenological blind spot as
  confession, not a theorem about physics.

  Operator inversion (repo spine, your gloss): changes do trace
  time — i.e. the sequence of revisions is already a timelike
  record you can read from outside or post-hoc even when
  local felt time won’t parse; this inverts the lyric’s “can’t
  trace” brag into a counter-claim you discharge as your own
  `Prop`, not as Bowie’s exegesis.

  Proved toy (Init only): `lyric_adjacent_years_distinct` is a pure
  `Nat` inequality of two calendar hooks neighboring the song
  era — not musicology, only a concrete reminder that distinct
  indices exist to anchor revision traces.

  Repo cousins: `HeraclitusRiverTwiceWitness` (river / self flux — canonical
  ancient template); `HeraclitusBowLifeDeathWitness` (name vs work on
  one implement — different fragment, same family); `ShipOfTheseusWitness`
  (σ-template across replacement); `CohenAnthemWitness` (release without
  perfect seal — different decade, shared revision ethos); `JoplinMeAndBobbyMcGeeWitness`
  (1970 chorus neighbor — pop voice on freedom/loss, not
  flux lemma here).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace BowieChangesWitness

/-- Tag: Heraclitean flux as driver of individual self-revision (you discharge). -/
abbrev heracliteanFluxDrivesIndividual (claim : Prop) : Prop :=
  claim

/-- Tag: lyric confession — “can’t trace time” from inside change (song register). -/
abbrev lyricCannotTraceTime (claim : Prop) : Prop :=
  claim

/-- Tag: operator inversion — changes trace time / revision is timelike record (your `Prop`). -/
abbrev operatorChangesTraceTime (claim : Prop) : Prop :=
  claim

/--
  Changes bundle: flux floor + lyric tag + inversion tag.
-/
structure ChangesFluxWitness (flux lyric inversion : Prop) where
  driver : heracliteanFluxDrivesIndividual flux
  blindSpot : lyricCannotTraceTime lyric
  traceRecord : operatorChangesTraceTime inversion

theorem changes_conjuncts (F L I : Prop) (w : ChangesFluxWitness F L I) : F ∧ L ∧ I :=
  And.intro w.driver (And.intro w.blindSpot w.traceRecord)

def buildChangesWitness (F L I : Prop) (hF : F) (hL : L) (hI : I) : ChangesFluxWitness F L I :=
  ⟨hF, hL, hI⟩

/-- Toy: distinct calendar indices for the 1970/1971 pop neighborhood (not discography). -/
theorem lyric_adjacent_years_distinct : (1970 : Nat) ≠ 1971 := by
  decide

end BowieChangesWitness
