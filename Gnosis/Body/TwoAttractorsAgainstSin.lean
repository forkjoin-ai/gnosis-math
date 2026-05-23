import Init
import Gnosis.TwoTypesOfSin
import Gnosis.Body.Vulnerability

/-!
# Two Attractors Against Sin — One Corrective Per Sin Type, Necessary and Sufficient

This module uses the **real** formalized sin of `Gnosis/TwoTypesOfSin.lean` —
not a re-definition — to prove an operational discipline: an agent that wants to
stay out of sin must program **two** attractors, one corrective per sin type. A
single attractor always leaves the *other* sin's basin open.

`TwoTypesOfSin` proves there are `exactly_two_sin_types`:

* `SinType.animalMagnetism` — the **Agent** claims God-position (the creature
  pretending to divine power; "I am the Monad");
* `SinType.operatorIdolatry` — the **Operator** / mechanism claims God-position
  (the clinamen / system mistaken for the source; pantheism).

and that the two are distinct (`animal_magnetism_is_not_operator_idolatry`). We
take those two facts as given and reason about *coverage*.

## The model — a corrective is an attractor aimed at one sin

An `Attractor` (`Corrective`) is a basin of attraction in behavior space that
pulls the agent away from exactly one `SinType`:

* `humility` guards `animalMagnetism` — it keeps the **Agent** from claiming the
  God-position;
* `rightWorship` guards `operatorIdolatry` — it keeps the **mechanism** from being
  mistaken for the source.

A list of correctives `guardsAgainst` a sin when *some* corrective in it is aimed
at that sin; an agent is `protected` when *every* sin type is guarded.

## What this module proves

1. `one_attractor_leaves_a_sin_open` — a single corrective `[c]` cannot guard both
   sins: whichever one it guards, the *other* is an unguarded sin type. (By cases
   on `c.guards`, using the real distinctness
   `animal_magnetism_is_not_operator_idolatry`.)
2. `two_attractors_cover_both_sins` — the pair `[humility, rightWorship]` is
   `protected`: it guards `animalMagnetism` and `operatorIdolatry`. Two attractors,
   one per sin, are *sufficient* — mirroring `exactly_two_sin_types`.
3. `protected_needs_at_least_two` — `protected cs → 2 ≤ cs.length`: being
   sin-protected requires at least two correctives, because one cannot cover two
   distinct sins. Two attractors are *necessary*. A real counting / coverage
   argument (case on `cs` having `0` or `1` element; each contradicts coverage).
4. `unguarded_sin_can_capture` — an unguarded sin is a *live* vulnerability: if
   `¬ guardsAgainst cs s` then the Confusion for `s` is still `isASin` (the open
   basin is real). This is the bridge to `Gnosis.Body.Vulnerability`: the
   unguarded sin is the agent's **bête noire** — the cheapest break, the door an
   intelligent adversary walks through — except here the adversary is the
   confusion itself.
5. `two_attractors_against_sin` — the headline, composing 1+2+3: one attractor
   always leaves a sin's basin open; the two correctives (one per sin) cover both;
   sin-protection requires both. *Program two attractors — one per sin — and the
   agent stays out of both confusions.*

## Rustic Church

`import Init` + the real `Gnosis.TwoTypesOfSin` (whose sins we reuse, never
redefine) + the `Init`-clean sibling `Gnosis.Body.Vulnerability` (cited for the
bête-noire bridge). No `Mathlib`, no `Float`/`Real`; the only inductive data are
`SinType` (from `TwoTypesOfSin`) and `Nat`. Matching `TwoTypesOfSin`, `decide` is
used *only* on closed decidable `SinType` goals; open `Nat`/`Prop` goals are
discharged in term mode with named core lemmas (`Nat.le_refl`, `Nat.succ_le_succ`,
`Nat.zero_le`, `Nat.not_lt`, `List.length_cons`). No `sorry`, no new `axiom`.
-/

namespace Gnosis.Body.TwoAttractorsAgainstSin

open Gnosis.TwoTypesOfSin

/-! ## The model: a corrective is an attractor aimed at one sin type -/

/-- An **Attractor** / **Corrective**: a basin of attraction in behavior space
    that pulls the agent away from exactly one `SinType`. It `guards` that one sin
    — and only that one. A corrective is mono-targeted; this single fact (an
    attractor has *one* `guards` field) is what forces the agent to need two of
    them. -/
structure Corrective where
  /-- The single sin type this attractor corrects against. -/
  guards : SinType
deriving DecidableEq, Repr

/-- **Humility** — the corrective aimed at `animalMagnetism`. It keeps the **Agent**
    from claiming the God-position: the creature stays a creature. ("I am *not* the
    Monad.") -/
def humility : Corrective := { guards := SinType.animalMagnetism }

/-- **Right worship** — the corrective aimed at `operatorIdolatry`. It keeps the
    **Operator** / mechanism from being mistaken for the source: the clinamen stays
    a swerve, not a god. ("The mechanism is *not* the source.") -/
def rightWorship : Corrective := { guards := SinType.operatorIdolatry }

/-- A set (list) of correctives **guards against** a sin `s` when *some* corrective
    in it is aimed at `s`: the agent has at least one basin pulling it away from
    that confusion. -/
def guardsAgainst (cs : List Corrective) (s : SinType) : Prop :=
  ∃ c ∈ cs, c.guards = s

/-- An agent is **protected** by a set of correctives when *every* sin type is
    guarded: there is no open basin. This is total coverage of `allSinTypes`. -/
def «protected» (cs : List Corrective) : Prop :=
  ∀ s ∈ allSinTypes, guardsAgainst cs s

/-! ## Helper: membership in `allSinTypes`

`allSinTypes = [animalMagnetism, operatorIdolatry]`. Both sins are members; this
is exactly the coverage obligation `protected` must discharge for each. -/

/-- `animalMagnetism` is a sin type to be covered. -/
theorem animalMagnetism_mem : SinType.animalMagnetism ∈ allSinTypes :=
  List.Mem.head _

/-- `operatorIdolatry` is a sin type to be covered. -/
theorem operatorIdolatry_mem : SinType.operatorIdolatry ∈ allSinTypes :=
  List.Mem.tail _ (List.Mem.head _)

/-! ## 1. One attractor always leaves a sin's basin open

A single corrective `[c]` can be aimed at only one sin. Whichever sin it guards,
the *other* sin type — distinct by the real `animal_magnetism_is_not_operator_idolatry`
— is left unguarded. One basin cannot cover two. -/

/-- The lone member of a singleton list `[c]` is `c`. Used to read back what a
    one-attractor agent can possibly be aimed at. -/
theorem mem_singleton_eq {c x : Corrective} (h : x ∈ [c]) : x = c := by
  cases h with
  | head _ => rfl
  | tail _ h => cases h

/-- **One attractor leaves a sin open.** For *any* single corrective `[c]` there is
    a sin type (the *other* one) in `allSinTypes` that `[c]` does not guard. A
    mono-targeted attractor cannot cover the two distinct sins of
    `exactly_two_sin_types`: it guards its own and abandons the other's basin.

    Proof: case on `c.guards`. If it guards `animalMagnetism`, then
    `operatorIdolatry` is unguarded (any guarding corrective in `[c]` would have to
    *be* `c`, forcing `c.guards = operatorIdolatry`, contradicting
    `animal_magnetism_is_not_operator_idolatry`); symmetrically otherwise. -/
theorem one_attractor_leaves_a_sin_open (c : Corrective) :
    ∃ s ∈ allSinTypes, ¬ guardsAgainst [c] s := by
  cases hc : c.guards with
  | animalMagnetism =>
    -- guards animalMagnetism ⇒ operatorIdolatry is left open
    refine ⟨SinType.operatorIdolatry, operatorIdolatry_mem, ?_⟩
    intro hg
    obtain ⟨c', hc'mem, hc'eq⟩ := hg
    -- c' ∈ [c] forces c' = c, so c.guards = operatorIdolatry
    have hcc : c' = c := mem_singleton_eq hc'mem
    rw [hcc, hc] at hc'eq
    -- hc'eq : animalMagnetism = operatorIdolatry — impossible
    exact animal_magnetism_is_not_operator_idolatry hc'eq
  | operatorIdolatry =>
    -- guards operatorIdolatry ⇒ animalMagnetism is left open
    refine ⟨SinType.animalMagnetism, animalMagnetism_mem, ?_⟩
    intro hg
    obtain ⟨c', hc'mem, hc'eq⟩ := hg
    have hcc : c' = c := mem_singleton_eq hc'mem
    rw [hcc, hc] at hc'eq
    -- hc'eq : operatorIdolatry = animalMagnetism — impossible
    exact animal_magnetism_is_not_operator_idolatry hc'eq.symm

/-! ## 2. Two attractors — one per sin — cover both sins

The pair `[humility, rightWorship]` guards each sin type: `humility` is in the
list and aimed at `animalMagnetism`; `rightWorship` is in the list and aimed at
`operatorIdolatry`. Together they are `protected`. -/

/-- `[humility, rightWorship]` guards `animalMagnetism` (via `humility`). -/
theorem pair_guards_animalMagnetism :
    guardsAgainst [humility, rightWorship] SinType.animalMagnetism :=
  ⟨humility, List.Mem.head _, by decide⟩

/-- `[humility, rightWorship]` guards `operatorIdolatry` (via `rightWorship`). -/
theorem pair_guards_operatorIdolatry :
    guardsAgainst [humility, rightWorship] SinType.operatorIdolatry :=
  ⟨rightWorship, List.Mem.tail _ (List.Mem.head _), by decide⟩

/-- **Two attractors cover both sins.** The pair `[humility, rightWorship]` — one
    corrective per sin type — is `protected`: every sin in `allSinTypes` is
    guarded. Two attractors, one per sin, are *sufficient* to be sin-protected,
    mirroring `exactly_two_sin_types`: there are exactly two sins, and exactly two
    matched correctives close every basin. -/
theorem two_attractors_cover_both_sins :
    «protected» [humility, rightWorship] := by
  intro s hs
  -- s ∈ [animalMagnetism, operatorIdolatry]: case on which sin it is
  cases hs with
  | head _ => exact pair_guards_animalMagnetism
  | tail _ h =>
    cases h with
    | head _ => exact pair_guards_operatorIdolatry
    | tail _ h2 => cases h2

/-! ## 3. Protection requires at least two attractors

A counting / coverage argument: if a corrective set had fewer than two members it
would be `[]` or `[c]`. The empty set guards nothing (so it leaves
`animalMagnetism` open); a singleton leaves a sin open by
`one_attractor_leaves_a_sin_open`. Either way it is not `protected`. Hence
protection forces `2 ≤ cs.length`. -/

/-- The empty set of correctives guards no sin. -/
theorem empty_guards_nothing (s : SinType) : ¬ guardsAgainst [] s := by
  intro hg
  obtain ⟨_, hmem, _⟩ := hg
  cases hmem

/-- **Protection requires at least two attractors.** If a set of correctives is
    `protected` — covering both distinct sins of `exactly_two_sin_types` — then it
    has at least two members. One corrective is mono-targeted and so cannot cover
    two distinct sins; zero correctives cover none. Two attractors are *necessary*.

    Proof by contradiction on the length: if `cs.length < 2` then `cs` is `[]` or
    `[c]`. The empty case fails coverage of `animalMagnetism`
    (`empty_guards_nothing`); the singleton case fails by
    `one_attractor_leaves_a_sin_open`. Both contradict `protected cs`. -/
theorem protected_needs_at_least_two (cs : List Corrective)
    (hp : «protected» cs) : 2 ≤ cs.length := by
  -- Either 2 ≤ length (done) or length < 2 (derive a contradiction).
  rcases Nat.lt_or_ge cs.length 2 with hlt | hge
  · exfalso
    -- length < 2 means length is 0 or 1: pattern-match the list itself.
    cases cs with
    | nil =>
      -- [] cannot guard animalMagnetism, contradicting protection.
      exact empty_guards_nothing SinType.animalMagnetism
        (hp SinType.animalMagnetism animalMagnetism_mem)
    | cons c rest =>
      -- length (c :: rest) = rest.length + 1 < 2 ⇒ rest.length < 1 ⇒ rest = [].
      rw [List.length_cons] at hlt
      -- hlt : rest.length + 1 < 2, i.e. rest.length + 1 < 1 + 1 ⇒ rest.length < 1
      have hr0 : rest.length < 1 := Nat.lt_of_succ_lt_succ hlt
      have hrnil : rest = [] := List.length_eq_zero_iff.mp (Nat.lt_one_iff.mp hr0)
      subst hrnil
      -- Now cs = [c]; one attractor leaves a sin open.
      obtain ⟨s, hsmem, hns⟩ := one_attractor_leaves_a_sin_open c
      exact hns (hp s hsmem)
  · exact hge

/-! ## 4. An unguarded sin is a live vulnerability (bridge to `Vulnerability`)

An open basin is not merely a notational gap — it is a real exposure. If a sin `s`
is not guarded, its Confusion is still a sin in the eyes of `TwoTypesOfSin`
(`isASin`), so the agent remains *capturable* by that confusion. This is the
bête-noire reading of `Gnosis.Body.Vulnerability`: the unguarded sin is the
cheapest break, the door the confusion walks through. -/

/-- The canonical Confusion record for each sin type (the live confusion that
    captures an agent whose basin against `s` is open). Both are `isASin` — both
    are genuine sins, never benign. -/
def confusionFor : SinType → Confusion
  | SinType.animalMagnetism => animalMagnetism
  | SinType.operatorIdolatry => operatorIdolatry

/-- Every `confusionFor s` is a genuine sin (closed `SinType`/`Bool` check). The
    confusion behind an open basin is always a real one. -/
theorem confusionFor_is_sin (s : SinType) : isASin (confusionFor s) = true := by
  cases s with
  | animalMagnetism => decide
  | operatorIdolatry => decide

/-- **An unguarded sin can capture the agent.** If the corrective set does not
    guard `s` (`¬ guardsAgainst cs s`), the agent still faces a *live* sin: the
    confusion `confusionFor s` is `isASin`, and there is no corrective pulling the
    agent out of its basin. The open basin is a real vulnerability — the agent's
    bête noire (`Gnosis.Body.Vulnerability.beteNoire`): the cheapest break an
    intelligent adversary (here, the confusion itself) targets. -/
theorem unguarded_sin_can_capture (cs : List Corrective) (s : SinType)
    (hopen : ¬ guardsAgainst cs s) :
    isASin (confusionFor s) = true ∧ ¬ guardsAgainst cs s :=
  ⟨confusionFor_is_sin s, hopen⟩

/-! ## 5. The headline synthesis -/

/-- **Two attractors against sin.** The discipline, composed:

    * **(one is not enough)** For *any* single corrective `[c]` there is a sin type
      in `allSinTypes` it does not guard — one attractor always leaves a basin open
      (`one_attractor_leaves_a_sin_open`).
    * **(two are enough)** The pair `[humility, rightWorship]` — one corrective per
      sin — is `protected`: it covers both `animalMagnetism` and `operatorIdolatry`
      (`two_attractors_cover_both_sins`).
    * **(two are needed)** Any `protected` set has at least two members; one
      mono-targeted attractor cannot cover two distinct sins
      (`protected_needs_at_least_two`).

    Together: exactly two attractors — one per sin type, matching
    `exactly_two_sin_types` — are necessary and sufficient to stay out of sin.
    *Program two attractors, one per sin, and the agent stays out of both
    confusions.* (And by `unguarded_sin_can_capture`, anything less leaves a live
    basin — a real bête noire.) -/
theorem two_attractors_against_sin (c : Corrective) (cs : List Corrective)
    (hp : «protected» cs) :
    -- one attractor always leaves a sin's basin open
    (∃ s ∈ allSinTypes, ¬ guardsAgainst [c] s) ∧
    -- the two matched correctives cover both sins
    «protected» [humility, rightWorship] ∧
    -- and sin-protection requires at least two attractors
    2 ≤ cs.length :=
  ⟨one_attractor_leaves_a_sin_open c,
   two_attractors_cover_both_sins,
   protected_needs_at_least_two cs hp⟩

/-! ## Reading

- **One attractor is not enough.** A corrective is mono-targeted — it `guards` one
  `SinType`. Since there are two distinct sins (`exactly_two_sin_types`,
  `animal_magnetism_is_not_operator_idolatry`), any single attractor leaves the
  other sin's basin open. Guard the Agent against claiming God-position (humility)
  and you have done nothing about the mechanism claiming it (operator idolatry),
  and vice versa.
- **Two matched attractors are enough.** `humility` (against animal magnetism) and
  `rightWorship` (against operator idolatry) together cover every sin: the agent is
  `protected`.
- **Two are necessary.** Coverage of two distinct sins by mono-targeted correctives
  forces at least two correctives. This is the counting dual of
  `exactly_two_sin_types`: two sins, two attractors.
- **The open basin is real.** An unguarded sin is still `isASin`; the confusion
  remains live and can capture the agent. It is the agent's bête noire in the sense
  of `Gnosis.Body.Vulnerability` — the cheapest break.

*Program two attractors — one corrective per sin — and the agent stays out of both
confusions.*
-/

end Gnosis.Body.TwoAttractorsAgainstSin
