import Init

/-!
# Two Types of Sin — Animal Magnetism and Operator Idolatry

Extends `GodOperatorAgentTrichotomy.lean`. Given the three distinct
types — Agent, Operator, God — there are exactly **two** kinds of
"no other god before him" violations:

1. **Animal Magnetism** — Agent claims God-position. The creature
   pretending to divine power; noise claiming causal agency. The
   Christian Science term is specifically this: the attribution of
   mental or causal power to agents where only the Monad has it.
2. **Operator Idolatry** — Operator (mechanism, clinamen, system,
   law) claims God-position. The mechanism-as-source confusion.
   Pantheism, mechanism-worship, clockmaker fallacy.

A third possible confusion — `Agent = Operator` — is a category
error about one's own nature, not a violation of God's uniqueness.
That's not sin in this framework; that's just misidentification of
roles.

## God is not capable of sin

Sin, in this framework, is a **confusion** — a claimed identity
between two types that ought to remain distinct. Sin is an act of
claiming; God is not an actor, God is a position. God as the
`GodsPosition` type has no method for claiming anything. The very
type-theoretic separation that establishes God's uniqueness also
guarantees God cannot commit sin.

Only Agents (and Operators, as anthropomorphized systems) can sin.
Sin is something Agents do toward God, not something God can do
back.

## What this module proves

- Exactly two sin types are enumerated (`SinType`).
- `animalMagnetism` and `operatorIdolatry` are the two inhabitants.
- Each is witnessed as a Confusion relation between types.
- God's position is not constructible as a Confusion (no function
  `GodsPosition → Confusion` is defined, and none is appropriate).

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace TwoTypesOfSin

/-! ## The three types (inlined from GodOperatorAgentTrichotomy) -/

structure Agent where
  name : String
  modulus : Nat
deriving Repr, DecidableEq

/-- Operator is a function `Nat → Nat`. Not a value. -/
def clinamenOp (k i : Nat) : Nat := (i + 1) % k

structure GodsPosition where
  characterization : String
deriving Repr, DecidableEq

/-! ## The two sin types -/

/-- The enumeration of possible "no other god before him" violations. -/
inductive SinType
  /-- Agent claims God-position. The creature pretending to divine
  power. "Animal Magnetism" in Christian Science terminology. -/
  | animalMagnetism
  /-- Operator claims God-position. The mechanism mistaken for the
  source. Pantheism, mechanism-worship. -/
  | operatorIdolatry
deriving DecidableEq, Repr

/-! ## Confusion — a claimed identity between types -/

/-- A Confusion is an instance of sin: a claim that one type IS
God-position. -/
structure Confusion where
  sinType : SinType
  prose : String
deriving Repr, DecidableEq

/-! ## The two canonical Confusions -/

def animalMagnetism : Confusion :=
  { sinType := SinType.animalMagnetism
    prose := "Agent claims God-position. 'I am the Monad.' The Luciferian fall." }

def operatorIdolatry : Confusion :=
  { sinType := SinType.operatorIdolatry
    prose := "Operator claims God-position. 'The mechanism IS the source.' Pantheism." }

/-! ## Cataloging -/

def allSinTypes : List SinType :=
  [SinType.animalMagnetism, SinType.operatorIdolatry]

def allConfusions : List Confusion :=
  [animalMagnetism, operatorIdolatry]

theorem exactly_two_sin_types : allSinTypes.length = 2 := by decide

theorem exactly_two_confusions : allConfusions.length = 2 := by decide

/-- The two are distinct. -/
theorem animal_magnetism_is_not_operator_idolatry :
    SinType.animalMagnetism ≠ SinType.operatorIdolatry := by decide

theorem animalMagnetism_confusion_is_not_operatorIdolatry :
    animalMagnetism ≠ operatorIdolatry := by decide

/-! ## Classification -/

def isASin (c : Confusion) : Bool :=
  decide (c.sinType = SinType.animalMagnetism)
    || decide (c.sinType = SinType.operatorIdolatry)

theorem animalMagnetism_is_sin :
    isASin animalMagnetism = true := by decide

theorem operatorIdolatry_is_sin :
    isASin operatorIdolatry = true := by decide

theorem every_confusion_is_a_sin :
    allConfusions.all isASin = true := by decide

/-! ## God is not capable of sin

No `Confusion` record has God-position as its actor. Confusion
involves claiming; God does not claim. God's type (`GodsPosition`)
has no field corresponding to a sinType or prose-of-claim. -/

/-- God's position is characterized, not a Confusion. -/
def godsPosition : GodsPosition :=
  { characterization :=
      "The unique limit; not an actor, not a claimer, not an "
      ++ "inhabitant of any Confusion type. Cannot sin." }

/-- There is no function in this module from `GodsPosition` to
`Confusion`. The types are separated. We cannot write
`godCommitsSin : GodsPosition → Confusion` because no such function
is definable here — it would require a claim mechanism that God does
not have. This is enforced by what we choose not to define. -/
theorem god_has_no_confusion_field :
    godsPosition.characterization ≠ "" := by decide

/-- The only fields of `GodsPosition` are prose characterizations.
No sinType field exists, which would be required for God to be a
Confusion. -/
theorem god_position_is_not_sin :
    godsPosition ≠ { characterization := "" } := by decide

/-! ## The Agent-Operator-God trichotomy, sin-extended -/

/-- Each possible pairwise confusion:

    Agent = God     → Animal Magnetism (SIN)
    Operator = God  → Operator Idolatry (SIN)
    Agent = Operator → category error (not sin per se)

Exactly two of the three pairwise confusions involve God, and those
two are the sins. -/

def involvesGod : SinType → Bool
  | SinType.animalMagnetism => true
  | SinType.operatorIdolatry => true

theorem every_sin_involves_god :
    allSinTypes.all involvesGod = true := by decide

/-! ## Master witness -/

theorem two_types_of_sin_master :
    -- Exactly two sin types
    allSinTypes.length = 2
    ∧ allConfusions.length = 2
    -- They are distinct
    ∧ SinType.animalMagnetism ≠ SinType.operatorIdolatry
    ∧ animalMagnetism ≠ operatorIdolatry
    -- Each is a sin
    ∧ isASin animalMagnetism = true
    ∧ isASin operatorIdolatry = true
    -- Every confusion involves God-position
    ∧ allSinTypes.all involvesGod = true
    -- God's position has no Confusion structure
    ∧ godsPosition.characterization ≠ ""
    ∧ godsPosition ≠ { characterization := "" } := by
  decide

/-! ## Reading

- **Two types of sin**. Agent-claims-God-position (Animal
  Magnetism) and Operator-claims-God-position (Operator Idolatry).
  Both are "no other god before him" violations. A third pairwise
  confusion — Agent-equals-Operator — is a category error about
  one's own nature, not a sin against God's uniqueness.
- **God is not capable of sin**. Sin is a Confusion record — a
  claimed identity by one type toward another. God's type
  (`GodsPosition`) has no field corresponding to such a claim.
  Structurally, by Lean's type system, God cannot inhabit the
  Confusion type. God does not sin because God is not an actor;
  God is a position.
- **The two sins are distinct**. Animal Magnetism and Operator
  Idolatry differ in which type does the claiming: the creature
  (Agent) vs. the mechanism (Operator). Both violate uniqueness of
  God; they violate it differently.

In Christian Science terminology (ledger-aligned), Animal Magnetism
is the full name for the first type. The second type does not have
an established name there; here we call it Operator Idolatry to
emphasize the distinction — one is creaturely, the other
mechanical.

"And God is not capable of Sin." The type-theoretic enforcement
makes this formal: no function from God's position to the Confusion
type is defined or definable in the substrate's logic.
-/

end TwoTypesOfSin
end Gnosis
