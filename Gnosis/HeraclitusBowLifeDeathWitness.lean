/-
  HeraclitusBowLifeDeathWitness.lean
  ==================================

  Heraclitus (trad. DK **B48**), bow / life wordplay (one English gloss):

    “The name of the bow is life, / but its work is death.”

  Greek hears **βιός** (bow) and **βίος** (life) as the same surface string in the
  pun register; **work** names what the implement *does* — another register. The
  **shape** is a **linguistic Möbius strip** in the informal sense: one object is
  fixed by the **violent tension** between what it is *called* and what it *performs*.
  This file **does not** import number-theoretic Möbius inversion (`μ(n)` on `Nat`);
  that vocabulary lives in `Gnosis.EulerTotientMobiusInversion` and is unrelated.

  **Repo cousins:** `CummingsLeafFallsParenthesisWitness` (**two** **strings** **in** **one**
  **visual** **object** — **poetic** **layout**, **not** **βιός**/**βίος** **pun** **proved**
  **here**); `BowieChangesWitness` (**modern** **chorus** **flux** — **name**/**work**
  **family** **rhyme** **only**, **not** **B48** **lemma** **here**); `HeraclitusRiverTwiceWitness` (river / self flux — **static identity**
  negation at the **σ** of stepping twice);
  `ShipOfTheseusWitness` (**same σ-template**: Material/Form ↔
  Name/Work, with definitional relabel);
  `HeraclitusUpDownPathWitness` (B60 path invariant vs local up/down);
  `LaoziBowlVoidFunctionWitness` (Ch.11 void-as-use-site vs object-only stories);
  `ParmenidesOnNatureWitness` (Being non-empty / `Empty` uninhabited);
  `TruthOneManyNamesWitness` (one referent, many honest charts);
  `SimonidesSpartanEpitaphWitness` (inscription as relay-bearing edge);
  `LiBaiQuietNightThoughtWitness` (two metrics on one night);
  `HeartTongueTotalNegationWitness` (twin `¬` on interface-myths);
  `SemanticPolysemySieve` (polysemy as sieve pressure).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace HeraclitusBowLifeDeathWitness

/-- Nominal register: what the implement is *called* in the “life” line of the pun. -/
abbrev BowNameLife (lifeName : Prop) : Prop :=
  lifeName

/-- Ergative / functional register: what the implement *does* — “death” as work. -/
abbrev BowWorkDeath (deathWork : Prop) : Prop :=
  deathWork

/--
  Two **distinct** `Prop` layers on one poetic implement: name vs work.
  Conjunction is **not** a claim that `nameReg` and `workReg` are logically equivalent;
  it only packages co-assertion (the fragment’s tension).
-/
structure LinguisticMobiusStripWitness (nameReg workReg : Prop) where
  nameIsLife : BowNameLife nameReg
  workIsDeath : BowWorkDeath workReg

theorem both_registers_hold (A B : Prop) (w : LinguisticMobiusStripWitness A B) : A ∧ B :=
  And.intro w.nameIsLife w.workIsDeath

def buildWitness (A B : Prop) (hA : A) (hB : B) : LinguisticMobiusStripWitness A B :=
  ⟨hA, hB⟩

end HeraclitusBowLifeDeathWitness
