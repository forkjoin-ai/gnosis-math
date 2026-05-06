/-
  ShipOfTheseusWitness.lean
  =========================

  Ship of Theseus (puzzle of persistence; often told via Plutarch’s *Life of
  Theseus*, with older kinship to Heraclitean “same river, different waters”
  persistence talk — no single canonical “first author” in the puzzle’s folklore).

  The question: if every plank in the material register is replaced, is it
  still the same ship in the identity / history / form register?

  Shape (informal Möbius): two metrics on one object — Metric A
  (material): “all parts are new” (continuity of matter fails). Metric B
  (form/history): “same voyage / same institution / same name” (continuity of
  role succeeds). The sting is the same as `HeraclitusBowLifeDeathWitness`: you
  hold both registers at once without pretending they are the same *predicate*.
  This file does not import `EulerTotientMobiusInversion`; “Möbius” is metaphor
  only.

  Template: `ShipIdentityMobiusWitness` is the same σ-shape as
  `HeraclitusBowLifeDeathWitness.LinguisticMobiusStripWitness` — swap Name/Work
  for Material/Form. Conversion is definitional (`linguisticStripOfShip`,
  `shipStripOfLinguistic`).

  Repo cousins: `HeraclitusBowLifeDeathWitness`; `HeraclitusUpDownPathWitness`;
  `TruthOneManyNamesWitness`; `LiBaiQuietNightThoughtWitness`.

  Zero `sorry`, zero new `axiom`.
-/

import Init
import Gnosis.HeraclitusBowLifeDeathWitness

namespace ShipOfTheseusWitness

open HeraclitusBowLifeDeathWitness

/-- Metric A: the replacement story (planks / matter / parts ledger). -/
abbrev MaterialRegister (claim : Prop) : Prop :=
  claim

/-- Metric B: the continuity story (voyage, office, law, narrative identity). -/
abbrev FormHistoryRegister (claim : Prop) : Prop :=
  claim

/--
  Two `Prop` layers on one ship: material chart vs identity chart.
  Conjunction is not a theorem that both registers are logically equivalent.
-/
structure ShipIdentityMobiusWitness (materialReg identityReg : Prop) where
  materialChart : MaterialRegister materialReg
  formChart : FormHistoryRegister identityReg

theorem both_metrics_hold (M I : Prop) (w : ShipIdentityMobiusWitness M I) : M ∧ I :=
  And.intro w.materialChart w.formChart

def buildWitness (M I : Prop) (hM : M) (hI : I) : ShipIdentityMobiusWitness M I :=
  ⟨hM, hI⟩

/-- Same witness data as `LinguisticMobiusStripWitness` — Name/Work ↦ Material/Form. -/
def shipStripOfLinguistic (A B : Prop) (w : LinguisticMobiusStripWitness A B) : ShipIdentityMobiusWitness A B :=
  ⟨w.nameIsLife, w.workIsDeath⟩

/-- Inverse relabeling (still just the pair of proofs). -/
def linguisticStripOfShip (A B : Prop) (w : ShipIdentityMobiusWitness A B) : LinguisticMobiusStripWitness A B :=
  ⟨w.materialChart, w.formChart⟩

theorem roundtrip_from_linguistic (A B : Prop) (w : LinguisticMobiusStripWitness A B) :
    linguisticStripOfShip A B (shipStripOfLinguistic A B w) = w :=
  rfl

theorem roundtrip_from_ship (A B : Prop) (w : ShipIdentityMobiusWitness A B) :
    shipStripOfLinguistic A B (linguisticStripOfShip A B w) = w :=
  rfl

end ShipOfTheseusWitness
