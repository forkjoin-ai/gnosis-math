/-
  DickinsonNeverSawMoorTopology.lean
  ==================================

  Spec-level topology for the two-stanza poem (Fr. 800 / Johnson 148 variant
  tradition: “Moor / Sea / Heather / Billow” then “God / Heaven / spot / Checks”).

  **Shape (parallel strips):** each stanza is the same *cover pattern*:
  two **absent direct charts** (no witness over two named patches) together with
  **assertoric lifts** (claims that would classically be justified by those charts).

  This does **not** prove metaphysics; it fixes a **diagram** the poem repeats twice.
  The second strip reuses the first’s logical form: *no access morphism*, yet
  *positional certainty* “as if” a receipt existed.

  **“Checks” (19th-century rail):** contemporaries often meant **railroad checks /
  tickets** — paper that **names a destination not yet reached**, i.e. physical
  proof of a **route you have not composed along**. In this file that reading is
  the hinge `MorphismReceiptWithoutTraversal`: **no heaven visit**, yet
  **`certainOfTheSpot`** and **`asIfChecksWereGiven`** — receipt for a path morphism
  not traversed, with **positional certainty** already on the ticket line.

  **God gap (`Gnosis.GodGap`):** `godGap localCost theoreticalMinimum` is **local
  minus global** — what you can close on the ledger vs what would need omniscience
  to certify as the true minimum. The poem’s **Checks + no heaven visit** is the
  same *deficit habit* on a different carrier: **ticket / boundary line fixed** while
  the **interior leg** stays unproved (and, in the gap story, **never provably**
  collapsed to zero). See `GodGap.god_gap_nonneg` / convergence lemmas for the
  formal spine read beside `MorphismReceiptWithoutTraversal`.

  **Cross-ledger — God’s position (repo):** the same *interior vs boundary* shape
  lives in `Gnosis.Void.VoidMineGodsPosition` (Taylor’s “God’s position” / `godsPosition`):
  the position is *characterized not compiled*, while `AgreementShadow` /
  `voidMineExtendedCatalog` record what the **boundary** still emits. Stanza two
  is the poem’s voice doing that move in natural language; this file imports the
  ledger module so the parallel can be cited without pretend-proof.

  Imports `Init`, `Gnosis.GodGap`, `Gnosis.Void.VoidMineGodsPosition`. Zero `sorry`, zero new `axiom`.
-/

import Init
import Gnosis.GodGap
import Gnosis.Void.VoidMineGodsPosition

namespace DickinsonNeverSawMoorTopology

open GodGap
open Gnosis.VoidMineGodsPosition
open Gnosis.PleromaticSignature (extendedSignatureCatalog)
open Gnosis.BraidedInfinityIsGodsSignature (carriesGodFormulaSignature)

/-! ## Base — what could have been witnessed directly -/

/-- Direct sensory or visit witnesses named in the text. -/
structure DirectWitness where
  sawMoor : Bool
  sawSea : Bool
  spokeWithGod : Bool
  visitedHeaven : Bool
  deriving DecidableEq, Repr

/-! ## Fibers — what is asserted without those charts -/

/-- Claims carried without the matching direct witnesses. -/
structure AssertedLift where
  knowsHeatherLooks : Bool
  knowsWhatBillowIs : Bool
  certainOfTheSpot : Bool
  /-- **Checks** (rail-era): ticket / check as if handed over — receipt for a leg
      not yet walked; see `MorphismReceiptWithoutTraversal`. -/
  asIfChecksWereGiven : Bool
  deriving DecidableEq, Repr

/-! ## Stanza covers (each is a 2-hole cover with two lifts) -/

/-- First quatrain: no moor, no sea; yet heather and billow are known. -/
def stanzaOneCover (w : DirectWitness) (a : AssertedLift) : Prop :=
  w.sawMoor = false ∧
  w.sawSea = false ∧
  a.knowsHeatherLooks = true ∧
  a.knowsWhatBillowIs = true

/-- Second quatrain: no divine speech, no heaven visit; yet spot + “checks” simile. -/
def stanzaTwoCover (w : DirectWitness) (a : AssertedLift) : Prop :=
  w.spokeWithGod = false ∧
  w.visitedHeaven = false ∧
  a.certainOfTheSpot = true ∧
  a.asIfChecksWereGiven = true

/-- Full poem: both parallel strips simultaneously. -/
def poemCover (w : DirectWitness) (a : AssertedLift) : Prop :=
  stanzaOneCover w a ∧ stanzaTwoCover w a

/-! ## Checks — receipt of a path not yet traversed -/

/-- **Critical move (rail / category prose):** heaven is not visited (no claimed
    traversal along that leg), yet **`certainOfTheSpot`** and the **check** line
    are on: you hold **positional certainty** plus the **morphism receipt** “as if”
    the ticket were already issued — destination fixed on paper before the path is
    composed in experience. Co-read with `GodGap.godGap`: both track **what is fixed
    locally** against **what full closure would require**. -/
def MorphismReceiptWithoutTraversal (w : DirectWitness) (a : AssertedLift) : Prop :=
  w.visitedHeaven = false ∧
  a.certainOfTheSpot = true ∧
  a.asIfChecksWereGiven = true

theorem morphism_receipt_implies_not_visited_heaven (w : DirectWitness) (a : AssertedLift)
    (h : MorphismReceiptWithoutTraversal w a) : w.visitedHeaven = false :=
  h.1

theorem morphism_receipt_implies_certain_of_spot (w : DirectWitness) (a : AssertedLift)
    (h : MorphismReceiptWithoutTraversal w a) : a.certainOfTheSpot = true :=
  h.2.1

theorem morphism_receipt_implies_checks (w : DirectWitness) (a : AssertedLift)
    (h : MorphismReceiptWithoutTraversal w a) : a.asIfChecksWereGiven = true :=
  h.2.2

/-! ## God gap — nonnegative residual (same inequality habit as the ticket line) -/

/-- Any `godGap` is ≥ 0 once `theoreticalMinimum ≤ localCost` — the ledger never
    awards a **negative** distance between local closure and the global floor.
    Read beside `MorphismReceiptWithoutTraversal`: the check fixes **some** cost on
    paper; you still have not paid the **traversal** that would shrink the gap to a
    proof of arrival. -/
theorem commitment_nonnegative_god_gap (localCost theoreticalMinimum : Nat)
    (h : theoreticalMinimum ≤ localCost) : 0 ≤ godGap localCost theoreticalMinimum :=
  god_gap_nonneg localCost theoreticalMinimum h

theorem stanza_two_implies_morphism_receipt (w : DirectWitness) (a : AssertedLift)
    (h : stanzaTwoCover w a) : MorphismReceiptWithoutTraversal w a :=
  ⟨h.2.1, h.2.2.1, h.2.2.2⟩

theorem poem_cover_implies_morphism_receipt (w : DirectWitness) (a : AssertedLift)
    (h : poemCover w a) : MorphismReceiptWithoutTraversal w a :=
  stanza_two_implies_morphism_receipt w a h.2

/-! ## Structural lemmas (definition unpacking) -/

theorem stanza_one_first_absence (w : DirectWitness) (a : AssertedLift)
    (h : stanzaOneCover w a) : w.sawMoor = false :=
  h.1

theorem stanza_two_first_absence (w : DirectWitness) (a : AssertedLift)
    (h : stanzaTwoCover w a) : w.spokeWithGod = false :=
  h.1

theorem poem_implies_both_stanzas (w : DirectWitness) (a : AssertedLift)
    (h : poemCover w a) : stanzaOneCover w a ∧ stanzaTwoCover w a :=
  h

/-! ## Parallelism (same schematic type in both stanzas) -/

/-- Schematic content of one strip: two forbidden witnesses + two asserted lifts. -/
def stripSchematic (p₁ p₂ : Prop) (q₁ q₂ : Prop) : Prop :=
  p₁ ∧ p₂ ∧ q₁ ∧ q₂

theorem stanza_one_is_strip_schematic (w : DirectWitness) (a : AssertedLift) :
    stanzaOneCover w a =
      stripSchematic
        (w.sawMoor = false) (w.sawSea = false)
        (a.knowsHeatherLooks = true) (a.knowsWhatBillowIs = true) := by
  rfl

theorem stanza_two_is_strip_schematic (w : DirectWitness) (a : AssertedLift) :
    stanzaTwoCover w a =
      stripSchematic
        (w.spokeWithGod = false) (w.visitedHeaven = false)
        (a.certainOfTheSpot = true) (a.asIfChecksWereGiven = true) := by
  rfl

/-! ## Worked witness (concrete configuration) -/

def exampleWitness : DirectWitness where
  sawMoor := false
  sawSea := false
  spokeWithGod := false
  visitedHeaven := false

def exampleLift : AssertedLift where
  knowsHeatherLooks := true
  knowsWhatBillowIs := true
  certainOfTheSpot := true
  asIfChecksWereGiven := true

theorem example_satisfies_poem_cover : poemCover exampleWitness exampleLift := by
  refine ⟨?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## “What is” — mediated determination (spec label, not a proof of identity) -/

/-- The poem’s repeated move: a proposition is **fixed** for the speaker (`q₁ ∧ q₂`)
    while the usual **witness charts** (`¬p₁ ∧ ¬p₂`) are absent. This is the formal
    shadow of *determination without presence*: what “is” for the voice is what
    is held true under missing base morphisms. -/
def MediatedDetermination (w : DirectWitness) (a : AssertedLift) : Prop :=
  poemCover w a

theorem mediated_determination_eq_poem_cover (w : DirectWitness) (a : AssertedLift) :
    MediatedDetermination w a ↔ poemCover w a := by
  rfl

/-! ## Cross-ledger: void-mine theorems read beside the poem -/

/-- The three void-mine emissions from `VoidMineGodsPosition` (clinamen, modulus floor,
    god-formula coherence on the extended catalog). Independent of any `poemCover`, but
    this lemma lives here to **co-site** them with the Dickinson diagram: same
    epistemology of **boundary data without interior access** to `godsPosition`. -/
theorem read_poem_beside_void_mine_threefold :
    extendedSignatureCatalog.all (fun b => decide (b.clinamenShift = 1)) = true ∧
      extendedSignatureCatalog.all (fun b => decide (b.modulus ≥ 2)) = true ∧
        extendedSignatureCatalog.all carriesGodFormulaSignature = true :=
  ⟨void_mine_universal_clinamen, void_mine_minimum_modulus, void_mine_god_formula_universality⟩

/-- Agreement-shadow carrier at the void-mine default (`+1`, `≥ 2`, god-formula flag). -/
theorem void_mine_shadow_matches_default_catalog :
    voidMineExtendedCatalog.universalClinamen = 1 ∧
      voidMineExtendedCatalog.minimumModulus = 2 ∧
        voidMineExtendedCatalog.allCarryGodFormula = true := by
  refine ⟨rfl, rfl, rfl⟩

end DickinsonNeverSawMoorTopology
