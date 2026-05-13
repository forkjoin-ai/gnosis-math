import Init
import Gnosis.AeonCycleTwelveShadow
import Gnosis.TwelveSlotSixtySixPairsCarrier

namespace Gnosis
namespace FoilForrestWalk

/-!
# Foil **Forrest** walk (**combinatorial index scaffold only**)

**Spelling:** **Forrest** — named after a friend (**not** English “forest”).

## Relation to **Skyrms walk** (runtime anchor)

In **`open-source/gnosis`**, **`src/forest/skyrms-walk.ts`** implements the **Skyrms walk**: Forest races compile
per-node timing certificates into **void-boundary** rejection counts; **`skyrmsWalk`** iterates **complement distributions**
(temperature **`η`**) until assignments stabilize toward a **Nash-style** equilibrium report (**soft** probabilities plus **hard**
argmax per node). **`skyrmsWalkFromForest`** wires that walk to **`GenerationState[]`** from the Forest convergence loop.

That runtime walk lives in **ℝⁿ distributions**, convergence thresholds, and compiler/node identifiers --- none of which belong in Init-only Lean.

## How this module **evolves** the same idea (combinatorially)

**Forrest walk** keeps only the **shape**: a **finite ordered trace** (“walk”) whose steps are **discrete gates** drawn from a fixed
carrier. Here steps are **strict ascending pairs** on **`Fin twelve`**, i.e. rows of **`pairsIJ`** (**66** chords ---
**`TwelveSlotSixtySixPairsCarrier`**). So:

* **Skyrms walk (TS):** iterate **probability vectors** over competing languages per node until equilibrium witnesses stabilize.
* **Forrest walk (Lean):** certify **which unordered pair-slots** appear, in order, in a trace --- suitable as an index spine for
  **Foil** / **distributed-inference** ensembles that reuse the **twelve-slot / sixty-six-pair** geometry (cf. **`NikMapTwelveCarrier`**)
  without importing probabilities or Nash predicates into the proof kernel.

This is **not** a formalization of Skyrms's dynamics; it is a **parallel discrete scaffold** for naming and typing traces alongside that lineage.

## Runtime **extension** (combine Skyrms + Forrest)

**`open-source/gnosis/src/forest/forrest-skyrms-bridge.ts`** closes the loop:

1. Pin **twelve** Forest node ids in a fixed slot order `nodesAtSlots[0..11]`.
2. From each Skyrms **`hardAssignment`** (map node → winning compiler), emit **`encodeHardAssignmentAsForrestWalk`**:
   for each `lo < hi`, if winners differ, append step `{ lo, hi }` (lex order in `lo`, then `hi`).
   These steps are exactly the **strict ascending pairs** this module types as **`ForrestWalkStep`** / **`pairsIJ`** chords.
3. **`bundleSkyrmsWithForrestWalk`** attaches that list to the final **`SkyrmsResult`**. Optional **`SkyrmsWalkHooks.onPostIteration`**
   in **`skyrms-walk.ts`** feeds **`forrestWalkFromSkyrmsIterationSnapshots`** so the **iterated** soft walk yields a **concatenated**
   discrete certificate (Skyrms time × pair geometry).

So **Skyrms** supplies *who wins where* over void-boundary mass; **Forrest** supplies *which twelve-slot gates record disagreement*
among pinned nodes. Probabilities and Nash checks stay in TypeScript; Lean keeps **shape-only** typing of the emitted chords.

**Informal runtime siblings:** ensemble routing in **`open-source/gnosis`** (Forest / Skyrms stack above), plus **Foil** surfaces under
**distributed-inference**.

This module pins **kernel-level indices only**: each step is an ascending **`pairsIJ`** chord on **`Fin twelve`**.

**No** randomness axioms, **no** impurity / Gini semantics, **no** void-boundary or **`η`** parameters --- those remain in TypeScript.

Lean records **which discrete gates** a trace may mention.

Cross-links: **`Gnosis.TwelveSlotSixtySixPairsCarrier`**, **`Gnosis.NikMapTwelveCarrier`**, **`Gnosis.EscherichiaColiOrthologTwelveCarrier`**,
**`Gnosis.SixtySixPairsAtlasWitness`**.
-/

open Gnosis.AeonCycleTwelveShadow
open Gnosis.TwelveSlotSixtySixPairsCarrier

/-- Vertex label for an abstract **twelve-slot** sketch (**not** a healpix index). -/
abbrev WalkVertex := TwelveSlot

/-- One **walk step**: traverse a strict unordered pair of distinct twelve-slots (**split / gate metaphor**). -/
abbrev ForrestWalkStep := StrictAscendingPair

/-- Chord coordinates for this step (**lies in **`pairsIJ`**). -/
def ForrestWalkStep.toChord (s : ForrestWalkStep) : Nat × Nat :=
  StrictAscendingPair.toNatChord s

theorem ForrestWalkStep.mem_pairsIJ (s : ForrestWalkStep) : s.toChord ∈ pairsIJ :=
  StrictAscendingPair.mem_pairsIJ s

/-- A **Forrest walk**: finite trace of **`pairsIJ`** gates (**order matters** at the list layer). -/
abbrev ForrestWalk :=
  List ForrestWalkStep

/-- Every listed step's chord belongs to **`pairsIJ`** (**immediate from step typing**). -/
theorem ForrestWalk.forall_mem_chord_mem_pairsIJ (w : ForrestWalk) :
    ∀ s ∈ w, s.toChord ∈ pairsIJ := by
  intro s _
  exact ForrestWalkStep.mem_pairsIJ s

/-- **`[]`** satisfies the chord-membership predicate vacuously. -/
theorem ForrestWalk.forall_mem_chord_mem_pairsIJ_nil :
    (∀ s ∈ ([] : ForrestWalk), s.toChord ∈ pairsIJ) :=
  fun _ h => nomatch h

/-- Inductive **`cons`** wrapper (**proof-layer bookkeeping for traces**). -/
theorem ForrestWalk.forall_mem_chord_mem_pairsIJ_cons (step : ForrestWalkStep) (w : ForrestWalk)
    (hw : ∀ t ∈ w, t.toChord ∈ pairsIJ) :
    ∀ u ∈ (step :: w), u.toChord ∈ pairsIJ := by
  intro u hu
  rcases List.mem_cons.mp hu with heq | hm
  · simpa [← heq] using ForrestWalkStep.mem_pairsIJ step
  · exact hw u hm

/-- Step touches an endpoint vertex (**incidence predicate on twelve slots**). -/
def ForrestWalkStep.touches (s : ForrestWalkStep) (v : WalkVertex) : Prop :=
  v = s.lo ∨ v = s.hi

theorem ForrestWalkStep.touches_lo (s : ForrestWalkStep) : s.touches s.lo :=
  Or.inl rfl

theorem ForrestWalkStep.touches_hi (s : ForrestWalkStep) : s.touches s.hi :=
  Or.inr rfl

end FoilForrestWalk
end Gnosis
