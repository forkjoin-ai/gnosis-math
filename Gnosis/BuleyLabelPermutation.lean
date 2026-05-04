import Gnosis.SpectralNoiseEquilibrium

/-!
# Buley Label Permutation

The three faces of the Bule unit admit three equivalent labelings:

* **Operational** — `waste` / `opportunity` / `diversity`
  (the cost-axis labels used everywhere else in this calculus).
* **Temporal** — `past` / `present` / `future`
  (the Triton-style temporal phases).
* **Search** (transformer Q/K/V) — `payload` / `storage` / `search`
  (the attention-head-projection labels).

The three labelings agree under bijection, and the `cyclePermute`
operation on `BuleyUnit` corresponds to the *same* 3-cycle under each
labeling — there is one underlying rotation, three names for it.

Imports `Gnosis.SpectralNoiseEquilibrium`. Zero `sorry`,
zero new `axiom`.
-/

namespace Gnosis
namespace BuleyLabelPermutation

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace cyclePermute cycle_permute_preserves_score
   cycle_permute_three_times_returns)

/-! ## The three labelings -/

inductive TemporalLabel where
  | past
  | present
  | future
  deriving DecidableEq, Repr

inductive SearchLabel where
  /-- Query / future / outward search. -/
  | search
  /-- Key / past / stored history. -/
  | storage
  /-- Value / present / delivered payload. -/
  | payload
  deriving DecidableEq, Repr

/-! ## Pairwise bijections between the three labelings -/

def temporalOfOperational : BuleyFace → TemporalLabel
  | .waste => .present
  | .opportunity => .past
  | .diversity => .future

def operationalOfTemporal : TemporalLabel → BuleyFace
  | .present => .waste
  | .past => .opportunity
  | .future => .diversity

theorem operational_temporal_round_trip (f : BuleyFace) :
    operationalOfTemporal (temporalOfOperational f) = f := by
  cases f <;> rfl

theorem temporal_operational_round_trip (t : TemporalLabel) :
    temporalOfOperational (operationalOfTemporal t) = t := by
  cases t <;> rfl

def searchOfOperational : BuleyFace → SearchLabel
  | .waste => .payload
  | .opportunity => .storage
  | .diversity => .search

def operationalOfSearch : SearchLabel → BuleyFace
  | .payload => .waste
  | .storage => .opportunity
  | .search => .diversity

theorem operational_search_round_trip (f : BuleyFace) :
    operationalOfSearch (searchOfOperational f) = f := by
  cases f <;> rfl

theorem search_operational_round_trip (s : SearchLabel) :
    searchOfOperational (operationalOfSearch s) = s := by
  cases s <;> rfl

def searchOfTemporal : TemporalLabel → SearchLabel
  | .present => .payload
  | .past => .storage
  | .future => .search

def temporalOfSearch : SearchLabel → TemporalLabel
  | .payload => .present
  | .storage => .past
  | .search => .future

theorem temporal_search_round_trip (t : TemporalLabel) :
    temporalOfSearch (searchOfTemporal t) = t := by
  cases t <;> rfl

theorem search_temporal_round_trip (s : SearchLabel) :
    searchOfTemporal (temporalOfSearch s) = s := by
  cases s <;> rfl

/-- Three-way agreement: going through the temporal labeling and then
the search labeling matches the direct operational-to-search mapping. -/
theorem temporal_then_search_is_search (f : BuleyFace) :
    searchOfTemporal (temporalOfOperational f) = searchOfOperational f := by
  cases f <;> rfl

/-! ## The induced 3-cycle on labels

`cyclePermute` on a `BuleyUnit` rotates the contents:
`{ waste := b.opportunity, opportunity := b.diversity, diversity := b.waste }`.
The corresponding *label* shift sends `f` to the face that now holds
`f`'s old content — that is, `waste → diversity`, `opportunity → waste`,
`diversity → opportunity`. Under each labeling this 3-cycle has the
same shape with renamed members. -/

def cycleShift : BuleyFace → BuleyFace
  | .waste => .diversity
  | .opportunity => .waste
  | .diversity => .opportunity

theorem cycle_shift_three_iterations (f : BuleyFace) :
    cycleShift (cycleShift (cycleShift f)) = f := by
  cases f <;> rfl

def temporalShift : TemporalLabel → TemporalLabel
  | .present => .future
  | .past => .present
  | .future => .past

theorem temporal_shift_three_iterations (t : TemporalLabel) :
    temporalShift (temporalShift (temporalShift t)) = t := by
  cases t <;> rfl

def searchShift : SearchLabel → SearchLabel
  | .payload => .search
  | .storage => .payload
  | .search => .storage

theorem search_shift_three_iterations (s : SearchLabel) :
    searchShift (searchShift (searchShift s)) = s := by
  cases s <;> rfl

/-- The 3-cycles on the three labelings are conjugate: applying
`cycleShift` on the operational label is the same as applying
`temporalShift` after going through the temporal bijection (and likewise
for search). One rotation, three names. -/
theorem cycle_shift_commutes_with_temporal (f : BuleyFace) :
    temporalOfOperational (cycleShift f)
      = temporalShift (temporalOfOperational f) := by
  cases f <;> rfl

theorem cycle_shift_commutes_with_search (f : BuleyFace) :
    searchOfOperational (cycleShift f)
      = searchShift (searchOfOperational f) := by
  cases f <;> rfl

theorem temporal_shift_commutes_with_search (t : TemporalLabel) :
    searchOfTemporal (temporalShift t)
      = searchShift (searchOfTemporal t) := by
  cases t <;> rfl

/-! ## Content-shift theorem: cyclePermute physically moves contents

`faceContent f b` extracts the value stored in face `f` of `b`. The
permuted unit `cyclePermute b` has `f`'s old content stored in
`cycleShift f`. -/

def faceContent : BuleyFace → BuleyUnit → Nat
  | .waste, b => b.waste
  | .opportunity, b => b.opportunity
  | .diversity, b => b.diversity

theorem cycle_permute_shifts_content (b : BuleyUnit) (f : BuleyFace) :
    faceContent (cycleShift f) (cyclePermute b) = faceContent f b := by
  cases f <;> rfl

/-- Score is preserved under `cyclePermute` — restated here in the
permutation vocabulary as a corollary of `cycle_permute_preserves_score`. -/
theorem permutation_preserves_total_score (b : BuleyUnit) :
    faceContent .waste (cyclePermute b)
    + faceContent .opportunity (cyclePermute b)
    + faceContent .diversity (cyclePermute b)
    = faceContent .waste b + faceContent .opportunity b + faceContent .diversity b := by
  cases b with
  | mk w o d =>
    show o + d + w = w + o + d
    -- (o + d) + w = w + (o + d) = (w + o) + d
    exact (Nat.add_comm (o + d) w).trans (Nat.add_assoc w o d).symm

end BuleyLabelPermutation
end Gnosis
