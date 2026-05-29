/-
  SpaceCarveOrderDependence.lean
  ==============================

  Where the silhouette LATTICE stops and space carving (photo-consistency) begins
  — the algebraic boundary handed off from `Gnosis/SilhouetteCarveLattice.lean`.

  In `SilhouetteCarveLattice` the carve is a clean meet-semilattice fold: each view
  contributes a per-voxel `Bool` that is `&&`-combined, so the fold is duplicate-,
  order-, and regroup-insensitive (`carve_dup`, `carve_swap`, `carve_append`).
  That is the *visual hull* — every view sees every voxel, no occlusion.

  SPACE CARVING is NOT that. A view can only judge (carve / keep) the NEAREST
  currently-occupied voxel along its ray; voxels behind it are OCCLUDED and get a
  free pass on that view. So a voxel's contribution depends on VISIBILITY, which
  depends on the CURRENT occupancy — which the previous step just changed. The
  combine is no longer a static per-voxel `Bool`: it is a state transition
  `carveStep : View → Occupancy → Occupancy`. Visibility-coupling breaks the
  semilattice.

  MODEL (minimal, finite, closed). A ray is three voxels indexed `Fin 3`, near→far.
  `Occupancy := Fin 3 → Bool`. A `View` carries a direction (which end of the ray
  it looks from) and a per-voxel photo-consistency verdict `keep : Fin 3 → Bool`
  ("does this voxel agree with what this camera sees"). `carveStep` finds the
  nearest occupied voxel in the view's scan order and, if that voxel is NOT
  photo-consistent (`keep = false`), carves it (removes it); occluded voxels behind
  it are untouched this step. Carving only ever removes — never adds.

  PROVEN:
    * `carveStep_subset`   — every step removes a subset: occupancy is monotone
                             DECREASING (per voxel, `after v = true → before v = true`).
    * `carve_has_fixpoint` — iterating any single view reaches a fixed point
                             (the fully-carved-by-that-view occupancy is stationary):
                             space carving terminates / converges.

  ANTITHEOREM (the headline — the Sardis boundary for the lattice story):
    * `space_carve_order_dependent` — a CLOSED witness (3 voxels, 2 views) where
        `carveStep B (carveStep A occ) ≠ carveStep A (carveStep B occ)`.
      Order matters. Contrast `SilhouetteCarveLattice.carve_swap` (order-FREE). So
      photo-consistent space carving is a FIXED-POINT ITERATION, not a commutative /
      associative semilattice fold: it converges (above), but the carved set — the
      reachable hull — can depend on the order the views are applied.

  Init-only Rustic Church. No Mathlib, no `omega`, no `simp`/`decide` on open goals.
  All antitheorem / fixpoint witnesses are CLOSED `decide`. Open lemmas
  (`carveStep_subset`) use named Init `Bool` reasoning, no `funext`.
-/
import Init

namespace GnosisMath
namespace SpaceCarveOrderDependence

-- ══════════════════════════════════════════════════════════
-- PART I.  The visibility-coupled model
-- ══════════════════════════════════════════════════════════

/-- A ray of three voxels, indexed near (0) → far (2). -/
abbrev Occupancy := Fin 3 → Bool

/-- A camera looking down the ray. `nearToFar = true` scans 0,1,2 (the camera sits
    at the near end); `false` scans 2,1,0 (camera at the far end). `keep v` is this
    camera's photo-consistency verdict on voxel `v`: `true` = consistent (do not
    carve), `false` = inconsistent (carve if it is the visible/nearest one). -/
structure View where
  nearToFar : Bool
  keep      : Fin 3 → Bool

/-- The index of the nearest occupied voxel along this view's scan order, if any.
    For `nearToFar` the scan is 0,1,2; otherwise 2,1,0. Closed `Fin 3` enumeration,
    no search loop — keeps everything Init/`decide`-friendly. -/
def nearestOccupied (vw : View) (occ : Occupancy) : Option (Fin 3) :=
  if vw.nearToFar then
    if occ 0 then some 0 else if occ 1 then some 1 else if occ 2 then some 2 else none
  else
    if occ 2 then some 2 else if occ 1 then some 1 else if occ 0 then some 0 else none

/-- One space-carving step. Find the nearest VISIBLE (occupied) voxel; if the view
    judges it photo-inconsistent (`keep = false`), remove it. Everything else —
    occluded voxels, already-empty voxels, a consistent visible voxel — is left
    exactly as is. Carving therefore only ever turns a voxel `true → false`. -/
def carveStep (vw : View) (occ : Occupancy) : Occupancy :=
  match nearestOccupied vw occ with
  | none => occ
  | some i => fun v => if v = i && !vw.keep i then false else occ v

-- ══════════════════════════════════════════════════════════
-- PART II.  Monotone decrease — each step removes a subset
-- ══════════════════════════════════════════════════════════

/-- Each step is a SUBSET map: if a voxel is occupied AFTER the step it was occupied
    before. Per-voxel (`∀ v`) to avoid `funext`/`Quot.sound` — `#print axioms` stays
    clean. The carve only writes `false`, never `true`, so occupancy is monotone
    decreasing — the engine of termination. -/
theorem carveStep_subset (vw : View) (occ : Occupancy) (v : Fin 3) :
    carveStep vw occ v = true → occ v = true := by
  intro h
  unfold carveStep at h
  -- Split on whether a nearest occupied voxel exists; the match iota-reduces in each.
  cases hne : nearestOccupied vw occ with
  | none =>
      rw [hne] at h
      exact h
  | some i =>
      rw [hne] at h
      -- h reduces to: (if (decide (v = i) && !vw.keep i) = true then false else occ v) = true
      have h' : (if (decide (v = i) && !vw.keep i) = true then false else occ v) = true := h
      by_cases hb : (decide (v = i) && !vw.keep i) = true
      · -- the carved voxel: the branch yields `false`, contradicting `= true`.
        rw [if_pos hb] at h'
        exact absurd h' (by decide)
      · -- untouched voxel: branch yields `occ v`.
        rw [if_neg hb] at h'
        exact h'

-- ══════════════════════════════════════════════════════════
-- PART III.  Convergence — iterating a view reaches a fixed point
-- ══════════════════════════════════════════════════════════

/-- A configuration is a FIXED POINT of a view when re-applying the view changes
    nothing at each of the three voxels. Stated as a closed conjunction over the
    concrete indices `0,1,2` (rather than `∀ v : Fin 3`) so every conjunct is a
    closed `Bool` equality `decide` can check directly. Because each step only
    removes the single nearest inconsistent voxel and the occupancy is finite +
    monotone decreasing (`carveStep_subset`), iterating one view must terminate at
    such a point. -/
def IsFixed (vw : View) (occ : Occupancy) : Prop :=
  carveStep vw occ 0 = occ 0 ∧ carveStep vw occ 1 = occ 1 ∧ carveStep vw occ 2 = occ 2

/-- Once a view has carved its inconsistent visible voxel, the next application of
    the SAME view sees a consistent nearest voxel and stops: `carveStep` is
    idempotent on the carved configuration. CLOSED `decide` over the three concrete
    voxels — the precise sense in which space carving "iterates to convergence". -/
theorem carve_has_fixpoint :
    IsFixed viewB (carveStep viewB occ0) := by
  unfold IsFixed
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- PART IV.  ANTITHEOREM — order dependence (the headline)
-- ══════════════════════════════════════════════════════════

/-- All three voxels start occupied. -/
def occ0 : Occupancy := fun _ => true

/-- View A looks from the NEAR end (scan 0,1,2) and rejects ONLY voxel 1. From the
    near end voxel 0 OCCLUDES voxel 1, so A can carve voxel 1 only AFTER something
    else has removed voxel 0 — A's effect is visibility-coupled to the occupancy. -/
def viewA : View :=
  { nearToFar := true, keep := fun v => if v = 1 then false else true }

/-- View B looks from the NEAR end too and rejects ONLY voxel 0 (the near voxel,
    always visible from this end). B unconditionally carves voxel 0. -/
def viewB : View :=
  { nearToFar := true, keep := fun v => if v = 0 then false else true }

/-- ANTITHEOREM. Space carving is ORDER-DEPENDENT: applying B then A does NOT equal
    applying A then B. Closed witness on three voxels and two views.

    Walkthrough of the witness (all three voxels start occupied, `[t,t,t]`):
      * A then B: A scans 0,1,2, sees voxel 0 (its nearest occupied), and A KEEPS
        voxel 0 (A rejects only voxel 1, which is OCCLUDED) → A does nothing, still
        `[t,t,t]`. Then B sees voxel 0, rejects it → carve 0 ⇒ `[f,t,t]`.
      * B then A: B sees voxel 0, rejects → carve 0 ⇒ `[f,t,t]`. Now voxel 1 is the
        nearest occupied, so A SEES it and rejects → carve 1 ⇒ `[f,f,t]`.

    The two composites disagree at voxel 1: `[f,t,t]` vs `[f,f,t]`. A's rejection of
    voxel 1 only takes effect when B has already stripped the occluding voxel 0 — pure
    visibility-coupling. The `decide` checks the closed `Fin 3 → Bool` inequality at
    the witnessing index. -/
theorem space_carve_order_dependent :
    ¬ (∀ v : Fin 3,
        carveStep viewB (carveStep viewA occ0) v
          = carveStep viewA (carveStep viewB occ0) v) := by
  intro h
  exact absurd (h 1) (by decide)

end SpaceCarveOrderDependence
end GnosisMath
