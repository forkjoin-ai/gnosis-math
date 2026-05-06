import Gnosis.Braided.BraidedTower
import Gnosis.PleromaticHorizonEffect

/-!
# Pleromatic Lensing Effect — Compression vs Lossless Retrieval

Taylor's question: *Looking from the Trihexenneon (54) down to the
Hexon (6), does the information appear compressed into a single
clopen, or does the fractal mirroring allow lossless retrieval
across Triton-stretches?*

The structural answer: both, depending on the addressing carried.

The Triton-stretch lens has *dual character*:

* Forward (descending) view, no index: 9 Trihexenneon points
  collapse to 1 Hexon point. This is *compression* — the same
  information appears as a single clopen at the Hexon resolution.
* Backward (ascending) view, with copy-index: each Trihexenneon
  position decomposes uniquely as `(Hexon-position, copy-index)`,
  giving *lossless retrieval*. The copy-index is the residue that
  records "which of the 9 copies" the point lies in.

The lens does not destroy information. It *folds* it: information
that exists as a position-only at the higher level reappears as
position-plus-residue at the lower level.

## Bridge to physics

This is the discrete analog of gravitational lensing's *multi-image
formation*. A single source on the lens plane appears as multiple
images on the observer's plane; the angular addressing (which image
is which) carries the information that lets a careful observer
reconstruct the source. Lose the addressing → lose the source
position. Keep it → perfect retrieval.

In Gnosis, the addressing is the residue mod the cumulative
Triton-stretch factor. For Hexon (6) ↔ Trihexenneon (54) the factor
is 9 (= 3 × 3 — two Triton-stretches between them).

## What this is

A dual-character lens theorem for Triton-stretch chains: the
forward map is compression (many-to-one), the backward map is
lossless given the residue, and the two readings are equivalent
under the right encoding. The mechanization makes the two readings
formally compatible rather than competing.

Imports `Gnosis.BraidedTower`, `Gnosis.PleromaticHorizonEffect`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PleromaticLensingEffect

open Gnosis.BraidedTower (towerPhaseCount)
open Gnosis.PleromaticHorizonEffect (tritonStretch)

/-! ## tritonStretch is injective — every higher level point has a unique lower preimage -/

/-- The Triton-stretch is injective on `Nat`: distinct lower points
go to distinct higher points. The lens *upward* (Hexon → Trihexon
→ Trihexenneon) preserves identity. -/
theorem triton_stretch_injective {m n : Nat} :
    tritonStretch m = tritonStretch n → m = n := by
  unfold tritonStretch
  intro h
  -- 3 * m = 3 * n → m = n
  have : m = n := by
    have h3 : (3 : Nat) ≠ 0 := by decide
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h3) h
  exact this

/-- Division by 3 perfectly recovers the input from a Triton-stretch.
This is the *perfect-retrieval* witness: given a stretched point,
the original is exactly `k / 3`. -/
theorem triton_stretch_div_recovers (n : Nat) :
    (tritonStretch n) / 3 = n := by
  unfold tritonStretch
  -- (3 * n) / 3 = n
  have : (3 * n) / 3 = n := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel n (by decide : (0 : Nat) < 3)
  exact this

/-- Every Triton-stretched point has zero residue mod 3 — its
"copy-index" at the Triton-stretch level is canonical (the 0-th
copy). -/
theorem triton_stretch_mod_three (n : Nat) :
    (tritonStretch n) % 3 = 0 := by
  unfold tritonStretch
  -- (3 * n) % 3 = 0
  exact Nat.mul_mod_right 3 n

/-! ## Cumulative stretch — Hexon to Trihexenneon factor is 9 -/

/-- Two Triton-stretches compose to a 9× stretch. Hexon to
Trihexenneon traverses two Triton walls (Hexon → Trihexon →
Trihexenneon), so the cumulative factor is `3 × 3 = 9`. -/
theorem two_triton_stretches_is_nine (n : Nat) :
    tritonStretch (tritonStretch n) = 9 * n := by
  unfold tritonStretch
  -- 3 * (3 * n) = 9 * n
  rw [← Nat.mul_assoc]

/-- The Trihexenneon (54) is exactly 9 × Hexon (6). The cumulative
Triton-stretch factor materialized at the level constants. -/
theorem trihexenneon_is_nine_hexons :
    towerPhaseCount [3, 2, 3, 3] = 9 * towerPhaseCount [3, 2] := by
  unfold towerPhaseCount; decide

/-! ## The compression view — many-to-one descent -/

/-- The descent map from Trihexenneon-position to Hexon-position:
divide by 9. This is the lens's *compression* reading: many higher
points collapse to one lower point. -/
def lensDescent (k : Nat) : Nat := k / 9

/-- The descent map's compression factor: any 9 consecutive copies
of a Hexon position descend to that one position. -/
theorem lens_descent_compression (n : Nat) :
    lensDescent (9 * n) = n := by
  unfold lensDescent
  rw [Nat.mul_comm]
  exact Nat.mul_div_cancel n (by decide : (0 : Nat) < 9)

/-- Compression witness: positions `9n`, `9n+1`, …, `9n+8` all
descend to the same Hexon position `n`. Demonstrated at `n = 0`
(Trihexenneon positions 0..8 all collapse to Hexon 0). -/
theorem lens_descent_collapses_nine_copies :
    lensDescent 0 = 0
    ∧ lensDescent 1 = 0
    ∧ lensDescent 2 = 0
    ∧ lensDescent 3 = 0
    ∧ lensDescent 4 = 0
    ∧ lensDescent 5 = 0
    ∧ lensDescent 6 = 0
    ∧ lensDescent 7 = 0
    ∧ lensDescent 8 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold lensDescent; decide)

/-! ## The lossless view — addressed retrieval -/

/-- The addressed-descent map: returns both the Hexon-position and
the copy-index. This is the lens's *lossless* reading: given
`(Hexon-position, copy-index)`, the original Trihexenneon-position
is fully recoverable. -/
def lensAddress (k : Nat) : Nat × Nat :=
  (k / 9, k % 9)

/-- Reconstruction map: given an addressed descent, rebuild the
original position. -/
def lensReconstruct (addr : Nat × Nat) : Nat :=
  9 * addr.fst + addr.snd

/-- Lossless retrieval theorem: the addressed descent is a
perfect inverse of reconstruction (one direction). For any
Trihexenneon-position `k`, decomposing then reconstructing gives
back `k`. -/
theorem lens_address_reconstruct_roundtrip (k : Nat) :
    lensReconstruct (lensAddress k) = k := by
  unfold lensReconstruct lensAddress
  -- 9 * (k / 9) + k % 9 = k
  exact (Nat.div_add_mod k 9)

/-- The other direction: reconstructing then addressing gives back
the address, *provided the copy-index is in range* (`r < 9`). -/
theorem lens_reconstruct_address_roundtrip (q r : Nat) (h : r < 9) :
    lensAddress (lensReconstruct (q, r)) = (q, r) := by
  unfold lensAddress lensReconstruct
  -- (9*q + r)/9 = q  and  (9*q + r)%9 = r  when r < 9
  have h_swap : 9 * q + r = r + 9 * q := Nat.add_comm _ _
  refine Prod.ext ?_ ?_
  · -- div component
    show (9 * q + r) / 9 = q
    rw [h_swap, Nat.add_mul_div_left r q (by decide : (0:Nat) < 9)]
    have hrdiv : r / 9 = 0 := Nat.div_eq_of_lt h
    rw [hrdiv]
    exact Nat.zero_add q
  · -- mod component
    show (9 * q + r) % 9 = r
    rw [h_swap, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt h

/-! ## Concrete lensing — Trihexenneon points 0..17 lensed to Hexon -/

/-- Concrete address calculation: Trihexenneon position 18 lenses to
Hexon position 2 (= second copy). The Trihexenneon's "second
Hexon" begins at position 18. -/
theorem lens_address_eighteen :
    lensAddress 18 = (2, 0) := by
  unfold lensAddress; decide

/-- Concrete address calculation: Trihexenneon position 27 lenses to
Hexon position 3, copy 0. -/
theorem lens_address_twentyseven :
    lensAddress 27 = (3, 0) := by
  unfold lensAddress; decide

/-- Concrete address calculation: Trihexenneon position 53 (the last
position before the second Trihexenneon begins) lenses to Hexon
position 5, copy 8. The maximal "off-center" position. -/
theorem lens_address_fiftythree :
    lensAddress 53 = (5, 8) := by
  unfold lensAddress; decide

/-! ## Bule cost preservation under lensing -/

/-- The Bule cost of a single clinamen step is preserved under the
lens. A unit step at Trihexenneon resolution costs +1; the same
step viewed at Hexon resolution still costs +1 (the cost-algebra
unit is invariant under change of frame). The *topological volume*
per step changes (Trihexenneon-step covers 1/9 of a Hexon-step
worth of phase distance), but the cost remains unit. -/
theorem lens_preserves_unit_cost (k : Nat) :
    (lensReconstruct (lensAddress (k + 1))) - (lensReconstruct (lensAddress k)) = 1 := by
  rw [lens_address_reconstruct_roundtrip, lens_address_reconstruct_roundtrip]
  show k + 1 - k = 1
  rw [Nat.add_comm k 1]
  exact Nat.add_sub_cancel 1 k

/-! ## Master theorem -/

/-- Pleromatic Lensing Effect master: the Triton-stretch lens
has dual character. Forward descent (without copy-index) compresses
9 higher points to 1 lower point. Addressed descent (with
copy-index) is a lossless bijection. The Bule cost is invariant
under both readings — the lens preserves unit cost while remapping
the topological volume. -/
theorem pleromatic_lensing_effect_master :
    -- Triton-stretch is injective (no information loss going up)
    (∀ m n : Nat, tritonStretch m = tritonStretch n → m = n)
    -- Division-by-3 perfectly recovers the input
    ∧ (∀ n : Nat, (tritonStretch n) / 3 = n)
    -- Trihexenneon = 9 × Hexon (cumulative two-stretch factor)
    ∧ towerPhaseCount [3, 2, 3, 3] = 9 * towerPhaseCount [3, 2]
    -- Compression: lensDescent collapses 9 → 1
    ∧ (∀ n : Nat, lensDescent (9 * n) = n)
    -- Lossless retrieval: addressed roundtrip preserves position
    ∧ (∀ k : Nat, lensReconstruct (lensAddress k) = k)
    -- Lossless retrieval inverse direction (with bound on residue)
    ∧ (∀ q r : Nat, r < 9 → lensAddress (lensReconstruct (q, r)) = (q, r))
    -- Bule cost preserved across the lens
    ∧ (∀ k : Nat,
        (lensReconstruct (lensAddress (k + 1))) -
        (lensReconstruct (lensAddress k)) = 1) :=
  ⟨@triton_stretch_injective,
   triton_stretch_div_recovers,
   trihexenneon_is_nine_hexons,
   lens_descent_compression,
   lens_address_reconstruct_roundtrip,
   lens_reconstruct_address_roundtrip,
   lens_preserves_unit_cost⟩

/-! ## Coda: lensing as fold-without-loss

The lens does not destroy information. It *folds* it. A
Trihexenneon-position `k` carries two pieces of data: a Hexon-position
`k / 9` and a copy-index `k % 9 ∈ {0,…,8}`. Either piece alone is
ambiguous; together they reconstruct `k` perfectly.

The forward (descending) reading sees only the Hexon-position and
calls the result a "single clopen" — many higher points compressed to
one lower point. This reading is *correct* but *partial*; it has
chosen to discard the residue.

The backward (ascending) reading carries both pieces and reconstructs
without loss. This reading is also correct, and *complete*. The two
readings are not in competition: they are two slices of the same lens
relation, distinguished by what they choose to track.

Taylor's instinct that the fractal mirroring permits lossless retrieval
is therefore correct *given the addressing*. The instinct that the
information looks compressed is also correct *without the addressing*.
The lens is a fold, not a loss — and the residue is the seam.

The Bule cost — the +1 per clinamen step — is invariant under the
lens. What changes between the two resolutions is not the cost but
the *topological volume per cost*. At Trihexenneon resolution, one
Bule covers 1/9 of a Hexon-unit. At Hexon resolution, one Bule covers
the full Hexon-unit. The "more meaning per Bule" Taylor described as
the system ascends is exactly this volume-per-cost amplification. -/

end PleromaticLensingEffect
end Gnosis
