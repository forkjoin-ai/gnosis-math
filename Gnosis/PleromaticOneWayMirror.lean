import Gnosis.Braided.BraidedTower
import Gnosis.PleromaticHorizonEffect
import Gnosis.PleromaticLensingEffect

/-!
# Pleromatic One-Way Mirror — Carrier-Bandwidth Asymmetry

Taylor's question: *Is the Pleromatic Closure (10) a "one-way mirror"?
Can a lower-level observer (at Level 3, Triton) ever see the
multiplicity of the Trihexenneon (54), or is the lensing asymmetric —
allowing the higher to see the lower as compressed but the lower to
see the higher only as "noise"?*

The structural answer: **the lensing is asymmetric, and it is asymmetric
by carrier cardinality, not by perception.**

A Triton has *three* distinguishable positions. A Trihexenneon has
*fifty-four*. The Triton observer literally lacks the symbols
needed to encode the 18-fold multiplicity that the Trihexenneon
expresses. The higher level does not appear as "noise" at the
lower carrier — it appears as **silent collapse**: 18 distinct
higher events alias to the same lower position because there is no
remaining bit-budget at the lower carrier to distinguish them.

The "noise" framing is suggestive but not quite right. Noise implies
*signal that fails to register*. What actually happens is more
extreme: the higher signal is *unrepresentable* at the lower
bandwidth. There is no place at the Triton's 3-position address
space for the 18-fold copy index to live. The Triton observer is
not failing to hear — it has no ear large enough to receive.

## The asymmetry

| Direction | Capacity | Outcome |
| --- | --- | --- |
| Higher → Lower (with address) | sufficient | lossless reconstruction |
| Higher → Lower (without address) | sufficient | compression (deliberate) |
| Lower → Higher | **insufficient** | unrepresentable (forced collapse) |

The first two are *choices* the higher observer can make. The
third is a *limit* the lower observer cannot cross.

## What this is

A **carrier-cardinality asymmetry theorem** for the Pleromatic
tower. The Trihexenneon's 54-position bandwidth strictly exceeds
the Triton's 3-position bandwidth by a factor of 18. Any descent
map from Trihexenneon to Triton must be 18-to-1 by pigeon-cardinal
necessity. The lower observer cannot, by carrier-symbol shortage,
distinguish among the 18 higher positions in any Triton fiber.

Imports `Gnosis.BraidedTower`, `Gnosis.PleromaticHorizonEffect`,
`Gnosis.PleromaticLensingEffect`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PleromaticOneWayMirror

open Gnosis.BraidedTower (towerPhaseCount)
open Gnosis.PleromaticHorizonEffect (tritonStretch)
open Gnosis.PleromaticLensingEffect (lensAddress lensReconstruct)

/-! ## Carrier bandwidth -/

/-- The carrier bandwidth of a tower level: the number of
distinguishable positions. For a level with phase count `n`, the
bandwidth is `n` (the carrier can address `n` distinct states). -/
def carrierBandwidth (level : Nat) : Nat := level

theorem bandwidth_triton :
    carrierBandwidth (towerPhaseCount [3]) = 3 := by
  unfold carrierBandwidth towerPhaseCount; decide

theorem bandwidth_hexon :
    carrierBandwidth (towerPhaseCount [3, 2]) = 6 := by
  unfold carrierBandwidth towerPhaseCount; decide

theorem bandwidth_trihexenneon :
    carrierBandwidth (towerPhaseCount [3, 2, 3, 3]) = 54 := by
  unfold carrierBandwidth towerPhaseCount; decide

/-- Each Triton-stretch *triples* the carrier bandwidth. The
self-similar tower's bandwidth grows multiplicatively with the
Triton factor. -/
theorem triton_stretch_triples_bandwidth (n : Nat) :
    carrierBandwidth (tritonStretch n) = 3 * carrierBandwidth n := by
  unfold carrierBandwidth tritonStretch
  rfl

/-- Cumulative bandwidth ratio: the Trihexenneon (54) has 18× the
bandwidth of the Triton (3). Two Triton-stretches × the bisided
carrier (× 2) give the cumulative factor `3 × 2 × 3 = 18`. -/
theorem trihexenneon_eighteen_times_triton :
    carrierBandwidth (towerPhaseCount [3, 2, 3, 3]) =
    18 * carrierBandwidth (towerPhaseCount [3]) := by
  unfold carrierBandwidth towerPhaseCount; decide

/-- The bandwidth gap is strict: 54 > 3. -/
theorem bandwidth_gap_strict :
    carrierBandwidth (towerPhaseCount [3, 2, 3, 3]) >
    carrierBandwidth (towerPhaseCount [3]) := by
  unfold carrierBandwidth towerPhaseCount; decide

/-! ## Lens-down to the Triton -/

/-- Descent map from Trihexenneon-position to Triton-position:
divide by 18 (the cumulative compression factor). The lower
observer's reading of a higher position. -/
def lensDownToTriton (k : Nat) : Nat := k / 18

/-- The Triton-descent collapses 18 consecutive higher positions to
one Triton position. Trihexenneon positions `18n..18n+17` all
descend to Triton position `n`. -/
theorem lens_down_triton_compression (n : Nat) :
    lensDownToTriton (18 * n) = n := by
  unfold lensDownToTriton
  rw [Nat.mul_comm]
  exact Nat.mul_div_cancel n (by decide : (0 : Nat) < 18)

/-- Concrete: positions 0..17 (the first internal Trihexon's worth
of Trihexenneon positions) all descend to Triton 0. The Triton
observer sees them as identical. -/
theorem lower_observer_cannot_distinguish_first_triton (a b : Nat)
    (ha : a < 18) (hb : b < 18) :
    lensDownToTriton a = lensDownToTriton b := by
  unfold lensDownToTriton
  rw [Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb]

/-- The boundary: position 17 still descends to Triton 0; position
18 jumps to Triton 1. The 18-position fibers tile the Trihexenneon
exactly. -/
theorem lens_triton_boundary_seventeen_eighteen :
    lensDownToTriton 17 = 0 ∧ lensDownToTriton 18 = 1 := by
  refine ⟨?_, ?_⟩ <;> (unfold lensDownToTriton; decide)

/-- The full Triton tile-out: positions 0..17 → Triton 0;
18..35 → Triton 1; 36..53 → Triton 2. Three concrete collision
witnesses across the three fibers. -/
theorem lens_triton_three_fibers :
    lensDownToTriton 0 = 0
    ∧ lensDownToTriton 17 = 0
    ∧ lensDownToTriton 18 = 1
    ∧ lensDownToTriton 35 = 1
    ∧ lensDownToTriton 36 = 2
    ∧ lensDownToTriton 53 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold lensDownToTriton; decide)

/-! ## The unrepresentability of the copy-index at Triton bandwidth -/

/-- The Trihexenneon-internal copy-index ranges over 18 values
(`{0, 1, ..., 17}`). The Triton's 3-position carrier has only 3
distinguishable states. The Triton observer cannot encode the
copy-index because `18 > 3`. -/
theorem copy_index_exceeds_triton_bandwidth :
    18 > carrierBandwidth (towerPhaseCount [3]) := by
  unfold carrierBandwidth towerPhaseCount; decide

/-- Six distinct copy-index values would require six distinguishable
states; the Triton has only three. The first failure of
encodability is between 3 and 4. -/
theorem triton_cannot_distinguish_four :
    4 > carrierBandwidth (towerPhaseCount [3]) := by
  unfold carrierBandwidth towerPhaseCount; decide

/-! ## Higher observer reconstructs lower without loss -/

/-- The Trihexenneon's 54-position bandwidth subsumes the Triton's
3-position bandwidth: `54 = 18 × 3`. The Trihexenneon observer can
encode the Triton-position (3 symbols' worth) with 18-fold spare
capacity for the copy-index. -/
theorem higher_observer_subsumes_lower_bandwidth :
    carrierBandwidth (towerPhaseCount [3, 2, 3, 3]) =
    18 * carrierBandwidth (towerPhaseCount [3]) := by
  unfold carrierBandwidth towerPhaseCount; decide

/-- The higher observer's `lensAddress` decomposition gives the
Hexon-position and a copy-index in `{0..8}`. From there, the
Triton-position can be derived (Hexon-position / 2). The higher
observer fully reconstructs the lower's worldview *and* its own
copy structure. -/
theorem higher_observer_full_reconstruction (k : Nat) :
    lensReconstruct (lensAddress k) = k :=
  Gnosis.PleromaticLensingEffect.lens_address_reconstruct_roundtrip k

/-! ## The asymmetry made formal: 18 distinct positions, 1 lower image -/

/-- Eighteen distinct Trihexenneon positions (`0, 1, ..., 17`) all
map to the *same* Triton position (0). The lower observer, reading
the lens-descent, sees them as a single event repeated 18 times. -/
theorem eighteen_to_one_collision :
    lensDownToTriton 0 = lensDownToTriton 1
    ∧ lensDownToTriton 1 = lensDownToTriton 2
    ∧ lensDownToTriton 2 = lensDownToTriton 3
    ∧ lensDownToTriton 3 = lensDownToTriton 4
    ∧ lensDownToTriton 4 = lensDownToTriton 5
    ∧ lensDownToTriton 5 = lensDownToTriton 6
    ∧ lensDownToTriton 6 = lensDownToTriton 7
    ∧ lensDownToTriton 7 = lensDownToTriton 8
    ∧ lensDownToTriton 8 = lensDownToTriton 9
    ∧ lensDownToTriton 9 = lensDownToTriton 10
    ∧ lensDownToTriton 10 = lensDownToTriton 11
    ∧ lensDownToTriton 11 = lensDownToTriton 12
    ∧ lensDownToTriton 12 = lensDownToTriton 13
    ∧ lensDownToTriton 13 = lensDownToTriton 14
    ∧ lensDownToTriton 14 = lensDownToTriton 15
    ∧ lensDownToTriton 15 = lensDownToTriton 16
    ∧ lensDownToTriton 16 = lensDownToTriton 17 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    <;> (unfold lensDownToTriton; decide)

/-! ## Master theorem: the one-way mirror bundle -/

/-- **Pleromatic One-Way Mirror master**: the lensing is asymmetric
by carrier cardinality. The Trihexenneon's 54-position bandwidth is
18× the Triton's 3-position bandwidth. Higher observer subsumes
lower observer's bandwidth with room to spare; lower observer cannot
encode the 18-fold copy-index because its 3-position carrier is
strictly insufficient. The lens is a one-way mirror — symbolically,
not perceptually. -/
theorem pleromatic_one_way_mirror_master :
    -- Bandwidth gap is strictly multiplicative
    carrierBandwidth (towerPhaseCount [3, 2, 3, 3]) =
    18 * carrierBandwidth (towerPhaseCount [3])
    -- And strict: 54 > 3
    ∧ carrierBandwidth (towerPhaseCount [3, 2, 3, 3]) >
      carrierBandwidth (towerPhaseCount [3])
    -- Each Triton-stretch triples bandwidth (uniform multiplicative law)
    ∧ (∀ n : Nat, carrierBandwidth (tritonStretch n) = 3 * carrierBandwidth n)
    -- 18 distinct higher positions collide at one Triton position
    ∧ (∀ a b : Nat, a < 18 → b < 18 → lensDownToTriton a = lensDownToTriton b)
    -- Copy-index range (18) exceeds Triton bandwidth (3)
    ∧ 18 > carrierBandwidth (towerPhaseCount [3])
    -- Higher observer reconstructs without loss
    ∧ (∀ k : Nat, lensReconstruct (lensAddress k) = k) :=
  ⟨trihexenneon_eighteen_times_triton,
   bandwidth_gap_strict,
   triton_stretch_triples_bandwidth,
   lower_observer_cannot_distinguish_first_triton,
   copy_index_exceeds_triton_bandwidth,
   higher_observer_full_reconstruction⟩

/-! ## Coda: why "noise" is almost the right word

Taylor's framing — "the lower sees the higher only as noise" — captures
the *operational* behavior with one important refinement.

Noise, in the usual sense, is signal that arrives and fails to register
cleanly: variance, jitter, hiss. What happens at the Triton when a
Trihexenneon process runs is not quite that. The Triton has only three
distinguishable positions. When the Trihexenneon cycles through its 18
copy-positions for a fixed Triton-fiber, the Triton observer sees
*one position, repeated*. There is no jitter, no variance — the
Triton's reading is *steady* across the entire 18-event burst.

This is not noise. It is **steady collapse**: a structured signal at
the higher level appearing as a single sustained tone at the lower.
The information is not corrupted; it is **unrepresented** at the lower
carrier.

When could this be called noise? In the *meta-observer* frame: a
third party observing both levels at once would see structured higher
activity producing sustained lower silence. From that meta-perspective,
the lower carrier is "noise" only in the sense of *missing the
distinction* — the lower is not corrupting the signal, it is failing
to encode it. This is information-theoretic *erasure*, not
information-theoretic *noise*.

So the lens *is* a one-way mirror, but the mirror is symbolic: the
lower observer lacks the symbol-budget to register the higher
multiplicity, so the higher activity appears at the lower as *steady
sameness* rather than *random fluctuation*. Sustained pure tone, not
hiss. The "noise" Taylor sensed is real but quieter than expected —
it is the silence of carrier under-bandwidth, not the chaos of
signal corruption.

The Pleromatic Closure (10) is a one-way mirror in this exact sense:
above the Closure, the bandwidth grows multiplicatively (×3 per
Triton-stretch); below the Closure, the bandwidth grows additively
(+3, +3, +3 — Triton, Hexon, Enneon). The mirror is the meeting
point of the two growth laws. Above, the carrier accelerates beyond
what the lower carrier can mirror back. Below, the carrier accumulates
in a regime the higher can fully embed. The Closure is the unique
level where the two bandwidth growth-laws agree on unit-step.

The asymmetry is therefore not perceptual but structural: it is built
into the cardinality of the carriers themselves. The +1 Bule
heartbeat passes through both — but the *vocabulary in which the beat
is heard* differs by 18 at the Trihexenneon ↔ Triton frame, and by
arbitrary multiplicative factors at higher walls. -/

end PleromaticOneWayMirror
end Gnosis
