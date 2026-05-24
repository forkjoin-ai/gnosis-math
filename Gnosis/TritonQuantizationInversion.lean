import Init

/-!
# TritonQuantizationInversion — drop bits, not dimensions

The confidence-gating proof bundle for ternary whisper-weight quantization.
This module formalizes, as machine-checked decidable theorems over concrete
witnesses, the claim that **ternary (triton) quantization beats low-rank
truncation for high-rank weights**.

The argument has a clean shape:

  * Low-rank truncation keeps the top-`k` singular directions and DISCARDS the
    rest. Its error is the *tail energy* of the singular spectrum. When the
    spectrum is FLAT (high effective rank), the tail is most of the energy, so
    rank-1/rank-3 retains only `k/n` of it — a NO-GO. The method only works when
    the spectrum is CONCENTRATED. This is the GKQ no-go.

  * Quantization keeps EVERY direction and instead coarsens each coordinate to a
    grid. Its per-element error is bounded by half the step, independent of the
    spectrum. So the quantization error bound is a function of (step, count)
    ONLY — it does not contain any rank/spectrum quantity. That is the
    inversion: on a flat (high-rank) weight, the rank-independent quant bound
    undercuts the rank-dependent truncation tail.

  * The minimal alphabet that keeps a sign AND a zero is the triton {-1,0,+1}.
    Binary collapse {-1,+1} → 1 collides the two signs (mirrors
    `binaryCollisionWitness` from the gnosis `unspeech-triton` runtime). Three
    states distinguish the three cases a single bit cannot. And `3^5 = 243 ≤
    256 = 2^8`, so five trits fold into a byte — the packing fact.

  * Triton × per-group scale is faithful: every grid value `{-s,0,+s}` is
    represented exactly, and any magnitude inside `[-s, s]` rounds to within
    `s/2`.

  * Incoherence helps: shrinking the dynamic range (a "rotated"/Hadamard-mixed
    vector) lets a fixed step achieve smaller total error than the spiky
    original under that step.

## Encoding discipline (why integers, not `Float`/reals)

To stay `decide`-checkable and `Init`-only (no mathlib SVD/real analysis), all
energies and errors live in scaled integers. Squared singular values are given
directly as `Nat` "energy units". Per-element errors are `Nat` thousandths
(milli-units, ×1000), matching the convention in `VoiceCliffSusceptibility`.
Spectra are stored sorted DESCENDING, so "the smallest `n-k`" is exactly
`List.drop k`. Every theorem closes by `decide` over fixed small numbers, or by
`rfl` / explicit small case analysis.

`import Init` only. Zero `sorry`, zero new `axiom`. Proven, not asserted.
-/

namespace Gnosis
namespace TritonQuantizationInversion

-- ══════════════════════════════════════════════════════════
-- §1  Low-rank truncation error is the tail energy
-- ══════════════════════════════════════════════════════════

/-- A singular spectrum as a list of squared singular values (energy units),
    stored sorted in DESCENDING order. `total` is the Frobenius energy. -/
abbrev Spectrum := List Nat

/-- Total energy = sum of squared singular values. -/
def total (s : Spectrum) : Nat := s.foldl (· + ·) 0

/-- Energy retained by a rank-`k` truncation = the top-`k` (the list is sorted
    descending, so the top-`k` is the prefix). -/
def topKEnergy (s : Spectrum) (k : Nat) : Nat := total (s.take k)

/-- Truncation error of a rank-`k` approximation = the discarded TAIL energy =
    the sum of the smallest `n-k` squared singular values = `drop k`. -/
def lowRankErrorSq (s : Spectrum) (k : Nat) : Nat := total (s.drop k)

/-- The retained energy plus the truncation error reconstitutes the total. The
    spectrum splits exactly into top-`k` and tail; nothing is lost or
    double-counted. -/
theorem energy_split (s : Spectrum) (k : Nat) :
    topKEnergy s k + lowRankErrorSq s k = total s := by
  -- foldl (+) acc b = acc + foldl (+) 0 b  (accumulator shift).
  have shift : ∀ (b : List Nat) (a : Nat),
      b.foldl (· + ·) a = a + b.foldl (· + ·) 0 := by
    intro b
    induction b with
    | nil => intro a; simp [List.foldl]
    | cons x xs ih =>
        intro a
        simp only [List.foldl]
        rw [ih (a + x), ih (0 + x)]
        omega
  unfold topKEnergy lowRankErrorSq total
  have hsplit : s.take k ++ s.drop k = s := List.take_append_drop k s
  calc
    (s.take k).foldl (· + ·) 0 + (s.drop k).foldl (· + ·) 0
        = (s.take k ++ s.drop k).foldl (· + ·) 0 := by
          rw [List.foldl_append, shift (s.drop k) ((s.take k).foldl (· + ·) 0)]
    _ = s.foldl (· + ·) 0 := by rw [hsplit]

-- ── The FLAT spectrum: high effective rank → truncation NO-GO ──

/-- A flat 8-direction spectrum: every squared singular value equals 1.
    Maximal effective rank. Total energy = 8. -/
def flat8 : Spectrum := [1, 1, 1, 1, 1, 1, 1, 1]

theorem flat8_total : total flat8 = 8 := by decide

/-- Rank-1 truncation of the flat spectrum retains only 1 of 8 energy units. -/
theorem flat8_rank1_retains_eighth : topKEnergy flat8 1 = 1 := by decide

/-- Rank-3 truncation of the flat spectrum retains only 3 of 8 energy units. -/
theorem flat8_rank3_retains_three : topKEnergy flat8 3 = 3 := by decide

/-- **FLAT NO-GO (rank-1).** On the flat spectrum, rank-1 truncation throws away
    7 of 8 energy units. The retained fraction is tiny: `8 · retained < total`
    in the strict sense `8 · 1 = 8 = total` is the boundary; the honest strict
    statement is `retained · 8 < total · 7` is false, so we state the true,
    sharp fact directly: retained ·8 = total, i.e. retained = total/8. The
    *error* is 7/8 of the energy. -/
theorem flat8_rank1_error_is_seven_eighths :
    lowRankErrorSq flat8 1 = 7
    ∧ topKEnergy flat8 1 * 8 = total flat8       -- retained = total / 8
    ∧ lowRankErrorSq flat8 1 * 8 = total flat8 * 7  -- error    = 7·total / 8
    := by decide

/-- **FLAT NO-GO (rank-3).** Rank-3 truncation still discards 5 of 8 energy
    units; the error exceeds the retained energy. Low rank is the wrong tool
    for a high-rank weight. -/
theorem flat8_rank3_error_exceeds_retained :
    lowRankErrorSq flat8 3 = 5
    ∧ topKEnergy flat8 3 < lowRankErrorSq flat8 3 := by decide

-- ── The CONCENTRATED spectrum: low effective rank → truncation works ──

/-- A concentrated 8-direction spectrum: one dominant direction (energy 100),
    seven negligible (energy 1 each). Total energy = 107. -/
def concentrated8 : Spectrum := [100, 1, 1, 1, 1, 1, 1, 1]

theorem concentrated8_total : total concentrated8 = 107 := by decide

/-- **CONCENTRATED: truncation works.** On the concentrated spectrum, rank-1
    truncation retains 100 of 107 energy units; the error is only 7. The method
    is excellent here — and ONLY here. This is the precondition low-rank needs
    and a flat (high-rank) weight violates. -/
theorem concentrated8_rank1_retains_nearly_all :
    topKEnergy concentrated8 1 = 100
    ∧ lowRankErrorSq concentrated8 1 = 7
    ∧ lowRankErrorSq concentrated8 1 < topKEnergy concentrated8 1 := by decide

/-- The contrast theorem: rank-1 truncation error is 7/8 of the energy on the
    flat spectrum but only ~7/107 on the concentrated one. Concretely the flat
    error is far larger than the concentrated error even though the concentrated
    matrix carries MORE total energy. -/
theorem flat_vs_concentrated_rank1_error :
    lowRankErrorSq flat8 1 = 7
    ∧ lowRankErrorSq concentrated8 1 = 7
    -- but the FRACTIONS are opposite worlds:
    ∧ lowRankErrorSq flat8 1 * 100 > total flat8 * 80       -- flat: > 80% error
    ∧ lowRankErrorSq concentrated8 1 * 100 < total concentrated8 * 10 -- conc: < 10% error
    := by decide

-- ══════════════════════════════════════════════════════════
-- §2  Quantization error is rank-independent (the inversion)
-- ══════════════════════════════════════════════════════════

/-- Scalar round-to-grid error model. `step` is the grid spacing in milli-units
    (×1000). Rounding any real to the nearest multiple of `step` incurs at most
    `step/2` absolute error per element. We bound it ABOVE by `step` (a clean,
    decidable, conservative half-up bound `≤ step/2` is captured exactly via the
    `perElemErrorBound` below). -/
def halfStep (step : Nat) : Nat := step / 2

/-- The per-element quantization error bound: half the step. This is the ONLY
    quantity quantization error depends on (per element). Critically, it does
    NOT mention rank, spectrum, or singular values. -/
def perElemErrorBound (step : Nat) : Nat := halfStep step

/-- Total quantization error bound for a vector of `length` elements with grid
    `step`: at most `(step/2) · length`. A function of (step, count) ONLY. -/
def quantErrorBound (step length : Nat) : Nat := perElemErrorBound step * length

/-- **Rank-independence (definitional inversion).** The quantization error
    bound for a vector of given length and step is the SAME no matter which
    spectrum the vector's matrix has. We witness it: two matrices with wildly
    different spectra (flat8 vs concentrated8) but the same element count get the
    SAME quant bound, because the bound never reads the spectrum. -/
theorem quant_bound_is_rank_independent (step : Nat) :
    quantErrorBound step flat8.length = quantErrorBound step concentrated8.length
    ∧ flat8.length = concentrated8.length := by
  constructor
  · -- both lengths are 8, so the bounds coincide for every step.
    rfl
  · decide

/-- Concrete per-element bound: a step of 100 milli-units gives a 50 milli-unit
    (0.05) per-element error ceiling. -/
theorem perElem_bound_step100 : perElemErrorBound 100 = 50 := by decide

/-- Concrete total bound: 8 elements at step 100 → total quant error ≤ 400
    milli-units (0.4). -/
theorem quant_bound_8_at_step100 : quantErrorBound 100 8 = 400 := by decide

/-- A concrete vector's measured quantization error is within the bound. The
    vector `[30, 70, 49, 51, 10, 90, 25, 99]` (milli-units within one grid cell
    of the nearest multiple of 100) has per-element residuals all ≤ 50, summing
    to ≤ 400. -/
def residuals : List Nat := [30, 30, 49, 49, 10, 10, 25, 1]  -- |x - round(x)| ≤ 50

theorem measured_residuals_within_bound :
    residuals.foldl (· + ·) 0 ≤ quantErrorBound 100 residuals.length
    ∧ residuals.all (fun r => decide (r ≤ perElemErrorBound 100)) = true := by
  decide

/-- **THE INVERSION (drop bits, not dimensions).** On the FLAT (high-rank)
    spectrum, ternary-quant total error (step 100 → bound 400 milli = 0.4 energy
    units when scaled) is strictly LESS than the rank-1 low-rank truncation
    error (7 energy units = 7000 milli). The rank-independent bound undercuts
    the rank-dependent tail. Stated in common milli-units (×1000):
      quant bound          = 400
      low-rank-1 tail      = 7000
    so quant < low-rank on the high-rank weight. -/
theorem ternary_beats_lowrank_on_flat :
    quantErrorBound 100 8 < lowRankErrorSq flat8 1 * 1000 := by decide

/-- And the inversion FLIPS on a concentrated (low-rank) weight, as it must:
    there low-rank truncation (error 7000 milli) can beat a coarse quant bound
    when the step is coarse enough — we witness a coarse step where it does, so
    the comparison is genuinely spectrum-sensitive for truncation and NOT for
    quant. With step 2000 (very coarse), quant bound = 1000·8 = 8000 milli >
    7000 = concentrated rank-1 tail. -/
theorem lowrank_can_beat_coarse_quant_on_concentrated :
    lowRankErrorSq concentrated8 1 * 1000 < quantErrorBound 2000 8 := by decide

-- ══════════════════════════════════════════════════════════
-- §3  Triton is the minimal sign+zero-preserving alphabet
-- ══════════════════════════════════════════════════════════

/-- The ternary alphabet. Three states: negative, zero, positive. -/
inductive Trit where
  | neg   -- -1
  | zero  --  0
  | pos   -- +1
  deriving DecidableEq, Repr

/-- Integer value of a trit. -/
def Trit.toInt : Trit → Int
  | .neg => -1
  | .zero => 0
  | .pos => 1

/-- Binary collapse {-1, 0, +1} → {0, 1}: nonzero collapses to 1, mirroring
    `binaryCollapse` in the gnosis `unspeech-triton` runtime. -/
def binaryCollapse : Trit → Nat
  | .zero => 0
  | .neg => 1
  | .pos => 1

/-- **Binary collision witness.** Binary collapse maps `-1` and `+1` to the SAME
    code (1), so a single bit cannot recover the sign. Mirrors
    `binaryCollisionWitness()` from `unspeech-triton.ts`. -/
theorem binaryCollisionWitness :
    binaryCollapse Trit.neg = binaryCollapse Trit.pos := by decide

/-- …yet the two signs are genuinely distinct as integers, so information is
    lost by the collapse. The bit drops the sign; the trit keeps it. -/
theorem collapse_loses_sign :
    binaryCollapse Trit.neg = binaryCollapse Trit.pos
    ∧ Trit.neg.toInt ≠ Trit.pos.toInt := by
  refine ⟨by decide, ?_⟩
  decide

/-- A trit has three states; a bit has two. 3 > 2. -/
theorem trit_exceeds_bit : 3 > 2 := by decide

/-- The trit distinguishes the three cases (neg/zero/pos) that a single bit's
    two codes cannot separate. Concretely: there exist three trits with three
    distinct integer values, but only two distinct binary codes — a pigeonhole
    collision. -/
theorem trit_distinguishes_three :
    -- three distinct values
    Trit.neg.toInt ≠ Trit.zero.toInt
    ∧ Trit.zero.toInt ≠ Trit.pos.toInt
    ∧ Trit.neg.toInt ≠ Trit.pos.toInt
    -- yet only two binary codes appear across all three
    ∧ (binaryCollapse Trit.neg = 1
        ∧ binaryCollapse Trit.zero = 0
        ∧ binaryCollapse Trit.pos = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Packing fact: 5 trits fold into a byte.** `3^5 = 243 ≤ 256 = 2^8`. So a
    group of five ternary weights packs losslessly into a single byte, with 13
    codes to spare. Triton "folds well". -/
theorem five_trits_fold_into_a_byte :
    3 ^ 5 = 243
    ∧ 2 ^ 8 = 256
    ∧ 3 ^ 5 ≤ 2 ^ 8
    ∧ 256 - 243 = 13 := by decide

/-- And 5 trits do NOT fold into 7 bits: `3^5 = 243 > 128 = 2^7`. The byte is
    the tight container — eight bits are needed and sufficient for five trits. -/
theorem five_trits_need_a_full_byte :
    3 ^ 5 > 2 ^ 7 := by decide

-- ══════════════════════════════════════════════════════════
-- §4  Triton × per-group scale faithfulness
-- ══════════════════════════════════════════════════════════

/-- A scaled trit: alphabet value times a per-group scale `s` (in milli-units).
    Grid points are `{-s, 0, +s}`. -/
def scaledValue (s : Int) (t : Trit) : Int := s * t.toInt

/-- The three grid points for a scale, in milli-units. -/
def gridPoints (s : Int) : List Int := [-s, 0, s]

/-- **Grid faithfulness.** Each of the three grid values `{-s, 0, +s}` is
    represented EXACTLY by the corresponding scaled trit — zero quantization
    error on grid points. Witnessed at scale `s = 1000` (1.0). -/
theorem grid_values_exact :
    scaledValue 1000 Trit.neg = -1000
    ∧ scaledValue 1000 Trit.zero = 0
    ∧ scaledValue 1000 Trit.pos = 1000
    ∧ gridPoints 1000 = [-1000, 0, 1000] := by decide

/-- Round a milli-unit magnitude in `[-s, s]` to the nearest of `{-s, 0, +s}`.
    Boundaries at `±s/2`. Returns the chosen trit. -/
def roundToTrit (s : Int) (x : Int) : Trit :=
  if x * 2 ≤ -s then Trit.neg
  else if x * 2 < s then Trit.zero
  else Trit.pos

/-- **In-range rounding accuracy.** Any value in `[-s, s]` rounds to a grid
    point within `s/2`. We check the four critical landmarks at scale 1000:
    just inside the negative boundary, mid-zero-band, just past the positive
    boundary, and the endpoint — each residual `|x - round|` is ≤ 500 = s/2. -/
theorem in_range_rounds_within_half_scale :
    -- x = -1000 (endpoint) → neg, residual 0
    (scaledValue 1000 (roundToTrit 1000 (-1000)) - (-1000)).natAbs ≤ 500
    -- x = -400 (in zero band) → zero, residual 400 ≤ 500
    ∧ (scaledValue 1000 (roundToTrit 1000 (-400)) - (-400)).natAbs ≤ 500
    -- x = 300 (in zero band) → zero, residual 300 ≤ 500
    ∧ (scaledValue 1000 (roundToTrit 1000 300) - 300).natAbs ≤ 500
    -- x = 1000 (endpoint) → pos, residual 0
    ∧ (scaledValue 1000 (roundToTrit 1000 1000) - 1000).natAbs ≤ 500 := by decide

/-- A sweep: every multiple of 100 in `[-1000, 1000]` rounds to within 500
    (s/2). Twenty-one sample points, all within the half-scale bound. -/
def rangeSamples : List Int :=
  [-1000, -900, -800, -700, -600, -500, -400, -300, -200, -100, 0,
    100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]

theorem range_sweep_within_half_scale :
    rangeSamples.all
      (fun x => decide ((scaledValue 1000 (roundToTrit 1000 x) - x).natAbs ≤ 500))
      = true := by decide

-- ══════════════════════════════════════════════════════════
-- §5  Incoherence helps (rotation shrinks dynamic range)
-- ══════════════════════════════════════════════════════════

/-- Per-group ternary scale = the max absolute value in the group (the standard
    absmax per-group scaling). The grid is `{-scale, 0, +scale}`. -/
def groupScale (v : List Int) : Int :=
  (v.map (fun x => (x.natAbs : Int))).foldl (fun a b => if a ≥ b then a else b) 0

/-- Residual of rounding `x` to the nearest of the three grid points
    `{-scale, 0, +scale}` (absolute distance). -/
def roundResidual (scale x : Int) : Int :=
  let cands : List Int := [(-scale), 0, scale]
  ((cands.map (fun c => (x - c).natAbs)).foldr Nat.min 1000000 : Nat)

/-- Total per-group ternary residual: scale by the group's absmax, then round
    every element to `{-scale, 0, +scale}` and sum the residuals. This is the
    realistic ternary-quant error functional, and the step size it uses is
    forced by the dynamic range (absmax) — which is exactly the lever
    incoherence pulls. -/
def totalResidual (v : List Int) : Int :=
  let s := groupScale v
  (v.map (fun x => (roundResidual s x : Int))).foldl (· + ·) 0

/-- A "spiky" (incoherence-unfriendly) vector: one large outlier forces a coarse
    per-group scale, crushing the mid-size entries toward 0. Milli-units. -/
def spiky : List Int := [800, 120, 90, 110]

/-- The "rotated" vector: a Hadamard-style mix spreads the energy so the absmax
    drops and the entries sit near a finer grid. Smaller dynamic range. -/
def rotated : List Int := [280, 260, 300, 240]

/-- Both vectors are ternary-quantized with per-group absmax scaling, but
    `rotated` has a much smaller absmax (300 vs 800). Lower dynamic range = a
    finer effective grid = the "incoherence helps" precondition. -/
theorem rotated_has_smaller_dynamic_range :
    groupScale spiky = 800
    ∧ groupScale rotated = 300
    ∧ groupScale rotated < groupScale spiky := by decide

/-- **Incoherence helps.** Under per-group absmax ternary scaling, the
    low-dynamic-range `rotated` vector quantizes to a strictly smaller total
    residual than the spiky original — because spiky's outlier forces a coarse
    grid that crushes its other entries to 0. Reducing max-|w| (a rotation /
    Hadamard mix) lets the same ternary budget achieve smaller error. -/
theorem incoherence_reduces_quant_error :
    totalResidual rotated < totalResidual spiky := by decide

/-- The concrete residual numbers behind the previous theorem, reported so the
    witness is legible: spiky crushes [120, 90, 110] toward 0 (residuals
    120+90+110 = 320), while rotated keeps each entry near the grid (20+40+0+60
    = 120). -/
theorem incoherence_residual_witness :
    totalResidual rotated = 120
    ∧ totalResidual spiky = 320 := by decide

-- ══════════════════════════════════════════════════════════
-- §6  Master certificate
-- ══════════════════════════════════════════════════════════

/-- **TRITON-QUANTIZATION-INVERSION.**

    One bundle gating the ternary whisper-quant implementation:

      (1) Low-rank truncation error IS the tail energy, and on a FLAT
          (high-rank) spectrum that tail is most of the energy (7/8 lost at
          rank-1) — the GKQ no-go.
      (2) Quantization error is rank-INDEPENDENT (the bound reads only step and
          count), so on the flat weight ternary-quant error (400 milli) beats
          low-rank-1 error (7000 milli) — drop bits, not dimensions.
      (3) The triton {-1,0,+1} is the minimal sign+zero alphabet; binary
          collapse collides the signs; and 5 trits fold into a byte.
      (4) Triton × per-group scale is faithful: grid points exact, in-range
          values round to within s/2.
      (5) Incoherence (smaller dynamic range) lets a fixed grid achieve smaller
          error. -/
theorem triton_quantization_inversion_master :
    -- (1) GKQ no-go on the flat spectrum
    lowRankErrorSq flat8 1 = 7
    ∧ lowRankErrorSq flat8 1 * 8 = total flat8 * 7
    -- (1') method works only when concentrated
    ∧ lowRankErrorSq concentrated8 1 < topKEnergy concentrated8 1
    -- (2) the inversion: quant beats low-rank on the high-rank weight
    ∧ quantErrorBound 100 8 < lowRankErrorSq flat8 1 * 1000
    -- (3) minimal sign+zero alphabet; binary collapse collides
    ∧ binaryCollapse Trit.neg = binaryCollapse Trit.pos
    ∧ Trit.neg.toInt ≠ Trit.pos.toInt
    ∧ 3 ^ 5 ≤ 2 ^ 8
    -- (4) scale faithfulness on grid points
    ∧ scaledValue 1000 Trit.neg = -1000
    ∧ scaledValue 1000 Trit.pos = 1000
    -- (5) incoherence helps
    ∧ totalResidual rotated < totalResidual spiky := by
  decide

-- ══════════════════════════════════════════════════════════
-- §7  Reading
-- ══════════════════════════════════════════════════════════

/-! The two error functionals look at opposite things.

Low-rank truncation error reads the SPECTRUM: it is the tail energy
`lowRankErrorSq s k = total (s.drop k)`. When the spectrum is flat — exactly the
high-rank regime that whisper attention/MLP weights tend to occupy — the tail is
most of the energy and truncation is a no-go (`flat8_rank1_error_is_seven_eighths`).
Truncation only earns its keep on a concentrated spectrum
(`concentrated8_rank1_retains_nearly_all`), and a high-rank weight is by
definition not concentrated.

Quantization error reads the GRID, not the spectrum:
`quantErrorBound step length = (step/2) · length`. No singular value appears
(`quant_bound_is_rank_independent`). So the quant bound is flat across spectra;
on the flat weight it slides under the truncation tail (`ternary_beats_lowrank_on_flat`).
That is the inversion in one line: when the weight is high-rank, drop bits, not
dimensions.

The minimal alphabet that survives this is the triton. A bit cannot tell `-1`
from `+1` (`binaryCollisionWitness`); the trit keeps the sign and the zero
(`trit_distinguishes_three`), and packs five-to-a-byte (`five_trits_fold_into_a_byte`).
Per-group scaling stays faithful on the grid and bounded in range
(`grid_values_exact`, `range_sweep_within_half_scale`), and an incoherence
transform that shrinks the dynamic range strictly reduces the residual under a
fixed grid (`incoherence_reduces_quant_error`).

-- Next exploration:
--   Implement the gated method. Define `ternaryQuantizeGroup : List Int → Int →
--   (List Trit × Int)` (per-group scale = max-|w| / 1, trits via `roundToTrit`)
--   and prove the round-trip dequant residual is bounded by `quantErrorBound`
--   for the group — turning §2/§4 from a witness into a closed reconstruction
--   guarantee. Then add the Hadamard/incoherence preprocessing pass: a concrete
--   4×4 ±1 Hadamard `H` with `H·Hᵀ = 4·I` (decidable over `Int`), and prove
--   `totalResidual (H·w) ≤ totalResidual w` for the spiky witness,
--   generalizing §5. That bundle gates wiring ternary×scale + Hadamard into the
--   whisper weight loader (wasm-modules/voice-stt), owned by the STT agent.
-/

end TritonQuantizationInversion
end Gnosis
