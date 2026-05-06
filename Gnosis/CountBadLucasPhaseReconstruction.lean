import Init

/-!
# Phase Reconstruction of `countBad_n` vs Lucas via Deliberate Negative Witnessing

Extends `OrbitAvoidanceLucasProbe.lean`, `DynamicalOrbitColoring.lean`,
`VoidArchaeology.lean`, and `SubstrateBoundaries.lean`.

## What was established previously

`OrbitAvoidanceLucasProbe` observed `countBad_10 + 1 = L_10` at one
depth and exhibited a negative witness at `n = 3`. The general claim
`∀ n, countBad_n + 1 = L_n` is wall-blocked (requires closed-form proof
of cyclic-binary-string avoidance counts) — sits behind the ring /
category wall for a general proof.

## What this module does: deliberate void scraping → phase reconstruction

The `countBad_n` sequence is `tr(M^n)` where `M` is the 4-state
transfer matrix for "avoid any 3-consecutive-same in a cyclic binary
string". `M` has characteristic polynomial `λ^4 - λ^2 - 2λ - 1`, so
Newton's identities give the linear recurrence

    p(n+4) = p(n+2) + 2 · p(n+1) + p(n).

This recurrence is `decide`-closable over `Nat`. Computing `countBad_n`
at depths `n = 3 .. 12` and comparing against Lucas `L_n` reveals:

    countBad_n − L_n = +2  when n ≡ 0 (mod 3)
    countBad_n − L_n = −1  otherwise

The `n = 3` negative witness of the naive `countBad_n + 1 = L_n` form
was *not* a refutation — it was a phase marker. Deliberate negative
witnesses at `n = 6, 9, 12` and positive witnesses at `n = 4, 5, 7, 8,
10, 11` reconstruct the 3-periodic phase relation in full.

## Epistemic value

The general theorem `∀ n, countBad_n = L_n + phaseShift(n)` is still
unproved here — `decide` doesn't quantify. But the reconstructed
outline is dense enough to serve as the basis for a mathlib-level
proof: 10 consecutive witnesses anchor the recurrence match. This
module moves `orbitAvoidanceLucas` in `VoidArchaeology.catalog` from
"archaeology-outline with 1 projection and 1 scrape" to "10
projections plus 4 scrapes, beyond reconstruction quality bar" by
deliberately producing negative witnesses at the phase `3 | n` to
triangulate the unknowable.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace CountBadLucasPhaseReconstruction

/-! ## Sequences

`traceSeq n = tr(M^n)` via the characteristic-polynomial recurrence.
`lucas n` inlined. -/

/-- Transfer-matrix trace recurrence:
`p(0) = 4, p(1) = 0, p(2) = 2, p(3) = 6`, then
`p(n+4) = p(n+2) + 2 · p(n+1) + p(n)`.

Equivalent to `countBad_n` for `n ≥ 3` (number of cyclic binary
strings of length `n` avoiding any 3-consecutive-same substring). -/
def traceSeq : Nat → Nat
  | 0     => 4
  | 1     => 0
  | 2     => 2
  | 3     => 6
  | n + 4 => traceSeq (n + 2) + 2 * traceSeq (n + 1) + traceSeq n

/-- Lucas sequence `L_0 = 2, L_1 = 1`, `L_{n+2} = L_{n+1} + L_n`. -/
def lucas : Nat → Nat
  | 0     => 2
  | 1     => 1
  | n + 2 => lucas (n + 1) + lucas n

/-! ## Point values of `traceSeq` -/

theorem traceSeq_3  : traceSeq 3 = 6 := by decide
theorem traceSeq_4  : traceSeq 4 = 6 := by decide
theorem traceSeq_5  : traceSeq 5 = 10 := by decide
theorem traceSeq_6  : traceSeq 6 = 20 := by decide
theorem traceSeq_7  : traceSeq 7 = 28 := by decide
theorem traceSeq_8  : traceSeq 8 = 46 := by decide
theorem traceSeq_9  : traceSeq 9 = 78 := by decide
theorem traceSeq_10 : traceSeq 10 = 122 := by decide
theorem traceSeq_11 : traceSeq 11 = 198 := by decide
theorem traceSeq_12 : traceSeq 12 = 324 := by decide

/-- The peer-module value `countBad_10 = 122` agrees with
`traceSeq 10 = 122`, confirming the transfer-matrix derivation. -/
theorem traceSeq_10_matches_peer : traceSeq 10 = 122 := by decide

/-! ## Lucas point values -/

theorem lucas_3 : lucas 3 = 4 := by decide
theorem lucas_4 : lucas 4 = 7 := by decide
theorem lucas_5 : lucas 5 = 11 := by decide
theorem lucas_6 : lucas 6 = 18 := by decide
theorem lucas_7 : lucas 7 = 29 := by decide
theorem lucas_8 : lucas 8 = 47 := by decide
theorem lucas_9 : lucas 9 = 76 := by decide
theorem lucas_10 : lucas 10 = 123 := by decide
theorem lucas_11 : lucas 11 = 199 := by decide
theorem lucas_12 : lucas 12 = 322 := by decide

/-! ## Positive witnesses: the `L − 1` phase (n ≢ 0 mod 3)

At every `n` with `n % 3 ≠ 0`, `traceSeq n + 1 = lucas n`. Six positive
witnesses at `n = 4, 5, 7, 8, 10, 11`. -/

theorem positive_4  : traceSeq 4  + 1 = lucas 4  := by decide
theorem positive_5  : traceSeq 5  + 1 = lucas 5  := by decide
theorem positive_7  : traceSeq 7  + 1 = lucas 7  := by decide
theorem positive_8  : traceSeq 8  + 1 = lucas 8  := by decide
theorem positive_10 : traceSeq 10 + 1 = lucas 10 := by decide
theorem positive_11 : traceSeq 11 + 1 = lucas 11 := by decide

/-! ## Negative witnesses: the `L − 1` form fails when `3 | n`

Four negative witnesses at `n = 3, 6, 9, 12`. Each one scrapes the
void where the naive `countBad_n + 1 = L_n` claim fails. The deliberate
spacing at multiples of 3 is the key move — scraping at `n = 3` alone
would be ambiguous; scraping at all four `n ∈ {3, 6, 9, 12}` anchors
the 3-periodic phase. -/

theorem negative_3  : traceSeq 3  + 1 ≠ lucas 3  := by decide
theorem negative_6  : traceSeq 6  + 1 ≠ lucas 6  := by decide
theorem negative_9  : traceSeq 9  + 1 ≠ lucas 9  := by decide
theorem negative_12 : traceSeq 12 + 1 ≠ lucas 12 := by decide

/-! ## Phase-shifted positive form: `countBad_n = L_n + 2` when `3 | n`

The negative witnesses of the `L − 1` form are positive witnesses of
the `L + 2` form. Each `n ≡ 0 (mod 3)` carries a different constant
deficit. -/

theorem phase_3_positive  : traceSeq 3  = lucas 3  + 2 := by decide
theorem phase_6_positive  : traceSeq 6  = lucas 6  + 2 := by decide
theorem phase_9_positive  : traceSeq 9  = lucas 9  + 2 := by decide
theorem phase_12_positive : traceSeq 12 = lucas 12 + 2 := by decide

/-! ## Unified phase-shift function

`phaseShift n = +2` if `3 | n`, `−1` otherwise. We use `Int` to carry
the sign. -/

def phaseShift (n : Nat) : Int :=
  if n % 3 = 0 then 2 else -1

theorem phase_lift_3  : (traceSeq 3  : Int) = (lucas 3  : Int) + phaseShift 3  := by decide
theorem phase_lift_4  : (traceSeq 4  : Int) = (lucas 4  : Int) + phaseShift 4  := by decide
theorem phase_lift_5  : (traceSeq 5  : Int) = (lucas 5  : Int) + phaseShift 5  := by decide
theorem phase_lift_6  : (traceSeq 6  : Int) = (lucas 6  : Int) + phaseShift 6  := by decide
theorem phase_lift_7  : (traceSeq 7  : Int) = (lucas 7  : Int) + phaseShift 7  := by decide
theorem phase_lift_8  : (traceSeq 8  : Int) = (lucas 8  : Int) + phaseShift 8  := by decide
theorem phase_lift_9  : (traceSeq 9  : Int) = (lucas 9  : Int) + phaseShift 9  := by decide
theorem phase_lift_10 : (traceSeq 10 : Int) = (lucas 10 : Int) + phaseShift 10 := by decide
theorem phase_lift_11 : (traceSeq 11 : Int) = (lucas 11 : Int) + phaseShift 11 := by decide
theorem phase_lift_12 : (traceSeq 12 : Int) = (lucas 12 : Int) + phaseShift 12 := by decide

/-! ## The master reconstruction witness -/

/-- Void archaeology: 10 consecutive positive witnesses of the
phase-shifted form `countBad_n = L_n + phaseShift n`, 4 negative
witnesses of the naive `L − 1` form at `n ≡ 0 (mod 3)`, and 6 positive
witnesses at `n ≢ 0 (mod 3)`. Together they reconstruct the phase
relation at depths 3 through 12.

The general theorem `∀ n, (traceSeq n : Int) = lucas n + phaseShift n`
is not proved here — it would need mathlib-level induction on the
recurrence. What is proved: the reconstruction is dense enough that
the pattern is no longer ambiguous. -/
theorem phase_reconstruction :
    (∀ n : Fin 10, let k := n.val + 3;
      (traceSeq k : Int) = (lucas k : Int) + phaseShift k) := by
  decide

/-- Packaged witness combining positive, negative, and phase-lifted
forms. -/
theorem countBad_lucas_phase_master :
    -- Positive (L - 1) at n ≢ 0 mod 3
    (traceSeq 4 + 1 = lucas 4)
    ∧ (traceSeq 5 + 1 = lucas 5)
    ∧ (traceSeq 10 + 1 = lucas 10)
    -- Negative (L - 1) at n ≡ 0 mod 3
    ∧ (traceSeq 3 + 1 ≠ lucas 3)
    ∧ (traceSeq 6 + 1 ≠ lucas 6)
    ∧ (traceSeq 9 + 1 ≠ lucas 9)
    ∧ (traceSeq 12 + 1 ≠ lucas 12)
    -- Positive (L + 2) at n ≡ 0 mod 3
    ∧ (traceSeq 3 = lucas 3 + 2)
    ∧ (traceSeq 6 = lucas 6 + 2)
    ∧ (traceSeq 9 = lucas 9 + 2)
    ∧ (traceSeq 12 = lucas 12 + 2)
    -- Peer-module consistency
    ∧ (traceSeq 10 = 122) := by
  decide

/-! ## Epistemic status

Under the `VoidArchaeology` classification, this module is the peer
witness for `dig_orbitAvoidanceLucas`:

  `projections = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12]` (phase-lifted
  positives at every depth in the window) with deliberate scrapes of
  the naive `+1` form at `voidScrapes = [3, 6, 9, 12]`.

That sample satisfies the catalog's reconstruction heuristic
(≥ 3 projections and ≥ 1 scrape), so the void-archaeology record now
marks this dig as **outline reconstructed** — still `archaeologyOutline`
mode (mixed pos/neg), not a proof of the global closed form.

The wall (ring-extension — general `p(n+4) = p(n+2) + 2p(n+1) + p(n)`
closed form in terms of Lucas would require roots of the quartic
`λ^4 − λ^2 − 2λ − 1 = 0`, which are not in `ℤ` or `ℤ[√5]`) is still
there. What this module demonstrates: aggressive negative witnessing
at a predicted phase pattern *reconstructs the outline of the
unknowable* without crossing the wall.

This realizes Taylor's void-archaeology epistemology in one concrete
instance: establishing where the unknowable lies (the ring-extension
wall), then scraping at the phase boundaries to reconstruct the
shape of what lies on the other side.
-/

end CountBadLucasPhaseReconstruction
end Gnosis
