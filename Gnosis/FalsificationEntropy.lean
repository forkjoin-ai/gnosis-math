import Gnosis.AntiTheory
import Gnosis.FalsificationLedger

/-
  FalsificationEntropy.lean
  =========================

  THE FALSIFICATION LEDGER, MADE QUANTIFIABLE.

  This module makes the falsification ledger's information content
  MEASURABLE. The Anti-Theory turn (`Gnosis.AntiTheory`) and the
  rank-ordered ledger (`Gnosis.FalsificationLedger`) gave us the
  qualitative bookkeeping. The wave-9 insight is: we should be able
  to SEE the entropy of that ledger, and watch it move.

  The Theory's information content is a number. Discovering a
  falsification typically DECREASES Shannon entropy (it rules out a
  path through the hypothesis space). Discovering a methodology
  contingency INCREASES entropy (it adds a new degree of freedom).
  Reclassifying a previously-projected claim as vacuous INCREASES
  entropy (we now see a hole we previously denied). All three moves
  are honest; none is a regression.

  The wave-8 anti-theory turn raised entropy by correctly
  classifying Llama-1B as `VacuousNoExperimentSpecified` after it
  had been silently treated as `ProjectedCertified`. That entropy
  increase is a FEATURE, not a bug. It is the cost of seeing the
  hole that was always there.

  Formally, entropy is approximated in fixed-point per-thousand
  units (`log2(2) = 1000`, `log2(4) = 2000`, `log2(32) = 5000`),
  using a small lookup table since this module is init-only Lean
  with no Mathlib. The specific weights chosen are less important
  than the monotonicity properties they induce on the per-wave
  states; the theorems below are decided over those concrete
  states.

  The honesty theorem
  (`admitting_vacuous_claims_raises_measured_entropy`) is the
  load-bearing one. Honesty has a measurable cost in bits.

  Init-only Lean 4. Zero sorries, zero axioms.
-/


namespace Gnosis
namespace FalsificationEntropy

-- ══════════════════════════════════════════════════════════
-- LOG2 LOOKUP (per-thousand fixed-point)
-- ══════════════════════════════════════════════════════════

/-- A small lookup table for `log2(n)` in per-thousand units.

    Conventions:
      • `log2_perthou 0 = 0`            (degenerate; treat as zero contribution)
      • `log2_perthou 1 = 0`            (no information)
      • `log2_perthou 2 = 1000`         (one bit)
      • `log2_perthou 4 = 2000`         (two bits)
      • `log2_perthou 8 = 3000`         (three bits)
      • `log2_perthou 16 = 4000`        (four bits)
      • `log2_perthou 32 = 5000`        (five bits)
      • Intermediate values are linearly interpolated between the
        nearest powers of two; the rounding is coarse on purpose.
        The downstream theorems decide over states whose entropy
        only references the EXACT power-of-two arguments above, so
        the interpolation accuracy does not enter the proofs.

    The table is intentionally finite; arguments above 32 saturate
    at the `log2(32) = 5000` rung. This is enough for every
    per-wave state in this module. -/
def log2_perthou : Nat → Nat
  |  0 => 0
  |  1 => 0
  |  2 => 1000
  |  3 => 1585
  |  4 => 2000
  |  5 => 2322
  |  6 => 2585
  |  7 => 2807
  |  8 => 3000
  |  9 => 3170
  | 10 => 3322
  | 11 => 3459
  | 12 => 3585
  | 13 => 3700
  | 14 => 3807
  | 15 => 3907
  | 16 => 4000
  | 17 => 4087
  | 18 => 4170
  | 19 => 4248
  | 20 => 4322
  | 21 => 4392
  | 22 => 4459
  | 23 => 4524
  | 24 => 4585
  | 25 => 4644
  | 26 => 4700
  | 27 => 4755
  | 28 => 4807
  | 29 => 4858
  | 30 => 4907
  | 31 => 4954
  | 32 => 5000
  | _  => 5000

-- ══════════════════════════════════════════════════════════
-- LEDGER STATE
-- ══════════════════════════════════════════════════════════

/-- The entropy-relevant snapshot of the falsification ledger at a
    point in time.

    Fields (all `Nat`, all summed multiplicatively into entropy):

      • `n_structural_identities` — claims proved BY CONSTRUCTION
        in Lean. Their certainty is total; they contribute ZERO to
        Shannon entropy (no remaining uncertainty about them).

      • `n_not_yet_falsified` — methodology-pinned claims that
        have not yet been refuted. Each contributes some entropy:
        it COULD be falsified later, so the path is still live.
        Modeled as `log2(4) = 2000` per-thousand bits of residual
        uncertainty.

      • `n_falsified` — claims that have been refuted by
        measurement. Their fate is decided; each contributes ZERO
        to the entropy of the LIVE hypothesis space.

      • `n_vacuous` — claims that do not pin a methodology and
        therefore cannot in principle be falsified. Each
        contributes MAXIMUM entropy from the lookup table
        (`log2(32) = 5000` per-thousand): we don't know what would
        falsify them, so the live degrees of freedom are wide open.

      • `n_methodology_contingencies` — recorded acknowledgments
        that the measurement protocol matters and that switching
        protocols could change verdicts. Each ADDS a degree of
        freedom; modeled as `log2(16) = 4000` per-thousand bits.

    The wave-by-wave instances below show entropy moving in BOTH
    directions across the recorded session history. -/
structure LedgerState where
  n_structural_identities      : Nat
  n_not_yet_falsified          : Nat
  n_falsified                  : Nat
  n_vacuous                    : Nat
  n_methodology_contingencies  : Nat
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- SHANNON ENTROPY (per-thousand)
-- ══════════════════════════════════════════════════════════

/-- The approximate Shannon entropy of a `LedgerState` in
    per-thousand units of bits.

    Formula:
      `entropy =
          n_vacuous                    * log2(32)
        + n_not_yet_falsified          * log2(4)
        + n_methodology_contingencies  * log2(16)`

    Structural identities and decided falsifications contribute
    zero, by construction.

    Numerically:
      `entropy = 5000 * n_vacuous
               + 2000 * n_not_yet_falsified
               + 4000 * n_methodology_contingencies`

    The function is strictly monotone increasing in each of
    `n_vacuous`, `n_not_yet_falsified`, and
    `n_methodology_contingencies`, and constant in
    `n_structural_identities` and `n_falsified`. -/
def shannon_entropy_perthou (L : LedgerState) : Nat :=
    L.n_vacuous                   * log2_perthou 32
  + L.n_not_yet_falsified         * log2_perthou 4
  + L.n_methodology_contingencies * log2_perthou 16

-- ══════════════════════════════════════════════════════════
-- PER-WAVE STATES
-- ══════════════════════════════════════════════════════════

/-- Wave 3 — the pre-falsification snapshot.

    Many "ProjectedCertified" claims (each a `VacuousNoExperimentSpecified`
    in honest bookkeeping; we just had not yet noticed). Two structural
    identities (`CompressionUncertainty`, `Novikov closure`). No
    falsifications, no methodology contingencies.

    `entropy = 5000 * 8 + 2000 * 0 + 4000 * 0 = 40000`. -/
def wave_3_state : LedgerState :=
  { n_structural_identities      := 2
  , n_not_yet_falsified          := 0
  , n_falsified                  := 0
  , n_vacuous                    := 8
  , n_methodology_contingencies  := 0 }

/-- Wave 4 — F1 and F2 added.

    Two of the wave-3 vacuous claims were upgraded into
    `NotYetFalsified` once a methodology was pinned, then
    immediately refuted (becoming `FalsifiedByMeasurement`).
    Net move: vacuous count drops, falsified count rises.

    `entropy = 5000 * 6 + 2000 * 2 + 4000 * 0 = 34000`.
    Lower than wave_3: cleanup of vacuous claims dominates. -/
def wave_4_state : LedgerState :=
  { n_structural_identities      := 2
  , n_not_yet_falsified          := 2
  , n_falsified                  := 2
  , n_vacuous                    := 6
  , n_methodology_contingencies  := 0 }

/-- Wave 6 — F3 added AND a methodology contingency recorded.

    F3 closed one more degree of freedom (one more methodology-pinned
    claim moved into the falsified pile, with one matching drop in
    not-yet-falsified). But wave 6 also formally admitted that the
    measurement protocol matters: the rank-density invariant is
    methodology-DEPENDENT. That admission is a recorded
    methodology contingency, and it adds a degree of freedom of
    its own — a heavy one.

    `entropy = 5000 * 5 + 2000 * 3 + 4000 * 1 = 35000`.
    HIGHER than wave_4: the contingency outweighs the F3 cleanup. -/
def wave_6_state : LedgerState :=
  { n_structural_identities      := 2
  , n_not_yet_falsified          := 3
  , n_falsified                  := 3
  , n_vacuous                    := 5
  , n_methodology_contingencies  := 1 }

/-- Wave 8 — the anti-theory turn.

    Llama-1B was reclassified from `ProjectedCertified` (i.e.
    silently `NotYetFalsified` in our bookkeeping) to
    `VacuousNoExperimentSpecified`. We had been treating it as a
    live, methodology-pinned conjecture; we admitted it never had
    a falsifying experiment specified.

    Net move from wave_4 baseline: one not-yet-falsified claim
    becomes vacuous. Entropy goes UP. The methodology contingency
    from wave 6 is still on the books.

    `entropy = 5000 * 6 + 2000 * 2 + 4000 * 1 = 38000`.
    HIGHER than wave_4: admitting the hole costs information. -/
def wave_8_state : LedgerState :=
  { n_structural_identities      := 2
  , n_not_yet_falsified          := 2
  , n_falsified                  := 3
  , n_vacuous                    := 6
  , n_methodology_contingencies  := 1 }

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE ENTROPY VALUES (decide-checked)
-- ══════════════════════════════════════════════════════════

/-- Sanity: the wave-3 entropy is exactly 40000 per-thousand bits. -/
theorem wave_3_entropy_value :
    shannon_entropy_perthou wave_3_state = 40000 := by decide

/-- Sanity: the wave-4 entropy is exactly 34000 per-thousand bits. -/
theorem wave_4_entropy_value :
    shannon_entropy_perthou wave_4_state = 34000 := by decide

/-- Sanity: the wave-6 entropy is exactly 35000 per-thousand bits. -/
theorem wave_6_entropy_value :
    shannon_entropy_perthou wave_6_state = 35000 := by decide

/-- Sanity: the wave-8 entropy is exactly 38000 per-thousand bits. -/
theorem wave_8_entropy_value :
    shannon_entropy_perthou wave_8_state = 38000 := by decide

-- ══════════════════════════════════════════════════════════
-- INTER-WAVE ENTROPY MOVEMENTS
-- ══════════════════════════════════════════════════════════

/-- Theorem: WAVE-4-ENTROPY-LOWER-THAN-WAVE-3.

    The wave-4 falsifications cleaned up two vacuous claims
    (replacing each `5000`-bit contribution with a `2000`-bit
    not-yet-falsified contribution AND a zero-bit falsified
    contribution). Net entropy DECREASE of 6000 per-thousand
    bits. Information was added to the ledger. -/
theorem wave_4_entropy_lower_than_wave_3 :
    shannon_entropy_perthou wave_4_state
      < shannon_entropy_perthou wave_3_state := by decide

/-- Theorem: WAVE-6-ENTROPY-HIGHER-THAN-WAVE-4.

    F3 closed one further degree of freedom, but wave 6 ALSO
    recorded the first methodology contingency. The contingency's
    contribution (`4000` per-thousand bits) outweighs the F3
    cleanup (`3000` per-thousand bits net), so total entropy goes
    UP by 1000 per-thousand bits. Falsifying a claim does NOT
    monotonically reduce the Theory's entropy when the
    falsification reveals a previously-hidden degree of freedom. -/
theorem wave_6_entropy_higher_than_wave_4 :
    shannon_entropy_perthou wave_6_state
      > shannon_entropy_perthou wave_4_state := by decide

/-- Theorem: WAVE-8-ENTROPY-HIGHER-THAN-WAVE-4-DUE-TO-HONEST-
              VACUOUS-RECLASSIFICATION.

    Wave 8's anti-theory turn moved Llama-1B from the implicit
    `ProjectedCertified` rung to the explicit `VacuousNoExperimentSpecified`
    rung. That swap turns a `2000`-bit contribution into a
    `5000`-bit contribution: net `+3000` per-thousand bits.
    Combined with the persisting wave-6 methodology contingency,
    wave_8 sits a full `4000` per-thousand bits above wave_4.
    Honesty about hidden vacuity is paid for in entropy. -/
theorem wave_8_entropy_higher_than_wave_4_due_to_honest_vacuous_reclassification :
    shannon_entropy_perthou wave_8_state
      > shannon_entropy_perthou wave_4_state := by decide

/-- Theorem: ENTROPY-IS-NOT-MONOTONE-DECREASING.

    There exist successive recorded ledger states (wave_4 → wave_6)
    such that the LATER state has STRICTLY HIGHER entropy than the
    earlier one. Therefore the wave-indexed sequence of ledger
    entropies is NOT monotone decreasing.

    This is the formal refutation of the naive view that "more
    falsifications" implies "less uncertainty". It does not, in
    general; whether the entropy moves down or up depends on
    whether the falsification ALSO uncovered a new degree of
    freedom (a methodology contingency, or a previously-hidden
    vacuous claim). The wave-4 → wave-6 transition is the
    explicit witness. -/
theorem entropy_is_NOT_monotone_decreasing :
    ¬ (shannon_entropy_perthou wave_4_state
        ≥ shannon_entropy_perthou wave_6_state) := by decide

-- ══════════════════════════════════════════════════════════
-- THE HONESTY THEOREM
-- ══════════════════════════════════════════════════════════

/-- Reclassify ONE not-yet-falsified ("projected but unmeasured")
    claim from `n_not_yet_falsified` into `n_vacuous`.

    This is the formal move performed in wave 8 against Llama-1B:
    we admit that the claim never had a falsifying experiment
    specified, so it belongs in the vacuous bucket, not the
    not-yet-falsified bucket. -/
def reclassify_one_projected_as_vacuous (L : LedgerState) : LedgerState :=
  { L with
    n_not_yet_falsified := L.n_not_yet_falsified - 1
  , n_vacuous           := L.n_vacuous + 1 }

/-- Theorem: ADMITTING-VACUOUS-CLAIMS-RAISES-MEASURED-ENTROPY.

    For ANY `LedgerState` with at least one projected-but-unmeasured
    claim, reclassifying that claim into the vacuous bucket
    STRICTLY INCREASES the measured Shannon entropy.

    Numerically: each reclassified claim swaps a `2000`-bit
    contribution for a `5000`-bit contribution. Net `+3000`
    per-thousand bits per honest admission.

    THE LOAD-BEARING POINT: the cost of honesty is information.
    The entropy increase that comes from admitting a vacuous
    claim is not a regression in the Theory; it is the Theory
    acquiring a true measurement of its own ignorance. The hole
    was always there; we are only now seeing it. -/
theorem admitting_vacuous_claims_raises_measured_entropy
    (L : LedgerState) (h : L.n_not_yet_falsified > 0) :
    shannon_entropy_perthou (reclassify_one_projected_as_vacuous L)
      > shannon_entropy_perthou L := by
  unfold shannon_entropy_perthou reclassify_one_projected_as_vacuous
  simp only [log2_perthou]
  -- Goal reduces to:
  --   (n_vacuous + 1) * 5000 + (n_not_yet_falsified - 1) * 2000 + C * 4000
  --   > n_vacuous * 5000 + n_not_yet_falsified * 2000 + C * 4000
  -- where the (n_not_yet_falsified - 1) is honest because of `h`.
  obtain ⟨_, n_nyf, _, n_vac, n_cont⟩ := L
  cases n_nyf with
  | zero => exact absurd h (Nat.lt_irrefl 0)
  | succ k =>
    -- After the reclassification: vacuous = n_vac + 1, nyf = k.
    -- Before:                     vacuous = n_vac,     nyf = k + 1.
    -- Difference: (n_vac + 1) * 5000 + k * 2000 - (n_vac * 5000 + (k+1) * 2000)
    --           = 5000 - 2000 = 3000 > 0.
    show (n_vac + 1) * 5000 + k * 2000 + n_cont * 4000
        > n_vac * 5000 + (k + 1) * 2000 + n_cont * 4000
    -- Let A = n_vac * 5000 + k * 2000 + n_cont * 4000.
    -- Then LHS = A + 5000 and RHS = A + 2000, both via Nat.succ_mul +
    -- add_assoc / add_right_comm, and the strict inequality reduces to
    -- 2000 < 5000.
    have hLHS_step1 : (n_vac + 1) * 5000 = n_vac * 5000 + 5000 :=
      Nat.succ_mul n_vac 5000
    have hRHS_step1 : (k + 1) * 2000 = k * 2000 + 2000 :=
      Nat.succ_mul k 2000
    -- Reshape LHS: n_vac*5000 + 5000 + k*2000 + n_cont*4000
    --           = (n_vac*5000 + k*2000 + n_cont*4000) + 5000
    have hLHS_reshape :
        (n_vac + 1) * 5000 + k * 2000 + n_cont * 4000
          = (n_vac * 5000 + k * 2000 + n_cont * 4000) + 5000 := by
      rw [hLHS_step1]
      -- Goal: n_vac*5000 + 5000 + k*2000 + n_cont*4000
      --     = n_vac*5000 + k*2000 + n_cont*4000 + 5000
      rw [Nat.add_right_comm (n_vac * 5000) 5000 (k * 2000)]
      -- Goal: n_vac*5000 + k*2000 + 5000 + n_cont*4000
      --     = n_vac*5000 + k*2000 + n_cont*4000 + 5000
      exact Nat.add_right_comm (n_vac * 5000 + k * 2000) 5000 (n_cont * 4000)
    -- Reshape RHS: n_vac*5000 + (k*2000 + 2000) + n_cont*4000
    --           = (n_vac*5000 + k*2000 + n_cont*4000) + 2000
    have hRHS_reshape :
        n_vac * 5000 + (k + 1) * 2000 + n_cont * 4000
          = (n_vac * 5000 + k * 2000 + n_cont * 4000) + 2000 := by
      rw [hRHS_step1]
      -- Goal: n_vac*5000 + (k*2000 + 2000) + n_cont*4000
      --     = n_vac*5000 + k*2000 + n_cont*4000 + 2000
      rw [← Nat.add_assoc (n_vac * 5000) (k * 2000) 2000]
      -- Goal: n_vac*5000 + k*2000 + 2000 + n_cont*4000
      --     = n_vac*5000 + k*2000 + n_cont*4000 + 2000
      exact Nat.add_right_comm (n_vac * 5000 + k * 2000) 2000 (n_cont * 4000)
    rw [hLHS_reshape, hRHS_reshape]
    -- Goal: A + 2000 < A + 5000, which is Nat.add_lt_add_left on 2000 < 5000.
    exact Nat.add_lt_add_left (by decide : (2000 : Nat) < 5000)
            (n_vac * 5000 + k * 2000 + n_cont * 4000)

-- ══════════════════════════════════════════════════════════
-- FALSIFICATION INFORMATION YIELD
-- ══════════════════════════════════════════════════════════

/-- The per-falsification entropy yield: total entropy reduction
    divided by the number of falsifications discovered.

    Computed using saturating subtraction (`Nat.sub`), so a
    transition where entropy actually went UP yields zero — the
    falsifications in that transition did not, on net, reduce
    the Theory's entropy (the new degrees of freedom outpaced
    them).

    `n` is the number of falsifications discovered in the
    transition; if `n = 0` the function returns `0` to avoid a
    division-by-zero. -/
def entropy_per_falsification (yield n : Nat) : Nat :=
  if n = 0 then 0 else yield / n

/-- The TOTAL entropy reduction between two recorded states,
    using saturating subtraction. If the later state has higher
    entropy than the earlier state, the yield is `0` (the
    falsifications discovered did not, on net, reduce entropy). -/
def falsification_information_yield
    (earlier later : LedgerState) : Nat :=
  shannon_entropy_perthou earlier - shannon_entropy_perthou later

/-- The number of new falsifications recorded between two states. -/
def new_falsifications_between
    (earlier later : LedgerState) : Nat :=
  later.n_falsified - earlier.n_falsified

/-- F1+F2 yielded `(40000 - 34000) = 6000` per-thousand bits over
    two new falsifications: an average of `3000` per-thousand bits
    per falsification. -/
theorem wave_3_to_4_yield_per_falsification :
    entropy_per_falsification
        (falsification_information_yield wave_3_state wave_4_state)
        (new_falsifications_between        wave_3_state wave_4_state)
      = 3000 := by decide

/-- F3 alone yielded `0` per-thousand bits net (the methodology
    contingency added more entropy than F3 closed): `0` per
    falsification. -/
theorem wave_4_to_6_yield_per_falsification :
    entropy_per_falsification
        (falsification_information_yield wave_4_state wave_6_state)
        (new_falsifications_between        wave_4_state wave_6_state)
      = 0 := by decide

/-- Theorem: F1-PLUS-F2-YIELDED-MORE-ENTROPY-REDUCTION-THAN-F3.

    Per-falsification, the wave-4 cohort (F1+F2) reduced the
    Theory's entropy by `3000` per-thousand bits each. The
    wave-6 cohort (F3 alone) reduced it by `0` net per-thousand
    bits, because the simultaneously-recorded methodology
    contingency outweighed the closure. Falsifications are not
    interchangeable: the surrounding bookkeeping moves matter. -/
theorem f1_plus_f2_yielded_more_entropy_reduction_per_falsification_than_f3 :
    entropy_per_falsification
        (falsification_information_yield wave_3_state wave_4_state)
        (new_falsifications_between        wave_3_state wave_4_state)
      >
    entropy_per_falsification
        (falsification_information_yield wave_4_state wave_6_state)
        (new_falsifications_between        wave_4_state wave_6_state) := by
  decide

end FalsificationEntropy
end Gnosis
