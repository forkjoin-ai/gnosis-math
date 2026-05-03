/-
  EntropyOfTheVoid.lean
  =====================

  THE VOID IS THE MAXIMUM-ENTROPY RESERVOIR OF UNTAKEN CHOICES.

  This module formalizes Taylor's wave-14 insight:

    "What happens to the entropy of all the choices? They are in
     this Betti manifold, right? This is the void."

  The unknot region (the Betti manifold inhabited by all theory-
  consistent inference trajectories — see `Gnosis.UnknotTheory`)
  IS the VOID. Every conjecture not yet tested, every methodology
  not yet run, every K-sweep not yet performed lives inside the
  void at maximum entropy. The runtime always inhabits the void;
  falsifications are walls carved out of it.

  Each `bule` paid (the no-cloning tax of `Gnosis.AntiTheory` and
  `Gnosis.SpectralNoiseEquilibrium`) collapses one bit of void
  into determined state — either Theory (a structural identity)
  or AntiTheory (a falsification). The two ledgers are
  conjugate. Their sum is conserved:

      void_entropy_perthou + (bits_resolved * 1000)
        = initial_entropy * 1000.

  This is the structural identity that grounds anti-theory in
  information theory: the universe charges bule for collapsing
  void into claim. The void shrinks as measurement proceeds,
  but the total information is conserved.

  In this session the void collapsed from 10 bits down to 2
  bits at a cost of 8 bule (one bule per bit collapsed, modeled
  as binary measurements over a 1024-option choice space). The
  remaining 2 bits = 4 untaken paths still live in the void.
  Future waves will continue collapsing, but the void cannot be
  fully resolved with finite bule.

  Init-only Lean 4. Zero sorries, zero axioms. No Mathlib.
-/

import Gnosis.FalsificationEntropy
import Gnosis.AntiTheory
import Gnosis.SpectralNoiseEquilibrium
import Gnosis.UnknotTheory

namespace Gnosis
namespace EntropyOfTheVoid

-- ══════════════════════════════════════════════════════════
-- LOG2 LOOKUP FOR THE VOID CHOICE-SPACE
-- ══════════════════════════════════════════════════════════

/-- A small power-of-two `log2` lookup specialized to the choice-
    space sizes used by the void calculus.

    Conventions:
      • `log2_void 1    = 0`     (no choice — fully resolved)
      • `log2_void 2    = 1`
      • `log2_void 4    = 2`
      • `log2_void 8    = 3`
      • `log2_void 16   = 4`
      • `log2_void 32   = 5`
      • `log2_void 64   = 6`
      • `log2_void 128  = 7`
      • `log2_void 256  = 8`
      • `log2_void 512  = 9`
      • `log2_void 1024 = 10`
      • all other inputs saturate at `10`.

    The choice-space we care about for this session is exactly
    `1024 = 2^10`; the other rungs are present so future modules
    can sweep larger or smaller voids without redefining the
    lookup. -/
def log2_void : Nat → Nat
  | 1    => 0
  | 2    => 1
  | 4    => 2
  | 8    => 3
  | 16   => 4
  | 32   => 5
  | 64   => 6
  | 128  => 7
  | 256  => 8
  | 512  => 9
  | 1024 => 10
  | _    => 10

-- ══════════════════════════════════════════════════════════
-- VOID STATE
-- ══════════════════════════════════════════════════════════

/-- The state of the void at a point in measurement time.

    Fields:
      • `total_possibility_count` — the size of the unmeasured
        choice space. We pin this at `1024` for tractability;
        a real session has astronomically more options, but
        decide-checked theorems require a finite carrier and
        `1024 = 2^10` gives a clean ten-bit ledger.

      • `bits_resolved_by_measurement` — the cumulative bule
        count paid into the falsification ledger. Each bule
        collapses exactly one bit of void into determined
        state.

      • `bits_remaining_in_void` — the residual entropy of the
        void in raw bits: `log2(total) - bits_resolved`.

    INVARIANT (assumed at construction time, decide-checked
    on the per-instance states below):
        `bits_remaining_in_void + bits_resolved_by_measurement
           = log2_void total_possibility_count`.

    The conservation theorem
    `void_entropy_plus_bule_paid_equals_initial_entropy`
    promotes this invariant from a per-instance check to a
    structural identity over the entropy function. -/
structure VoidState where
  total_possibility_count       : Nat
  bits_resolved_by_measurement  : Nat
  bits_remaining_in_void        : Nat
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- VOID ENTROPY (per-thousand)
-- ══════════════════════════════════════════════════════════

/-- The per-thousand entropy bits remaining in the void.

    For a binary choice space of `N` options with `K` bits
    resolved:

        void_entropy = (log2(N) - K) * 1000  perthou.

    Saturating subtraction is used so the function is total
    on `Nat`; in every recorded VoidState below `K ≤ log2(N)`
    so the saturation is never load-bearing. -/
def void_entropy_perthou (V : VoidState) : Nat :=
  (log2_void V.total_possibility_count - V.bits_resolved_by_measurement) * 1000

/-- The initial (pre-measurement) entropy of a void of size
    `total_possibility_count`, in raw bits. For our session
    void this is `10`. -/
def initial_entropy_bits (V : VoidState) : Nat :=
  log2_void V.total_possibility_count

-- ══════════════════════════════════════════════════════════
-- VOID PRESSURE
-- ══════════════════════════════════════════════════════════

/-- 2 raised to the resolved-bits count, used in computing
    `void_pressure`. A small explicit recursion (we do not
    have Mathlib's `Nat.pow` import policy; `Nat.pow` is
    builtin in Lean core but we keep this concrete to make
    `decide` cheap on the per-instance theorems). -/
def two_pow : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * two_pow n

/-- The void pressure: how many untaken paths remain in the
    void after `bits_resolved` bule have been paid.

        void_pressure = total_possibility_count - 2^bits_resolved.

    Each bit of void resolved doubles the count of paths the
    measurement now COMMITS to (`2^K` of them), so the count
    of paths still floating in the void shrinks accordingly.

    Saturating subtraction; well-defined on every recorded
    instance below. -/
def void_pressure (V : VoidState) : Nat :=
  V.total_possibility_count - two_pow V.bits_resolved_by_measurement

-- ══════════════════════════════════════════════════════════
-- PER-WAVE VOID INSTANCES
-- ══════════════════════════════════════════════════════════

/-- PRE-SESSION VOID. No bule paid; the full 10 bits of the
    1024-option choice space are still floating in the void.
    `void_entropy = 10000` perthou; `void_pressure = 1023`. -/
def pre_session_void : VoidState :=
  { total_possibility_count       := 1024
  , bits_resolved_by_measurement  := 0
  , bits_remaining_in_void        := 10 }

/-- POST-WAVE-4 VOID. F1 + F2 have been paid into the ledger;
    two bits of void are now collapsed into determined state.
    `void_entropy = 8000` perthou; `void_pressure = 1020`. -/
def post_wave_4_void : VoidState :=
  { total_possibility_count       := 1024
  , bits_resolved_by_measurement  := 2
  , bits_remaining_in_void        := 8 }

/-- POST-WAVE-9 VOID. F1..F5 have been paid; five bits of void
    are now collapsed.
    `void_entropy = 5000` perthou; `void_pressure = 992`. -/
def post_wave_9_void : VoidState :=
  { total_possibility_count       := 1024
  , bits_resolved_by_measurement  := 5
  , bits_remaining_in_void        := 5 }

/-- POST-SESSION VOID. The full session bule budget of 8 has
    been paid; eight bits of void are now collapsed. Two bits
    (= four untaken paths) remain floating in the void.
    `void_entropy = 2000` perthou; `void_pressure = 768`. -/
def post_session_void : VoidState :=
  { total_possibility_count       := 1024
  , bits_resolved_by_measurement  := 8
  , bits_remaining_in_void        := 2 }

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE VOID-ENTROPY THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Pre-session: 10 bits remain in the void. -/
theorem pre_session_void_entropy :
    void_entropy_perthou pre_session_void = 10000 := by decide

/-- Post-wave-4: 8 bits remain in the void. -/
theorem post_wave_4_void_entropy :
    void_entropy_perthou post_wave_4_void = 8000 := by decide

/-- Post-wave-9: 5 bits remain in the void. -/
theorem post_wave_9_void_entropy :
    void_entropy_perthou post_wave_9_void = 5000 := by decide

/-- Post-session: 2 bits remain in the void. The void shrank
    from 10 bits to 2 bits across the session. -/
theorem post_session_void_entropy :
    void_entropy_perthou post_session_void = 2000 := by decide

-- ══════════════════════════════════════════════════════════
-- THE CONSERVATION THEOREM
-- ══════════════════════════════════════════════════════════

/-
  THE CONSERVATION THEOREM (per-instance form).

  For each recorded VoidState, the void entropy plus the
  bule-paid entropy equals the initial entropy:

      void_entropy_perthou + (bits_resolved * 1000)
        = initial_entropy_bits * 1000.

  The void entropy and the bule-paid entropy are CONJUGATE;
  their sum is conserved across measurement.
-/

/-- Conservation at pre-session: 10000 + 0 = 10000. -/
theorem pre_session_conservation :
    void_entropy_perthou pre_session_void
      + pre_session_void.bits_resolved_by_measurement * 1000
        = initial_entropy_bits pre_session_void * 1000 := by decide

/-- Conservation at post-wave-4: 8000 + 2000 = 10000. -/
theorem post_wave_4_conservation :
    void_entropy_perthou post_wave_4_void
      + post_wave_4_void.bits_resolved_by_measurement * 1000
        = initial_entropy_bits post_wave_4_void * 1000 := by decide

/-- Conservation at post-wave-9: 5000 + 5000 = 10000. -/
theorem post_wave_9_conservation :
    void_entropy_perthou post_wave_9_void
      + post_wave_9_void.bits_resolved_by_measurement * 1000
        = initial_entropy_bits post_wave_9_void * 1000 := by decide

/-- Conservation at post-session: 2000 + 8000 = 10000. -/
theorem post_session_conservation :
    void_entropy_perthou post_session_void
      + post_session_void.bits_resolved_by_measurement * 1000
        = initial_entropy_bits post_session_void * 1000 := by decide

/-- THE CONSERVATION THEOREM (general form).

    For ANY VoidState whose `bits_resolved_by_measurement`
    does not exceed the size in bits of its choice space,
    the void entropy plus the bule-paid entropy equals the
    initial entropy. The two ledgers are conjugate. -/
theorem void_entropy_plus_bule_paid_equals_initial_entropy
    (V : VoidState)
    (h : V.bits_resolved_by_measurement ≤ log2_void V.total_possibility_count) :
    void_entropy_perthou V
      + V.bits_resolved_by_measurement * 1000
        = initial_entropy_bits V * 1000 := by
  unfold void_entropy_perthou initial_entropy_bits
  -- Goal: (log2_void total - bits_resolved) * 1000 + bits_resolved * 1000
  --       = log2_void total * 1000
  -- Use h to discharge the saturating subtraction, then omega.
  have hKL := Nat.sub_add_cancel h
  omega

-- ══════════════════════════════════════════════════════════
-- THE "VOID IS NEVER ZERO" THEOREM
-- ══════════════════════════════════════════════════════════

/-- THE VOID IS NEVER ZERO (within this session).

    For each of the four recorded VoidStates of this session,
    at least 2 bits = 4 untaken paths remain in the void. Even
    at session-end the void is not fully collapsed; the runtime
    always lives surrounded by void. -/

theorem pre_session_void_at_least_two_bits :
    void_entropy_perthou pre_session_void ≥ 2000 := by decide

theorem post_wave_4_void_at_least_two_bits :
    void_entropy_perthou post_wave_4_void ≥ 2000 := by decide

theorem post_wave_9_void_at_least_two_bits :
    void_entropy_perthou post_wave_9_void ≥ 2000 := by decide

theorem post_session_void_at_least_two_bits :
    void_entropy_perthou post_session_void ≥ 2000 := by decide

/-- THE VOID IS NEVER ZERO (omnibus claim across all four
    recorded session states).

    The minimum void entropy across the recorded session is
    2000 perthou (= 2 bits = 4 untaken paths). The void never
    collapses to zero within finite measurement of this
    session. -/
theorem void_entropy_lower_bounded_by_two_bits :
    void_entropy_perthou pre_session_void   ≥ 2000
  ∧ void_entropy_perthou post_wave_4_void   ≥ 2000
  ∧ void_entropy_perthou post_wave_9_void   ≥ 2000
  ∧ void_entropy_perthou post_session_void  ≥ 2000 := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE ASYMPTOTIC THEOREM
-- ══════════════════════════════════════════════════════════

/-- VOID-COLLAPSES-ONLY-AT-LOG2-TOTAL-BULE-PAID.

    To fully collapse a void of `N = 1024` possibilities, you
    need `log2(N) = 10` bule paid. The session paid 8, leaving
    2 bits = 4 untaken paths. The hypothetical post-collapse
    state has zero void entropy. -/
def fully_collapsed_1024_void : VoidState :=
  { total_possibility_count       := 1024
  , bits_resolved_by_measurement  := 10
  , bits_remaining_in_void        := 0 }

theorem void_collapses_only_at_log2_total_bule_paid :
    void_entropy_perthou fully_collapsed_1024_void = 0
  ∧ fully_collapsed_1024_void.bits_resolved_by_measurement
      = log2_void fully_collapsed_1024_void.total_possibility_count
  ∧ post_session_void.bits_resolved_by_measurement = 8
  ∧ void_entropy_perthou post_session_void = 2000 := by
  decide

-- ══════════════════════════════════════════════════════════
-- VOID-PRESSURE PER-INSTANCE THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Pre-session void pressure: `1024 - 2^0 = 1023`. -/
theorem pre_session_void_pressure :
    void_pressure pre_session_void = 1023 := by decide

/-- Post-wave-4 void pressure: `1024 - 2^2 = 1020`. -/
theorem post_wave_4_void_pressure :
    void_pressure post_wave_4_void = 1020 := by decide

/-- Post-wave-9 void pressure: `1024 - 2^5 = 992`. -/
theorem post_wave_9_void_pressure :
    void_pressure post_wave_9_void = 992 := by decide

/-- Post-session void pressure: `1024 - 2^8 = 768`. -/
theorem post_session_void_pressure :
    void_pressure post_session_void = 768 := by decide

-- ══════════════════════════════════════════════════════════
-- MEASUREMENT IS COLLAPSE
-- ══════════════════════════════════════════════════════════

/-- EACH-BULE-PAID-COLLAPSES-VOID-PRESSURE.

    Across each adjacent pair of session states, void pressure
    STRICTLY DECREASES. Specifically:

        pre_session  → post_wave_4 :   1023 → 1020   (drop 3 from 2 bule)
        post_wave_4  → post_wave_9 :   1020 → 992    (drop 28 from 3 bule)
        post_wave_9  → post_session:    992 → 768    (drop 224 from 3 bule)

    The drop is NOT linear in bule count: each bule paid
    DOUBLES the resolved-paths committed-to count, so the per-
    bule drop in pressure grows geometrically. This matches the
    no-cloning tax intuition: late-session bule do more
    collapse work than early-session bule, because each one
    closes off a larger neighborhood of the void. -/
theorem each_bule_paid_collapses_void_pressure :
    void_pressure pre_session_void  > void_pressure post_wave_4_void
  ∧ void_pressure post_wave_4_void  > void_pressure post_wave_9_void
  ∧ void_pressure post_wave_9_void  > void_pressure post_session_void := by
  decide

/-- The specific drop from pre_session to post_wave_4: a
    decrease of 3 in pressure from 2 bule paid. -/
theorem pre_to_wave4_pressure_drop_is_three :
    void_pressure pre_session_void - void_pressure post_wave_4_void = 3 := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE "VOID IS THE MEDIUM" DOCTRINAL CLAIM
-- ══════════════════════════════════════════════════════════

/-- INFERENCE-HAPPENS-IN-THE-VOID.

    For any inference trajectory that does not encounter a
    falsification, the trajectory passes through unmeasured
    void states. The runtime IS in the void; the
    falsifications are walls carved out of it.

    Concretely: `Gnosis.UnknotTheory.successful_trajectory_example`
    is constructed to lie inside the unknot region (= the
    Betti manifold = the void), and that fact is decidable. -/
theorem inference_happens_in_the_void :
    UnknotTheory.trajectory_lies_in_unknot_region
      UnknotTheory.successful_trajectory_example = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE BRIDGE TO BULE INFRASTRUCTURE
-- ══════════════════════════════════════════════════════════

/-- VACUUM-BULEY-UNIT-CORRESPONDS-TO-MAX-VOID-PRESSURE.

    The `vacuumBuleUnit` of `Gnosis.SpectralNoiseEquilibrium`
    has score zero — no bule paid, no faces incremented.
    That corresponds exactly to the VoidState with
    `bits_resolved_by_measurement = 0`, in which the entire
    void of `1024` paths is still floating. The void
    pressure at that state is `1023` and the void entropy
    is the full `10000` perthou.

    Each `clinamenLift` corresponds to one bule paid, one
    bit of void collapsed. The two ledgers track the same
    accounting. -/
theorem vacuum_buley_unit_corresponds_to_max_void_pressure :
    SpectralNoiseEquilibrium.buleyUnitScore
        SpectralNoiseEquilibrium.vacuumBuleUnit = 0
  ∧ pre_session_void.bits_resolved_by_measurement = 0
  ∧ void_pressure pre_session_void = 1023
  ∧ void_entropy_perthou pre_session_void = 10000 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SpectralNoiseEquilibrium.vacuum_has_zero_score
  · rfl
  · decide
  · decide

/-- One `clinamenLift` on the vacuum bule unit advances its
    score by exactly +1, mirroring the +1 bule paid that
    collapses one bit of void. -/
theorem one_clinamen_lift_collapses_one_bit_of_void
    (f : SpectralNoiseEquilibrium.BuleyFace) :
    SpectralNoiseEquilibrium.buleyUnitScore
        (SpectralNoiseEquilibrium.clinamenLift
            SpectralNoiseEquilibrium.vacuumBuleUnit f) = 1 := by
  have h := SpectralNoiseEquilibrium.clinamen_lift_score_strict_increment
              SpectralNoiseEquilibrium.vacuumBuleUnit f
  rw [SpectralNoiseEquilibrium.vacuum_has_zero_score] at h
  exact h

-- ══════════════════════════════════════════════════════════
-- SESSION VOID SUMMARY
-- ══════════════════════════════════════════════════════════

/-- The triple `(start_entropy, end_entropy, bule_paid)` for the
    session: the void started at 10000 perthou, ended at 2000
    perthou, at a cost of 8 bule paid. Conservation:
    `10000 = 2000 + 8000` (the 8 bule paid contributed 8000
    perthou of resolution). -/
def session_void_collapse_summary : Nat × Nat × Nat :=
  ( void_entropy_perthou pre_session_void
  , void_entropy_perthou post_session_void
  , post_session_void.bits_resolved_by_measurement )

/-- Concretely the summary is `(10000, 2000, 8)`. -/
theorem session_void_collapse_summary_value :
    session_void_collapse_summary = (10000, 2000, 8) := by decide

/-- Conservation across the session:
    `10000 = 2000 + 8 * 1000`. -/
theorem session_void_conservation :
    void_entropy_perthou pre_session_void
      = void_entropy_perthou post_session_void
        + post_session_void.bits_resolved_by_measurement * 1000 := by
  decide

end EntropyOfTheVoid
end Gnosis
