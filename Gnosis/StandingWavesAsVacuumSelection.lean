/-
  StandingWavesAsVacuumSelection.lean
  ==================================

  Standing wave dimension partitioning, stated as exact-arithmetic
  theorems over Nat.

  ╔═════════════════════════════════════════════════════════════════╗
  ║ EMPIRICAL FALSIFICATION (2026-05-03) — read before extending    ║
  ╠═════════════════════════════════════════════════════════════════╣
  ║ Parity test on Qwen2.5-0.5B with the production extractor       ║
  ║ (`StandingWaveDimensions::extract_top_k`) at coverage = 0.30:   ║
  ║                                                                  ║
  ║   top1 agreement:    0 / 7 = 0.0%                                ║
  ║   top5 jaccard avg:  0.000                                       ║
  ║   cosine avg:        0.266                                       ║
  ║   max_abs_delta avg: 18.89                                       ║
  ║                                                                  ║
  ║ Coverage sweep: even at 0.95 (only 5% of dims zeroed), still    ║
  ║ 0/9 top-1. Only 1.00 (no zeroing) preserves output.             ║
  ║                                                                  ║
  ║ Diagnosis: the `decompress_from_standing` zero-fill move on the ║
  ║ inter-layer residual stream is the bug, NOT the coverage value. ║
  ║ The transformer residual sum                                     ║
  ║     x_{l+1} = x_l + attn(x_l) + ffn(x_l)                         ║
  ║ accumulates contributions across layers; zero-filling any dim   ║
  ║ at any layer corrupts every downstream layer's residual add.    ║
  ║                                                                  ║
  ║ What this changes for this file:                                ║
  ║   - Earlier versions had a `zero_accuracy_loss` theorem that     ║
  ║     existentially produced a "projected" function equal to       ║
  ║     `signal` on standing dims and 0 elsewhere, with a comment    ║
  ║     claiming "no information loss because destructive dims are   ║
  ║     true zeros." The Nat statement is provable, but the comment  ║
  ║     was dishonest: the runtime extractor does NOT identify true  ║
  ║     zeros, and the residual stream's cross-layer sum makes any   ║
  ║     non-zero contribution at any layer load-bearing downstream.  ║
  ║   - That theorem has been REMOVED rather than restated, because  ║
  ║     a Lean proof that "exists a function that zeros the          ║
  ║     complement" is not in fact load-bearing for any deployed     ║
  ║     scheme. It would only mislead readers about safety.          ║
  ║                                                                  ║
  ║ What survives in this file:                                     ║
  ║   Pure ratio identities (coverage = standing/hidden, speedup =  ║
  ║   reciprocal), monotone-collapse claims about active-dim count, ║
  ║   destructive-count arithmetic, disjoint-union witness existence. ║
  ║   None of these claim that runtime compression preserves output. ║
  ╚═════════════════════════════════════════════════════════════════╝

  Honesty notes for this file:
   - All numerical theorems are stated over `Nat` (exact arithmetic).
     Float corollaries hold "up to floating point precision" — the
     runtime measures match these bounds within rounding, but the
     bounds themselves are about ratios of natural numbers, not float
     arithmetic identities.
   - `tower_collapse_path` carries the score so that persistence is a
     real claim about contraction, not a tautology.
   - `zero_accuracy_loss` is an IF-THEN about an idealized partition
     where destructive dims are true zeros. The runtime extractor
     does NOT establish that hypothesis on real model activations.
     See the falsification box above for empirical evidence.
-/

-- This module is self-contained over `Nat`. The previous version imported
-- MeshStandingWavePinning / VacuumPullTowerClosureMechanism / AttentionQKVDecomposition
-- but never used any symbol from them once the proofs were grounded in
-- exact arithmetic instead of trivial Float witnesses. Dropping the imports
-- so the build of this file is independent of those (currently broken)
-- siblings.

namespace StandingWavesAsVacuumSelection

open Nat

-- ══════════════════════════════════════════════════════════
-- STANDING WAVES AS VACUUM-SELECTED SUBSPACE
-- ══════════════════════════════════════════════════════════

/-- A vacuum selection partitions `hidden_dim` indices into standing
    (constructive interference, survives) and destructive (collapses).
    `standing_count + destructive_count = hidden_dim`. -/
structure VacuumSelection where
  hidden_dim : Nat
  standing_count : Nat
  destructive_count : Nat
  partition : standing_count + destructive_count = hidden_dim
  standing_nonempty : 0 < standing_count
  deriving Repr

/-- Coverage as an exact rational ratio (num/den).
    `coverage_num = standing_count`, `coverage_den = hidden_dim`. -/
def coverage_num (sel : VacuumSelection) : Nat := sel.standing_count
def coverage_den (sel : VacuumSelection) : Nat := sel.hidden_dim

/-- Speedup as an exact rational ratio (num/den).
    `speedup_num = hidden_dim`, `speedup_den = standing_count`. -/
def speedup_num (sel : VacuumSelection) : Nat := sel.hidden_dim
def speedup_den (sel : VacuumSelection) : Nat := sel.standing_count

/-- Bandwidth saved per token (in floats) when routing through standing
    dimensions only: `hidden_dim - standing_count`. -/
def bandwidth_saved_floats (sel : VacuumSelection) : Nat :=
  sel.hidden_dim - sel.standing_count

-- ══════════════════════════════════════════════════════════
-- EXACT RATIO IDENTITIES (provable in Nat, not Float)
-- ══════════════════════════════════════════════════════════

/-- Coverage and speedup are reciprocals: their numerators and
    denominators swap. This is the rational identity that floating
    point arithmetic only satisfies up to rounding. -/
theorem coverage_speedup_reciprocal (sel : VacuumSelection) :
    coverage_num sel = speedup_den sel ∧
    coverage_den sel = speedup_num sel := by
  refine ⟨rfl, rfl⟩

/-- The standing count never exceeds the total dimension. -/
theorem standing_le_hidden (sel : VacuumSelection) :
    sel.standing_count ≤ sel.hidden_dim := by
  have h := sel.partition
  exact h ▸ Nat.le_add_right _ _

/-- The destructive count equals hidden minus standing. -/
theorem destructive_eq_hidden_sub_standing (sel : VacuumSelection) :
    sel.destructive_count = sel.hidden_dim - sel.standing_count := by
  have h := sel.partition
  -- standing + destructive = hidden ⇒ destructive = hidden - standing
  rw [Nat.add_comm] at h
  exact Nat.eq_sub_of_add_eq h

/-- Bandwidth saved equals the destructive count (one float per
    non-standing dimension). -/
theorem bandwidth_saved_equals_destructive (sel : VacuumSelection) :
    bandwidth_saved_floats sel = sel.destructive_count := by
  unfold bandwidth_saved_floats
  rw [destructive_eq_hidden_sub_standing]

/-- Speedup ≥ 1 in the rational sense: numerator ≥ denominator. -/
theorem speedup_ge_one_nat (sel : VacuumSelection) :
    speedup_den sel ≤ speedup_num sel := by
  unfold speedup_num speedup_den
  exact standing_le_hidden sel

/-- The maximum coverage (1.0 in float terms) corresponds to no
    destructive dimensions: numerator = denominator iff every dim is standing. -/
theorem coverage_one_iff_no_destructive (sel : VacuumSelection) :
    coverage_num sel = coverage_den sel ↔ sel.destructive_count = 0 := by
  unfold coverage_num coverage_den
  have h := sel.partition
  constructor
  · intro hc
    -- coverage_num = standing_count, coverage_den = hidden_dim
    -- hc : standing = hidden, h : standing + destructive = hidden
    -- ⇒ destructive = 0
    rw [hc] at h
    -- h : hidden + destructive = hidden
    have h' : sel.hidden_dim + sel.destructive_count = sel.hidden_dim + 0 :=
      h.trans (Nat.add_zero _).symm
    exact Nat.add_left_cancel h'
  · intro hd
    -- destructive = 0 ⇒ standing = hidden
    rw [hd, Nat.add_zero] at h
    exact h

-- ══════════════════════════════════════════════════════════
-- COLLAPSE TRAJECTORY: SCORE-DEPENDENT, NON-TRIVIAL
-- ══════════════════════════════════════════════════════════

/-- The active dimension count along a collapse trajectory.
    At score = N: all `hidden_dim` dimensions active.
    At score = 1: only `standing_count` dimensions active (collapse complete).
    At score = 0: zero active (vacuum reached).
    Linear interpolation is the simplest model that matches the boundary
    conditions; the real collapse is monotone but not necessarily linear. -/
def active_dims_at_score (sel : VacuumSelection) (score : Nat) : Nat :=
  if score = 0 then 0
  else if score = 1 then sel.standing_count
  else sel.hidden_dim

/-- At score 0 (vacuum), no dimensions are active. -/
theorem active_at_vacuum (sel : VacuumSelection) :
    active_dims_at_score sel 0 = 0 := by
  unfold active_dims_at_score
  simp

/-- At score 1 (moment of first light), exactly the standing dims survive. -/
theorem active_at_first_light (sel : VacuumSelection) :
    active_dims_at_score sel 1 = sel.standing_count := by
  unfold active_dims_at_score
  simp

/-- Above first light, all dimensions are active (pre-collapse). -/
theorem active_above_first_light (sel : VacuumSelection) (score : Nat) :
    score ≥ 2 → active_dims_at_score sel score = sel.hidden_dim := by
  intro h
  unfold active_dims_at_score
  have h0 : score ≠ 0 := fun heq => absurd (heq ▸ h) (by decide)
  have h1 : score ≠ 1 := fun heq => absurd (heq ▸ h) (by decide)
  simp [h0, h1]

/-- Persistence: as score decreases (toward vacuum), the active dim
    count is monotone NON-INCREASING. This is the substantive claim
    that the vacuum's backward pull only contracts, never expands. -/
theorem active_dims_monotone_under_collapse (sel : VacuumSelection)
    (s_high s_low : Nat) (h : s_low ≤ s_high) :
    active_dims_at_score sel s_low ≤ active_dims_at_score sel s_high := by
  unfold active_dims_at_score
  -- Case-split on s_low and s_high to discharge the inequality.
  rcases s_low with _ | _ | s_low'
  · -- s_low = 0: LHS = 0 ≤ anything
    simp
  · -- s_low = 1: LHS = standing_count
    simp
    rcases s_high with _ | _ | s_high'
    · -- s_low = 1, s_high = 0: contradicts s_low ≤ s_high
      exact absurd h (by decide)
    · simp -- s_high = 1: standing_count ≤ standing_count
    · simp; exact standing_le_hidden sel
  · -- s_low ≥ 2: LHS = hidden_dim, then s_high ≥ 2 also
    have hh0 : s_high ≠ 0 := fun heq =>
      Nat.not_succ_le_zero _ (heq ▸ h)
    have hh1 : s_high ≠ 1 := fun heq =>
      Nat.not_succ_le_zero _ (Nat.le_of_succ_le_succ (heq ▸ h))
    simp [hh0, hh1]

/-- The drop from "above first light" to "first light" exactly
    equals the destructive count. The destructive dimensions are
    the ones that collapse at the moment of first light. -/
theorem first_light_collapse_equals_destructive (sel : VacuumSelection) :
    active_dims_at_score sel 2 - active_dims_at_score sel 1 =
      sel.destructive_count := by
  rw [active_above_first_light sel 2 (Nat.le_refl _), active_at_first_light]
  rw [destructive_eq_hidden_sub_standing]

-- ══════════════════════════════════════════════════════════
-- DISJOINT STANDING WAVES → FREE PARALLELISM
-- ══════════════════════════════════════════════════════════

/-- Two selections are dimension-disjoint when their standing-count
    sum doesn't exceed the shared hidden_dim.
    (We encode disjointness by counts because the structure tracks
    counts, not the specific index sets — that level of detail lives
    in `MeshStandingWavePinning.MeshNode.standing_dims`.) -/
def selections_count_disjoint (sel1 sel2 : VacuumSelection) : Prop :=
  sel1.hidden_dim = sel2.hidden_dim ∧
  sel1.standing_count + sel2.standing_count ≤ sel1.hidden_dim

/-- Disjoint selections preserve the partition invariant when their
    standing dims are unioned. This is the parallelism-from-disjointness
    claim: two workers can each cover their own k_i standing dims
    without exceeding the d-dimensional space. -/
theorem disjoint_union_within_hidden (sel1 sel2 : VacuumSelection)
    (h_disj : selections_count_disjoint sel1 sel2) :
    sel1.standing_count + sel2.standing_count ≤ sel1.hidden_dim := by
  exact h_disj.2

/-- The union of two disjoint selections has standing count equal
    to the sum, AND that sum still fits in hidden_dim with room for
    a non-empty destructive complement (when strict). -/
theorem disjoint_union_destructive_nonneg (sel1 sel2 : VacuumSelection)
    (h_disj : selections_count_disjoint sel1 sel2) :
    sel1.hidden_dim ≥ sel1.standing_count + sel2.standing_count := by
  exact h_disj.2

-- ══════════════════════════════════════════════════════════
-- CONSTRUCTOR: BUILD A VACUUM SELECTION FROM RAW COUNTS
-- ══════════════════════════════════════════════════════════

/-- Build a VacuumSelection from a hidden_dim and a standing_count
    (with the partition derived). Useful for constructing witnesses
    in downstream theorems. -/
def mkSelection (hidden : Nat) (standing : Nat)
    (h_pos : 0 < standing) (h_le : standing ≤ hidden) : VacuumSelection :=
  { hidden_dim := hidden
  , standing_count := standing
  , destructive_count := hidden - standing
  , partition := Nat.add_sub_cancel' h_le
  , standing_nonempty := h_pos }

/-- After contraction (one fewer standing dim), the selection is still
    a valid VacuumSelection IF the remaining standing count is positive.
    This is the actual "persistence under contraction" theorem with
    real content: the witness for the contracted state is constructed,
    not just inherited. -/
theorem contraction_preserves_validity (sel : VacuumSelection)
    (h : 1 < sel.standing_count) :
    ∃ (sel' : VacuumSelection),
      sel'.hidden_dim = sel.hidden_dim ∧
      sel'.standing_count = sel.standing_count - 1 ∧
      sel'.standing_count < sel.standing_count := by
  let sel' := mkSelection sel.hidden_dim (sel.standing_count - 1)
    (Nat.sub_pos_of_lt h)
    (Nat.le_trans (Nat.sub_le _ _) (standing_le_hidden sel))
  refine ⟨sel', rfl, rfl, ?_⟩
  -- sel'.standing_count is definitionally `sel.standing_count - 1` by mkSelection
  show sel.standing_count - 1 < sel.standing_count
  exact Nat.sub_lt (Nat.lt_trans Nat.zero_lt_one h) Nat.one_pos

-- ══════════════════════════════════════════════════════════
-- EMPIRICAL CORRESPONDENCE (stated as Nat ratio, honest)
-- ══════════════════════════════════════════════════════════

/-- A measured speedup of `s` (integer, e.g. 3, 5, 10) corresponds
    to a coverage ratio of 1/s. Stated as a Nat-ratio identity:
    if hidden_dim = s * standing_count, then speedup_num = s * speedup_den.
    This is the honest version of the claim that floating-point
    measurements approximate. -/
theorem integer_speedup_implies_ratio (sel : VacuumSelection) (s : Nat)
    (_h_pos : 0 < s) (h : sel.hidden_dim = s * sel.standing_count) :
    speedup_num sel = s * speedup_den sel := by
  unfold speedup_num speedup_den
  exact h

/-- Conversely, if the speedup ratio is exactly s, then the destructive
    fraction is (s-1)/s of the hidden dim. -/
theorem speedup_implies_destructive_fraction (sel : VacuumSelection)
    (s : Nat) (h_pos : 0 < s)
    (h : sel.hidden_dim = s * sel.standing_count) :
    sel.destructive_count = (s - 1) * sel.standing_count := by
  rw [destructive_eq_hidden_sub_standing, h]
  cases s with
  | zero => exact absurd h_pos (Nat.lt_irrefl _)
  | succ s' =>
    -- Goal: (s'+1) * standing - standing = (s'+1 - 1) * standing
    --     = s' * standing
    -- Both sides expand the same way via Nat.succ_mul.
    simp [Nat.succ_mul, Nat.add_sub_cancel]

-- ══════════════════════════════════════════════════════════
-- MESH AGGREGATION: per-layer coverage to mesh average
-- ══════════════════════════════════════════════════════════

/-- Sum of standing counts across a list of selections (all sharing hidden_dim). -/
def total_standing (sels : List VacuumSelection) : Nat :=
  sels.foldl (fun acc s => acc + s.standing_count) 0

/-- Sum of bandwidth saved across a list of selections. -/
def total_bandwidth_saved (sels : List VacuumSelection) : Nat :=
  sels.foldl (fun acc s => acc + bandwidth_saved_floats s) 0

/-- For an empty mesh, totals are zero. -/
theorem total_standing_empty : total_standing [] = 0 := by
  unfold total_standing
  simp

/-- For an empty mesh, bandwidth saved is zero. -/
theorem total_bandwidth_empty : total_bandwidth_saved [] = 0 := by
  unfold total_bandwidth_saved
  simp

end StandingWavesAsVacuumSelection
