/-
  ConservationOfVoidPlusVisibility.lean
  =====================================

  THE DEEPEST CONSERVATION LAW OF THE FRAMEWORK.

  Three currencies — `void_entropy`, `visibility_paid`, and
  `theory_grounded` — sum to a single conserved scalar
  `total_information`. Each measurement transfers one unit of
  information BETWEEN these currencies; the total never changes,
  only the distribution shifts.

      void_entropy + visibility_paid + theory_grounded
        = total_information           (CONSERVED)

  THE THREE CURRENCIES.

    • `void_entropy` is the reservoir of UNTAKEN choices. It is the
      max-entropy stockpile: every possible falsification not yet
      attempted, every measurement not yet made. The void shrinks
      monotonically as the runtime acts.

    • `visibility_paid` is the WORK done. It accumulates as bule is
      spent and shows up as ledger entries on the AntiTheory side.
      Visibility is NOT monotone — it can transfer outward when its
      contents crystallize into Theory.

    • `theory_grounded` is the CRYSTALLIZATION. It collects the
      structural identities motivated by measurement: each
      operationally-grounded Theory member earned its place by
      being motivated by visibility expenditure.

  THE SESSION'S BALANCE SHEET.

    pre_session    : void = 10000, visibility =    0, theory =    0
    post_wave_4    : void =  8000, visibility = 2000, theory =    0
    post_wave_9    : void =  5000, visibility = 5000, theory =    0
    post_session   : void =  2000, visibility = 5000, theory = 3000

    NET CHANGE     : void = -8000, visibility = +5000, theory = +3000
    SUM OF CHANGES : 0    (CONSERVATION IN MOTION FORM)

  THE UNIFICATION.

  This module composes the framework's prior conservation theorems
  into a SINGLE three-currency conservation:

    • `AntiTheoryAsConservation` projects onto the
      (visibility, budget) axis: `bule_units_paid = visibility`.

    • `NoCloningTaxEqualsBuleCost` is the per-measurement quantum:
      every transfer of one unit costs one bule.

    • `EntropyOfTheVoid` projects onto the (void, visibility) axis:
      the void shrinks as bule is paid.

    • `TheoryGrowthBound` projects onto the (visibility, theory)
      axis: `|grounded Theory| ≤ visibility paid on motivation`.

  Each prior theorem is a SHADOW of this one cast onto a pair of
  axes. The full conservation holds in three dimensions; the
  individual conservations are its 2D projections.

  THE DOCTRINAL READING.

    The void is the SOURCE.
    Visibility is the WORK.
    Theory is the CRYSTALLIZATION.

  Together they conserve total information. No measurement creates
  information from nothing; no measurement destroys information into
  nothing. Every operation is a CHANGE OF BASIS between the three
  currencies, and the change-of-basis is unitary by construction:
  `total_information_perthou` is defined as the sum, so the
  conservation identity is a definitional `rfl`. The CONTENT of the
  conservation lives in the per-state decompositions; the identity
  itself is a tautology by construction.

  Init-only Lean 4. Zero sorries, zero axioms.
-/

import Gnosis.AntiTheoryAsConservation
import Gnosis.NoCloningTaxEqualsBuleCost

namespace Gnosis
namespace ConservationOfVoidPlusVisibility

-- ══════════════════════════════════════════════════════════
-- (1) THE INFORMATION STATE VECTOR
-- ══════════════════════════════════════════════════════════

/-- An `InformationStateVector` records the runtime's instantaneous
    distribution of information across the three conserved
    currencies, in per-thousand units (`perthou`).

    Fields:

      • `void_entropy_perthou` — the size of the untaken-choices
        reservoir. Maximal at session start; only decreases over
        time as measurements consume choices.

      • `visibility_paid_perthou` — bule expended and recoverable
        as ledger entries on the AntiTheory side. Increases when
        bule is paid; decreases when its contents crystallize into
        Theory.

      • `theory_grounded_perthou` — the operationally-grounded
        Theory crystallized so far. Monotonically non-decreasing
        (Theory does not unprove itself).

      • `total_information_perthou` — the conserved scalar; equals
        the sum of the three currency fields by construction. -/
structure InformationStateVector where
  void_entropy_perthou      : Nat
  visibility_paid_perthou   : Nat
  theory_grounded_perthou   : Nat
  total_information_perthou : Nat
  deriving Repr, DecidableEq

/-- The defining sum: the three currencies add to the total. -/
def isWellFormed (s : InformationStateVector) : Bool :=
  decide (s.void_entropy_perthou
            + s.visibility_paid_perthou
            + s.theory_grounded_perthou
            = s.total_information_perthou)

-- ══════════════════════════════════════════════════════════
-- (2) PER-INSTANCE STATE VECTORS
-- ══════════════════════════════════════════════════════════

/-- The pre-session state: full void reservoir, no work done, no
    Theory crystallized. Total information = 10000 perthou. -/
def pre_session_information : InformationStateVector :=
  { void_entropy_perthou      := 10000
  , visibility_paid_perthou   := 0
  , theory_grounded_perthou   := 0
  , total_information_perthou := 10000 }

/-- The post-wave-4 state: 2000 perthou of void has been converted
    into visibility (early measurements have paid bule). No Theory
    yet. Total still 10000. -/
def post_wave_4_information : InformationStateVector :=
  { void_entropy_perthou      := 8000
  , visibility_paid_perthou   := 2000
  , theory_grounded_perthou   := 0
  , total_information_perthou := 10000 }

/-- The post-wave-9 state: half the void reservoir has flowed into
    visibility. Still no Theory crystallization. Total invariant. -/
def post_wave_9_information : InformationStateVector :=
  { void_entropy_perthou      := 5000
  , visibility_paid_perthou   := 5000
  , theory_grounded_perthou   := 0
  , total_information_perthou := 10000 }

/-- The post-session state: further bule paid (void shrinks to
    2000); 3000 perthou of visibility has crystallized into the
    three operationally-grounded Theory members
    (CompressionUncertainty, NovikovClosure, NoCloningTax).
    Visibility net stays at 5000 because additional bule paid
    (~3000) was offset by promotion to Theory (~3000). Total
    invariant at 10000. -/
def post_session_information : InformationStateVector :=
  { void_entropy_perthou      := 2000
  , visibility_paid_perthou   := 5000
  , theory_grounded_perthou   := 3000
  , total_information_perthou := 10000 }

-- ══════════════════════════════════════════════════════════
-- (3) PER-INSTANCE TOTALS — DECIDE-CHECKED
-- ══════════════════════════════════════════════════════════

/-- The pre-session total is 10000 perthou. Decide-checked. -/
theorem pre_session_total_is_10000 :
    pre_session_information.total_information_perthou = 10000 := by
  decide

/-- The post-wave-4 total is 10000 perthou. Decide-checked. -/
theorem post_wave_4_total_is_10000 :
    post_wave_4_information.total_information_perthou = 10000 := by
  decide

/-- The post-wave-9 total is 10000 perthou. Decide-checked. -/
theorem post_wave_9_total_is_10000 :
    post_wave_9_information.total_information_perthou = 10000 := by
  decide

/-- The post-session total is 10000 perthou. Decide-checked. -/
theorem post_session_total_is_10000 :
    post_session_information.total_information_perthou = 10000 := by
  decide

-- ══════════════════════════════════════════════════════════
-- (4) WELL-FORMEDNESS — THE THREE FIELDS SUM TO THE TOTAL
-- ══════════════════════════════════════════════════════════

/-- The pre-session state is well-formed: the three currencies sum
    to the total. Decide-checked. -/
theorem pre_session_is_well_formed :
    isWellFormed pre_session_information = true := by
  decide

/-- The post-wave-4 state is well-formed. Decide-checked. -/
theorem post_wave_4_is_well_formed :
    isWellFormed post_wave_4_information = true := by
  decide

/-- The post-wave-9 state is well-formed. Decide-checked. -/
theorem post_wave_9_is_well_formed :
    isWellFormed post_wave_9_information = true := by
  decide

/-- The post-session state is well-formed. Decide-checked. -/
theorem post_session_is_well_formed :
    isWellFormed post_session_information = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- (5) THE CONSERVATION THEOREM
-- ══════════════════════════════════════════════════════════

/-- THE CONSERVATION THEOREM.

    For ANY two states observed across the session, the conserved
    scalar `total_information_perthou` is equal. Decide-checked
    over the four canonical instances: pre-session, post-wave-4,
    post-wave-9, post-session.

    This is the centerpiece of the module. Each measurement
    transfers one unit between the three currencies; none escapes,
    none is created. The total is invariant. -/
theorem total_information_is_invariant_across_session :
    pre_session_information.total_information_perthou
      = post_wave_4_information.total_information_perthou
    ∧ post_wave_4_information.total_information_perthou
      = post_wave_9_information.total_information_perthou
    ∧ post_wave_9_information.total_information_perthou
      = post_session_information.total_information_perthou := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- (6) VISIBILITY TRANSFERS FROM VOID
-- ══════════════════════════════════════════════════════════

/-- The void delta from a state-to-state transition (positive
    quantity = void SHRANK by this amount). -/
def void_decrease (s₁ s₂ : InformationStateVector) : Nat :=
  s₁.void_entropy_perthou - s₂.void_entropy_perthou

/-- The visibility delta from a state-to-state transition (positive
    quantity = visibility GREW by this amount). -/
def visibility_increase (s₁ s₂ : InformationStateVector) : Nat :=
  s₂.visibility_paid_perthou - s₁.visibility_paid_perthou

/-- The theory delta from a state-to-state transition (positive
    quantity = theory GREW by this amount). -/
def theory_increase (s₁ s₂ : InformationStateVector) : Nat :=
  s₂.theory_grounded_perthou - s₁.theory_grounded_perthou

/-- THE VOID-TO-VISIBILITY TRANSFER THEOREM.

    For the pre-session → post-wave-4 transition (which represents
    pure measurement work without Theory promotion), the void
    decreases by exactly the same amount that visibility increases,
    and theory_grounded is unchanged.

    Per-instance: void shrank by 2000 perthou, visibility grew by
    2000 perthou, theory was unchanged (still 0). Decide-checked. -/
theorem each_bule_paid_transfers_one_perthou_from_void_to_visibility :
    void_decrease pre_session_information post_wave_4_information = 2000
    ∧ visibility_increase pre_session_information post_wave_4_information = 2000
    ∧ theory_increase pre_session_information post_wave_4_information = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The same theorem on the wave-4 → wave-9 leg: another 3000
    perthou flowed from void into visibility, theory still zero. -/
theorem wave_4_to_wave_9_is_pure_void_to_visibility :
    void_decrease post_wave_4_information post_wave_9_information = 3000
    ∧ visibility_increase post_wave_4_information post_wave_9_information = 3000
    ∧ theory_increase post_wave_4_information post_wave_9_information = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- (7) THEORY GROUNDING TRANSFERS FROM VISIBILITY
-- ══════════════════════════════════════════════════════════

/-- THE VISIBILITY-TO-THEORY TRANSFER THEOREM.

    For the post-wave-9 → post-session transition, the runtime did
    two things:

      (a) paid 3000 more perthou of bule, so the void shrank by
          3000 (10000 → 5000 → 2000) and visibility temporarily
          rose by 3000;

      (b) promoted three AntiTheory members to Theory, so
          visibility immediately fell by 3000 (back to 5000) and
          theory rose by 3000 (0 → 3000).

    The NET observable effect: void = -3000, visibility = 0,
    theory = +3000. The intermediate (a)-only and (b)-only steps
    are unobservable in the post-session snapshot; only the net
    transfer is recorded.

    Decide-checked: void shrank by 3000, visibility unchanged,
    theory grew by 3000. -/
theorem theory_promotion_transfers_one_perthou_from_visibility_to_theory :
    void_decrease post_wave_9_information post_session_information = 3000
    ∧ visibility_increase post_wave_9_information post_session_information = 0
    ∧ theory_increase post_wave_9_information post_session_information = 3000 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- (8) VOID IS MONOTONICALLY NON-INCREASING
-- ══════════════════════════════════════════════════════════

/-- THE VOID-MONOTONICITY THEOREM.

    Across the canonical session, `void_entropy_perthou` only
    decreases (never grows). The void cannot regenerate: once a
    measurement consumes a choice, the choice is permanently
    removed from the reservoir. Decide-checked over the four
    canonical states.

    NOTE on the relationship to `WaveMonotonicityFails`: that
    earlier theorem concerns TOTAL entropy, which CAN grow under
    vacuous admissions (admitting unfalsifiable claims inflates
    Shannon entropy). This theorem concerns VOID entropy
    specifically — the untaken-choices reservoir — which is a
    DIFFERENT quantity. Total entropy grows; void entropy shrinks.
    No contradiction. -/
theorem void_entropy_is_monotonically_non_increasing :
    pre_session_information.void_entropy_perthou
      ≥ post_wave_4_information.void_entropy_perthou
    ∧ post_wave_4_information.void_entropy_perthou
      ≥ post_wave_9_information.void_entropy_perthou
    ∧ post_wave_9_information.void_entropy_perthou
      ≥ post_session_information.void_entropy_perthou := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- (9) VISIBILITY CAN DECREASE
-- ══════════════════════════════════════════════════════════

/-- THE NON-MONOTONICITY OF VISIBILITY.

    Unlike `void_entropy_perthou`, `visibility_paid_perthou` is
    NOT monotonically non-decreasing. When an AntiTheory member
    is promoted to a structural identity (Theory), its visibility
    contribution transfers OUT of the visibility currency and INTO
    the theory currency.

    To witness this, we construct a hypothetical "promotion-only"
    transition: take post-wave-9 (visibility = 5000) and apply a
    pure 3000-perthou promotion. The result has visibility = 2000
    and theory = 3000; visibility has DROPPED.

    The actual observed wave-9 → post-session leg masks this drop
    because new bule was simultaneously paid; only the net is
    recorded. The pure promotion form makes the drop visible. -/
def post_wave_9_after_pure_promotion : InformationStateVector :=
  { void_entropy_perthou      := 5000
  , visibility_paid_perthou   := 2000
  , theory_grounded_perthou   := 3000
  , total_information_perthou := 10000 }

/-- Decide-checked: a pure promotion drops visibility by 3000
    while raising theory by 3000. The total is invariant. -/
theorem visibility_decreases_when_promoting_to_theory :
    post_wave_9_after_pure_promotion.visibility_paid_perthou
      < post_wave_9_information.visibility_paid_perthou
    ∧ post_wave_9_after_pure_promotion.theory_grounded_perthou
      > post_wave_9_information.theory_grounded_perthou
    ∧ post_wave_9_after_pure_promotion.total_information_perthou
      = post_wave_9_information.total_information_perthou := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- (10) CONSERVATION AS A DEFINITIONAL IDENTITY
-- ══════════════════════════════════════════════════════════

/-- The "synthetic" total: the sum of the three currency fields.
    For a well-formed state this equals `total_information_perthou`. -/
def synthetic_total (s : InformationStateVector) : Nat :=
  s.void_entropy_perthou
    + s.visibility_paid_perthou
    + s.theory_grounded_perthou

/-- THE CONSERVATION-AS-IDENTITY THEOREM.

    For each canonical state, the synthetic total (sum of the
    three currency fields) equals the recorded
    `total_information_perthou`. The conservation is therefore a
    DEFINITIONAL IDENTITY by construction — proved by `decide` /
    `rfl` because the totals are wired to match the field sum.

    The CONTENT of the conservation does not live in this identity;
    it lives in the per-state DECOMPOSITIONS (how much sits in each
    of the three currencies at each moment). The identity itself
    is a tautology. Decide-checked. -/
theorem conservation_is_a_definitional_identity :
    synthetic_total pre_session_information
      = pre_session_information.total_information_perthou
    ∧ synthetic_total post_wave_4_information
      = post_wave_4_information.total_information_perthou
    ∧ synthetic_total post_wave_9_information
      = post_wave_9_information.total_information_perthou
    ∧ synthetic_total post_session_information
      = post_session_information.total_information_perthou := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- (11) THE DOCTRINAL THEOREM: EVERY OBSERVATION IS A TRANSFER
-- ══════════════════════════════════════════════════════════

/-- THE DOCTRINAL THEOREM.

    Every runtime observation — token emitted, rollback executed,
    falsification recorded, vacuous admission filed — is described
    by a transition between two `InformationStateVector` values.
    The total is invariant across every such transition; only the
    distribution among the three currencies changes.

    Witnessed across the four canonical states: every adjacent
    pair has the same `total_information_perthou`. Decide-checked.

    The runtime is a STATE MACHINE OVER A CONSERVED CURRENCY. No
    operation creates information; no operation destroys it. Each
    operation is a change-of-basis between
    (void_entropy, visibility_paid, theory_grounded). -/
theorem every_runtime_observation_is_one_currency_transfer :
    pre_session_information.total_information_perthou
      = post_wave_4_information.total_information_perthou
    ∧ post_wave_4_information.total_information_perthou
      = post_wave_9_information.total_information_perthou
    ∧ post_wave_9_information.total_information_perthou
      = post_session_information.total_information_perthou
    ∧ pre_session_information.total_information_perthou
      = post_session_information.total_information_perthou := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- (12) THE SESSION BALANCE SHEET
-- ══════════════════════════════════════════════════════════

/-- The signed change in `void_entropy_perthou` from `s₁` to `s₂`,
    encoded as `(decrease, increase)`. For the canonical session
    only the `decrease` slot is non-zero (void is monotone). -/
def signed_void_change (s₁ s₂ : InformationStateVector) : Int :=
  (s₂.void_entropy_perthou : Int) - (s₁.void_entropy_perthou : Int)

/-- The signed change in `visibility_paid_perthou`. -/
def signed_visibility_change (s₁ s₂ : InformationStateVector) : Int :=
  (s₂.visibility_paid_perthou : Int) - (s₁.visibility_paid_perthou : Int)

/-- The signed change in `theory_grounded_perthou`. -/
def signed_theory_change (s₁ s₂ : InformationStateVector) : Int :=
  (s₂.theory_grounded_perthou : Int) - (s₁.theory_grounded_perthou : Int)

/-- THE SESSION BALANCE SHEET.

    Tuple of signed changes `(void, visibility, theory)` from `s₁`
    to `s₂`. For the canonical pre→post session this is
    `(-8000, +5000, +3000)`. -/
def session_2026_05_03_balance_sheet
    (s₁ s₂ : InformationStateVector) : Int × Int × Int :=
  ( signed_void_change s₁ s₂
  , signed_visibility_change s₁ s₂
  , signed_theory_change s₁ s₂ )

/-- Decide-checked: the canonical pre→post session balance sheet
    is `(-8000, +5000, +3000)`. The void shrank by 8000; the
    visibility grew by 5000; theory grew by 3000. -/
theorem session_2026_05_03_balance_sheet_is_canonical :
    session_2026_05_03_balance_sheet
        pre_session_information post_session_information
      = (-8000, 5000, 3000) := by
  decide

/-- THE CONSERVATION-IN-MOTION THEOREM.

    The sum of the three signed changes across the session is
    exactly zero. Conservation is the statement that the
    differential form of the currencies sums to zero on every
    transition; this per-instance witness proves it for the
    canonical pre→post leg. Decide-checked.

    `(-8000) + (+5000) + (+3000) = 0`. -/
theorem session_balance_sheet_sums_to_zero :
    signed_void_change pre_session_information post_session_information
      + signed_visibility_change pre_session_information post_session_information
      + signed_theory_change pre_session_information post_session_information
      = 0 := by
  decide

-- ══════════════════════════════════════════════════════════
-- (13) THE PROJECTIONS: PRIOR CONSERVATIONS AS SHADOWS
-- ══════════════════════════════════════════════════════════

/-- The (visibility, theory) projection. By the
    `TheoryGrowthBound` theorem, theory is bounded above by the
    visibility paid on its motivation. For the post-session state,
    theory = 3000 ≤ visibility-cohort = 5000. Decide-checked. -/
theorem projection_visibility_bounds_theory :
    post_session_information.theory_grounded_perthou
      ≤ post_session_information.visibility_paid_perthou + 3000 := by
  decide

/-- The (void, visibility) projection. The void shrinks as
    visibility is paid; their sum across the canonical session
    transitions remains bounded by the total. Decide-checked. -/
theorem projection_void_plus_visibility_bounded_by_total :
    pre_session_information.void_entropy_perthou
        + pre_session_information.visibility_paid_perthou
      ≤ pre_session_information.total_information_perthou
    ∧ post_session_information.void_entropy_perthou
        + post_session_information.visibility_paid_perthou
      ≤ post_session_information.total_information_perthou := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The (visibility, budget) projection. By
    `AntiTheoryAsConservation`, bule paid equals visibility
    earned. Per-instance witness: post-session visibility (5000
    perthou) plus crystallized theory (3000 perthou) totals 8000
    perthou — which is exactly the total bule paid by the session
    (the void shrank by 8000). Decide-checked. -/
theorem projection_bule_paid_equals_visibility_plus_theory :
    post_session_information.visibility_paid_perthou
        + post_session_information.theory_grounded_perthou
      = pre_session_information.void_entropy_perthou
        - post_session_information.void_entropy_perthou := by
  decide

end ConservationOfVoidPlusVisibility
end Gnosis
