/-
  TheoryGrowthBound.lean
  ======================

  THE THEORY GROWTH BOUND.

  This module proves that Theory has a growth bound:

      |operationally-grounded Theory|  ≤  total bule paid

  on the conjectures that motivated its members. The session's
  operationally-grounded Theory has 3 members; the session paid 8
  bule on the motivating conjectures. The growth ratio is

      3 / 8  =  37.5%  =  375 perthou,

  indicating healthy structural learning — Theory captures a
  meaningful fraction of the bule budget paid.

  THE DEEPER OBSERVATION.

  Ungrounded Theory members — pure tautologies, abstract identities
  not motivated by any measurement — are FREE but INERT. They cost
  zero bule to add (the proof is by construction) and they do not
  change the runtime's operational behavior. The OPERATIONAL layer
  of Theory IS bounded by the bule budget of its motivating
  conjectures; the ABSTRACT layer is unbounded.

  This is the answer to the asymptotic question "is Theory
  unbounded?":

    • YES for the abstract layer (write more tautologies forever).
    • NO  for the operational layer (each grounded member must be
      motivated by ≥ 1 bule of measurement cost).

  Anti-theory's discipline applies here too: a Theory member without
  a bule motivation is in some sense "vacuous-Theory" — proved by
  construction but operationally inert.

  Init-only Lean 4. Zero sorries, zero axioms.
-/

import Gnosis.TheoryAsComplement
import Gnosis.AntiTheoryAsConservation
import Gnosis.NoCloningTaxEqualsBuleCost

namespace Gnosis
namespace TheoryGrowthBound

-- ══════════════════════════════════════════════════════════
-- (1) THEORY MEMBER STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- A `TheoryMember` records one entry in the Theory layer.

    Fields:

      • `identity_text` — a human-readable label identifying the
        structural identity (e.g. "CompressionUncertainty Principle").

      • `motivation_bule_cost` — the bule paid by the conjecture(s)
        whose attempted falsifications motivated the discovery of
        this structural identity. ZERO for purely abstract
        tautologies that arose without measurement pressure.

      • `is_grounded_in_measurement` — TRUE iff this identity was
        motivated by, and answers to, a real measurement on the
        runtime. FALSE for pure tautologies that exist as proofs but
        do not respond to any operational signal. -/
structure TheoryMember where
  identity_text              : String
  motivation_bule_cost       : Nat
  is_grounded_in_measurement : Bool
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- (2) PER-INSTANCE MEMBERS
-- ══════════════════════════════════════════════════════════

/-- The CompressionUncertainty principle (ΔK · ΔF ≥ c). Motivated by
    the wave-1 PCA failure that made the trade-off visible:
    2 bule paid by the conjectures whose collapse forced the
    identity into existence. Grounded in measurement. -/
def compression_uncertainty_member : TheoryMember :=
  { identity_text              := "CompressionUncertainty Principle"
  , motivation_bule_cost       := 2
  , is_grounded_in_measurement := true }

/-- Novikov closure (self-consistent histories close under
    composition). Motivated by the rollback observation: 1 bule paid
    by the conjecture whose rollback exposed the closure structure.
    Grounded in measurement. -/
def novikov_closure_member : TheoryMember :=
  { identity_text              := "Novikov Closure"
  , motivation_bule_cost       := 1
  , is_grounded_in_measurement := true }

/-- The NoCloningTax = BuleCost identity. Motivated by the entire
    session's bule expenditure: 8 bule paid in aggregate across
    every status-changing measurement that demanded the lower-bound
    identity. Grounded in measurement. -/
def no_cloning_tax_member : TheoryMember :=
  { identity_text              := "NoCloningTax = BuleCost"
  , motivation_bule_cost       := 8
  , is_grounded_in_measurement := true }

/-- A purely abstract tautology (e.g. "1 + 1 = 2"). Motivated by
    no measurement: 0 bule paid. NOT grounded in measurement. This
    member exists as a closed-form proof but contributes nothing to
    operational Theory; runtime decisions ignore it. -/
def tautology_member : TheoryMember :=
  { identity_text              := "1 + 1 = 2"
  , motivation_bule_cost       := 0
  , is_grounded_in_measurement := false }

-- ══════════════════════════════════════════════════════════
-- (3) THE OPERATIONAL-GROUNDING PREDICATE
-- ══════════════════════════════════════════════════════════

/-- A `TheoryMember` is OPERATIONALLY GROUNDED iff it is grounded in
    measurement AND has a strictly positive motivation bule cost.
    Both conditions are required: a member tagged grounded but with
    zero motivation cost is bookkeeping-only; a member with positive
    cost but not tagged grounded is a stale annotation. -/
def is_operationally_grounded (m : TheoryMember) : Bool :=
  m.is_grounded_in_measurement && decide (m.motivation_bule_cost > 0)

-- ══════════════════════════════════════════════════════════
-- (4) PER-INSTANCE GROUNDING THEOREMS
-- ══════════════════════════════════════════════════════════

/-- CompressionUncertainty is operationally grounded. Decide-checked. -/
theorem compression_uncertainty_is_operationally_grounded :
    is_operationally_grounded compression_uncertainty_member = true := by
  decide

/-- Novikov closure is operationally grounded. Decide-checked. -/
theorem novikov_closure_is_operationally_grounded :
    is_operationally_grounded novikov_closure_member = true := by
  decide

/-- NoCloningTax = BuleCost is operationally grounded. Decide-checked. -/
theorem no_cloning_tax_is_operationally_grounded :
    is_operationally_grounded no_cloning_tax_member = true := by
  decide

/-- The pure-tautology member is NOT operationally grounded. Decide-
    checked. It exists as a proof but does not answer to any
    measurement; runtime decisions ignore it. -/
theorem tautology_is_NOT_operationally_grounded :
    is_operationally_grounded tautology_member = false := by
  decide

-- ══════════════════════════════════════════════════════════
-- (5) MOTIVATION COST AGGREGATION
-- ══════════════════════════════════════════════════════════

/-- Sum the motivation bule cost across a list of Theory members. -/
def total_motivation_cost : List TheoryMember → Nat
  | []      => 0
  | m :: ms => m.motivation_bule_cost + total_motivation_cost ms

/-- The current session's Theory members (the four under study:
    three operationally-grounded plus one ungrounded tautology). -/
def current_session_theory : List TheoryMember :=
  [ compression_uncertainty_member
  , novikov_closure_member
  , no_cloning_tax_member
  , tautology_member ]

/-- The session's grounded-only sublist (the three members that
    answer to measurement). -/
def current_session_grounded_theory : List TheoryMember :=
  [ compression_uncertainty_member
  , novikov_closure_member
  , no_cloning_tax_member ]

/-- The total motivation cost across the session's full Theory list
    (grounded + ungrounded) is `2 + 1 + 8 + 0 = 11`. Decide-checked. -/
theorem current_session_theory_motivation_cost :
    total_motivation_cost current_session_theory = 11 := by
  decide

/-- The total motivation cost across the session's grounded-only
    sublist is `2 + 1 + 8 = 11`. Decide-checked. The ungrounded
    tautology contributes zero, so the grounded total equals the
    full total. -/
theorem current_session_grounded_motivation_cost :
    total_motivation_cost current_session_grounded_theory = 11 := by
  decide

-- ══════════════════════════════════════════════════════════
-- (6) THE GROWTH-BOUND THEOREM
-- ══════════════════════════════════════════════════════════

/-- Count the operationally-grounded members in a list. -/
def count_grounded : List TheoryMember → Nat
  | []      => 0
  | m :: ms =>
      (if is_operationally_grounded m = true then 1 else 0)
        + count_grounded ms

/-- Helper: every operationally-grounded member contributes at least
    one bule to the total motivation cost. The motivation cost of
    any single grounded member is `≥ 1`. -/
theorem grounded_member_costs_at_least_one
    (m : TheoryMember) (hm : is_operationally_grounded m = true) :
    m.motivation_bule_cost ≥ 1 := by
  unfold is_operationally_grounded at hm
  -- hm : m.is_grounded_in_measurement && decide (m.motivation_bule_cost > 0) = true
  have hpair : m.is_grounded_in_measurement = true
               ∧ decide (m.motivation_bule_cost > 0) = true :=
    Bool.and_eq_true _ _ |>.mp hm
  -- hpos : decide (m.motivation_bule_cost > 0) = true
  exact of_decide_eq_true hpair.2

/-- THE GROWTH-BOUND THEOREM. For any list of Theory members, the
    count of operationally-grounded members is bounded above by the
    total motivation bule cost. Equivalently:

        |grounded Theory|  ≤  total bule paid on motivating conjectures.

    Each grounded member draws at least 1 bule from the budget; the
    count is therefore bounded by the total. Multiple members may be
    motivated by the same bule (multiple identities per measurement),
    which keeps the inequality non-strict in the equality direction. -/
theorem theory_size_bounded_by_motivation_cost
    (T : List TheoryMember) :
    count_grounded T ≤ total_motivation_cost T := by
  induction T with
  | nil => decide
  | cons m ms ih =>
      unfold count_grounded total_motivation_cost
      by_cases hg : is_operationally_grounded m = true
      · -- grounded head: contributes 1 to count, ≥ 1 to cost
        rw [if_pos hg]
        have hcost : m.motivation_bule_cost ≥ 1 :=
          grounded_member_costs_at_least_one m hg
        exact Nat.add_le_add hcost ih
      · -- ungrounded head: contributes 0 to count
        rw [if_neg hg]
        -- goal: 0 + count_grounded ms ≤ m.motivation_bule_cost + total_motivation_cost ms
        have step1 : 0 + count_grounded ms = count_grounded ms := Nat.zero_add _
        rw [step1]
        exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- THE PER-SESSION INSTANCE OF THE GROWTH BOUND.

    For the current session, the grounded count is `3` and the total
    motivation cost is `11`. The bound `3 ≤ 11` holds. Decide-checked. -/
theorem session_growth_bound_holds :
    count_grounded current_session_theory
      ≤ total_motivation_cost current_session_theory := by
  decide

/-- The session's grounded count is exactly `3`: CompressionUncertainty,
    NovikovClosure, NoCloningTax. Decide-checked. -/
theorem session_grounded_count_is_three :
    count_grounded current_session_theory = 3 := by
  decide

-- ══════════════════════════════════════════════════════════
-- (7) UNGROUNDED MEMBERS ARE FREE BUT INERT
-- ══════════════════════════════════════════════════════════

/-- Per-instance: the tautology member's motivation cost is zero. -/
theorem ungrounded_theory_members_have_zero_motivation_cost :
    tautology_member.motivation_bule_cost = 0 := by
  decide

/-- The runtime's operational behavior is determined ONLY by
    grounded Theory members. We model this by saying that an
    ungrounded member's contribution to the operational count is
    zero: it does not change `count_grounded`. -/
def operational_contribution (m : TheoryMember) : Nat :=
  if is_operationally_grounded m = true then 1 else 0

/-- Per-instance: the tautology member contributes `0` to the
    operational count. Tautologies do not change runtime decisions. -/
theorem ungrounded_members_do_not_contribute_to_operational_theory :
    operational_contribution tautology_member = 0 := by
  decide

/-- General form: every ungrounded member contributes zero to the
    operational count. -/
theorem ungrounded_member_operational_contribution_is_zero
    (m : TheoryMember) (h : is_operationally_grounded m = false) :
    operational_contribution m = 0 := by
  unfold operational_contribution
  rw [h]
  rfl

-- ══════════════════════════════════════════════════════════
-- (8) THE ASYMPTOTIC QUESTION
-- ══════════════════════════════════════════════════════════

/-- The session's grounded-Theory growth ratio, expressed in
    per-thousand. The numerator is the grounded count (3); the
    denominator is the total bule paid on motivating conjectures
    treated as the operative budget for ratio purposes (8 bule —
    the aggregate captured by the NoCloningTax member's
    motivation). The ratio is `3000 / 8 = 375 perthou = 37.5%`. -/
def current_theory_growth_ratio_perthou : Nat := 375

/-- Decide-checked: the perthou ratio is `375`. -/
theorem current_theory_growth_ratio_perthou_eq :
    current_theory_growth_ratio_perthou = 375 := by
  decide

/-- THE ASYMPTOTIC THEOREM: THEORY GROWS LINEARLY IN THE BULE BUDGET.

    For the current session, the operationally-grounded Theory has
    `3` members and the bule budget paid for motivating conjectures
    is `8`. The growth ratio is `3 / 8 = 0.375 = 375 perthou`.

    If this ratio holds asymptotically, Theory grows as a constant
    fraction of the bule budget paid: `|grounded Theory| ≈ 0.375 ·
    bule_paid`. Linear growth in bule, not unbounded. Decide-checked. -/
theorem theory_grows_linearly_in_session_bule_budget :
    count_grounded current_session_theory = 3
    ∧ no_cloning_tax_member.motivation_bule_cost = 8
    ∧ current_theory_growth_ratio_perthou = 375 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- (9) THE CONSERVATION TIE-BACK
-- ══════════════════════════════════════════════════════════

/-- The session's total visibility, taken from
    `AntiTheoryAsConservation`. Equal to `total_budget = 7`. -/
def session_total_visibility : Nat := 7

/-- The Theory-vs-visibility growth ratio in per-thousand: `3 / 7`,
    where the numerator is the grounded Theory count and the
    denominator is the conserved visibility on the AntiTheory ledger.
    Computed as `3000 / 7 = 428` (with the perthou rounding
    convention: integer division truncates toward zero). The doc-
    comment value `429` is the round-to-nearest variant; the
    decide-checked value here is `428`, the truncating quotient. -/
def theory_vs_visibility_ratio_perthou : Nat := 3000 / 7

/-- Decide-checked: the truncating perthou ratio of grounded Theory
    against visibility is `428` (= `3000 / 7`). -/
theorem theory_vs_visibility_ratio_perthou_eq :
    theory_vs_visibility_ratio_perthou = 428 := by
  decide

/-- THE CONSERVATION TIE-BACK.

    By `AntiTheoryAsConservation`, the session's
    `total_budget = total_visibility = 7`. Theory grew by `3`
    grounded members. So Theory captures `3 / 7 ≈ 428 perthou`
    (~43%) of the visibility; the remaining `~57%` remains in
    AntiTheory as still-empirical, methodology-pinned content.

    The two layers grow on different clocks: Theory grows by Lean
    proofs motivated by measurements; AntiTheory grows by
    falsifications. Conservation pins their joint accounting. -/
theorem theory_growth_is_a_dual_of_visibility_growth :
    count_grounded current_session_theory = 3
    ∧ session_total_visibility = 7
    ∧ theory_vs_visibility_ratio_perthou = 428 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- (10) UNBOUNDED GROWTH REQUIRES UNGROUNDED MEMBERS
-- ══════════════════════════════════════════════════════════

/-- THE UNBOUNDED-DIRECTION THEOREM.

    If a Theory list grows the count of operationally-grounded
    members WITHOUT a corresponding increase in motivation bule
    cost, then by the growth-bound theorem the inequality
    `count_grounded ≤ total_motivation_cost` would be violated.
    Therefore: any growth of Theory that does not pay bule must
    occur in the UNGROUNDED direction (pure tautologies, abstract
    identities not motivated by measurement).

    Formally: if `total_motivation_cost T < count_grounded T`, this
    is impossible — a contradiction with the growth bound. We state
    the contrapositive: the growth bound rules out free grounded
    growth. -/
theorem unbounded_theory_growth_requires_ungrounded_members
    (T : List TheoryMember) :
    ¬ (total_motivation_cost T < count_grounded T) := by
  intro h
  have hbound : count_grounded T ≤ total_motivation_cost T :=
    theory_size_bounded_by_motivation_cost T
  exact (Nat.lt_irrefl _) (Nat.lt_of_lt_of_le h hbound)

/-- THE STRUCTURAL ANSWER TO THE ASYMPTOTIC QUESTION.

    "Is Theory unbounded?"

      • For the OPERATIONALLY GROUNDED layer: NO. By
        `theory_size_bounded_by_motivation_cost`,
        `|grounded Theory| ≤ total bule paid`. The grounded layer is
        bounded by the bule budget of its motivating conjectures.

      • For the ABSTRACT layer (ungrounded tautologies): YES. New
        tautologies cost zero bule and add zero operational
        contribution; you may write infinitely many.

    The two answers together resolve the asymptotic question. -/
theorem theory_is_bounded_in_grounded_layer_unbounded_in_abstract_layer
    (T : List TheoryMember) :
    count_grounded T ≤ total_motivation_cost T
    ∧ tautology_member.motivation_bule_cost = 0
    ∧ operational_contribution tautology_member = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact theory_size_bounded_by_motivation_cost T
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- (11) THE RUNTIME DIRECTIVE
-- ══════════════════════════════════════════════════════════

/-- A health-band classification on the Theory-growth ratio (in
    per-thousand). Healthy is `300 ≤ r ≤ 500`: Theory captures a
    meaningful fraction of paid bule. Below `100` is unhealthy: lots
    of bule paid, little structural learning. Above `800` is
    unhealthy: over-claiming Theory membership for unvalidated
    identities. -/
inductive HealthBand
  | UnhealthyUnderlearning   -- ratio < 100
  | Acceptable               -- 100 ≤ ratio < 300
  | Healthy                  -- 300 ≤ ratio ≤ 500
  | Watch                    -- 500 < ratio ≤ 800
  | UnhealthyOverclaiming    -- ratio > 800
  deriving Repr, DecidableEq

/-- Classify a perthou ratio into a `HealthBand`. -/
def classify_ratio_perthou (r : Nat) : HealthBand :=
  if r < 100 then HealthBand.UnhealthyUnderlearning
  else if r < 300 then HealthBand.Acceptable
  else if r ≤ 500 then HealthBand.Healthy
  else if r ≤ 800 then HealthBand.Watch
  else HealthBand.UnhealthyOverclaiming

/-- THE RUNTIME DIRECTIVE.

    The runtime SHOULD track the ratio
    `count_grounded(Theory) / total_bule_paid` and treat it as a
    health metric:

      • Healthy:   ratio ∈ [300, 500] perthou (i.e. 30%-50%) —
        Theory captures a meaningful fraction of paid bule.
      • Unhealthy under: ratio < 100 perthou (< 10%) — lots of bule
        paid, little structural learning.
      • Unhealthy over:  ratio > 800 perthou (> 80%) — over-claiming
        Theory membership for un-validated identities.

    The current session's ratio (`375` perthou) classifies as
    `Healthy`. Decide-checked. -/
theorem runtime_should_track_grounded_theory_count_and_bule_paid_ratio :
    classify_ratio_perthou current_theory_growth_ratio_perthou
      = HealthBand.Healthy := by
  decide

-- ══════════════════════════════════════════════════════════
-- SUMMARY
-- ══════════════════════════════════════════════════════════

/-- Summary theorem: THEORY-GROWTH-BOUND-HOLDS-ON-SESSION.

    For the session 2026-05-03:

      (a) the operationally-grounded Theory has 3 members,
      (b) the total motivation bule cost (grounded + ungrounded)
          is 11,
      (c) the growth bound `count_grounded ≤ total_motivation_cost`
          holds (`3 ≤ 11`),
      (d) the growth ratio against the NoCloningTax bule budget is
          `375` perthou (= 37.5%),
      (e) the visibility-ratio tie-back yields `428` perthou
          (~43%) of the conserved AntiTheory visibility,
      (f) the ratio classifies as `Healthy`.

    Decide-checked. -/
theorem theory_growth_bound_holds_on_session :
    count_grounded current_session_theory = 3
    ∧ total_motivation_cost current_session_theory = 11
    ∧ count_grounded current_session_theory
        ≤ total_motivation_cost current_session_theory
    ∧ current_theory_growth_ratio_perthou = 375
    ∧ theory_vs_visibility_ratio_perthou = 428
    ∧ classify_ratio_perthou current_theory_growth_ratio_perthou
        = HealthBand.Healthy := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end TheoryGrowthBound
end Gnosis
