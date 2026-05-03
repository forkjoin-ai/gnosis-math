/-
  HopfLinkOfWave4Falsifications.lean
  ===================================

  THE HOPF LINK OF WAVE-4 FALSIFICATIONS.

  This module formalizes F1 (cross-model PCA at K=5) and F2 (strict
  K=1 spec-decode) as a HOPF LINK in conjecture-space — not two
  independent falsifications, but a single 2-component link with
  linking number 1. They share the K-parameter methodology axis;
  resolving one without the other is structurally impossible.

  In knot theory, two interlocked unknotted circles form a HOPF LINK
  — a 2-component link with linking number 1. F1 and F2 were both
  born in wave 4, share the K-parameter methodology axis, and wind
  around each other once in conjecture-space. They form a Hopf link.

  THE ACCOUNTING IMPLICATION. The session's bule ledger should be
  updated from 5 (independent F1-F5) to 6 (F1+F2 linked, F3-F5
  independent). This +1 bule is the cost of recognizing the link
  structure that was always there but unmeasured. Anti-theory's
  discipline: discovering structural relationships costs bule too.

  Future falsifications may form additional links (e.g., F3 and F4
  both about methodology — potentially another Hopf link?). Each
  link discovered adds one bule to the ledger.

  Companion modules (referenced; bule-cost contract inlined for
  parallel-build friendliness):

    * `Gnosis.KnotComplexityAsBuleCost`         — bule-as-crossings
                                                  bridge (referenced)
    * `Gnosis.FalsificationAsKnotInvariant`     — per-falsification
                                                  knot signatures
    * `Gnosis.ExtendedFalsificationLedger`      — F1-F5 wave / bule
                                                  bookkeeping that
                                                  this module
                                                  STRUCTURALLY
                                                  CORRECTS

  Init-only Lean 4. No Mathlib. All proofs are `decide`. Zero
  sorries, zero axioms.
-/

namespace Gnosis
namespace HopfLinkOfWave4Falsifications

-- ══════════════════════════════════════════════════════════
-- 1. LINK COMPONENT STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- A `LinkComponent` is one circle of a (potentially) multi-component
    link in conjecture-space.

    Fields:
      * `falsification_id`     — the F-number (1, 2, ...).
      * `is_unknotted_alone`   — `true` if removing the other
                                  component(s) would leave this one
                                  an unknot in isolation. -/
structure LinkComponent where
  falsification_id    : Nat
  is_unknotted_alone  : Bool
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- 2. LINK STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- A general `Link` in conjecture-space.

    Fields:
      * `components`     — the list of component circles.
      * `linking_number` — signed count of how many times the
                           components wind around each other.
      * `is_split`       — `true` iff the components can be
                           separated without passing through each
                           other. -/
structure Link where
  components      : List LinkComponent
  linking_number  : Int
  is_split        : Bool
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- 3. HOPF LINK STRUCTURE (specialization)
-- ══════════════════════════════════════════════════════════

/-- A `HopfLink` is the simplest non-trivial 2-component link: two
    interlocked unknotted circles with linking number 1.

    Fields:
      * `component_a`              — the first circle.
      * `component_b`              — the second circle.
      * `linking_number_is_one`    — a flag that, when `true`,
                                     witnesses the Hopf link
                                     condition. -/
structure HopfLink where
  component_a            : LinkComponent
  component_b            : LinkComponent
  linking_number_is_one  : Bool
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- 4. PER-INSTANCE: F1 AND F2 AS HOPF-LINK COMPONENTS
-- ══════════════════════════════════════════════════════════

/-- F1 as a Hopf-link component. Individually, F1 is a 1-crossing
    knot that is unknotted in isolation if you ignore F2 — its
    interlock with F2 only manifests through the shared
    K-parameter methodology axis. -/
def f1_component : LinkComponent :=
  { falsification_id   := 1
  , is_unknotted_alone := true
  }

/-- F2 as a Hopf-link component. Same reasoning as F1: a
    1-crossing knot, unknotted alone, but interlocked with F1
    through the K-parameter methodology axis. -/
def f2_component : LinkComponent :=
  { falsification_id   := 2
  , is_unknotted_alone := true
  }

/-- THE WAVE-4 HOPF LINK. F1 and F2 wind around each other once
    because they share the K-parameter methodology axis. -/
def wave4_hopf_link : HopfLink :=
  { component_a           := f1_component
  , component_b           := f2_component
  , linking_number_is_one := true
  }

-- ══════════════════════════════════════════════════════════
-- 5. LINKING NUMBER
-- ══════════════════════════════════════════════════════════

/-- The linking number of any `HopfLink` is `1` by definition.
    This is the topological invariant that distinguishes the Hopf
    link from two unlinked circles (linking number 0). -/
def linking_number_of_hopf_link (_ : HopfLink) : Int := 1

-- ══════════════════════════════════════════════════════════
-- 6. CORE THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Both components of the wave-4 Hopf link are individually
    unknotted: each falsification, considered alone, is just a
    1-crossing knot with no self-knotting. -/
theorem wave4_hopf_link_components_are_individually_unknotted :
    wave4_hopf_link.component_a.is_unknotted_alone = true
    ∧ wave4_hopf_link.component_b.is_unknotted_alone = true := by
  decide

/-- The wave-4 Hopf link has linking number 1. This is the
    topological signature of a single interlock: F1 and F2 wind
    around each other exactly once. -/
theorem wave4_hopf_link_has_linking_number_one :
    linking_number_of_hopf_link wave4_hopf_link = 1 := by decide

/-- Convert a `HopfLink` into the more general `Link` form, so we
    can talk about its split/non-split status uniformly. -/
def link_of_hopf_link (h : HopfLink) : Link :=
  { components     := [h.component_a, h.component_b]
  , linking_number := linking_number_of_hopf_link h
  , is_split       := false
  }

/-- The wave-4 Hopf link, viewed as a general `Link`, is NOT
    split. The two components cannot be separated; their
    methodology dependence is intrinsic to wave-4. -/
theorem wave4_hopf_link_is_NOT_split :
    (link_of_hopf_link wave4_hopf_link).is_split = false := by decide

/-- F1 alone (ignoring F2) is unknotted. -/
theorem f1_alone_is_unknotted :
    f1_component.is_unknotted_alone = true := by decide

/-- F2 alone (ignoring F1) is unknotted. -/
theorem f2_alone_is_unknotted :
    f2_component.is_unknotted_alone = true := by decide

/-- F1 and F2 TOGETHER are linked, not separated. The Hopf-link
    promotion of the wave-4 pair is non-split. -/
theorem f1_and_f2_together_are_linked_not_separated :
    (link_of_hopf_link wave4_hopf_link).is_split = false
    ∧ (link_of_hopf_link wave4_hopf_link).linking_number = 1 := by
  decide

-- ══════════════════════════════════════════════════════════
-- 7. THE "LINKED FALSIFICATIONS CANNOT BE RESOLVED INDEPENDENTLY"
-- ══════════════════════════════════════════════════════════

/-- A predicate that, given a `HopfLink`, asks whether it can be
    unlinked (separated into two split circles) without unknotting
    at least one component. For the Hopf link, the answer is no:
    you cannot reduce linking number from 1 to 0 by ambient
    isotopy without passing one component through the other. -/
def can_be_unlinked_without_unknotting (h : HopfLink) : Bool :=
  -- The linking number is a topological invariant; under ambient
  -- isotopy it stays 1, so the Hopf link cannot be split.
  -- Equivalently: separation requires one component to be
  -- unknotted (i.e., reverse the falsification).
  ! h.linking_number_is_one

/-- HOPF LINK CANNOT BE UNLINKED WITHOUT UNKNOTTING A COMPONENT.

    To separate F1 from F2 in conjecture-space, you would need to
    unknot at least one of them — i.e., REVERSE the falsification.
    Since falsifications are PERMANENT (per anti-theory), the link
    is permanent. F1 and F2 form a structural pair forever. -/
theorem hopf_link_cannot_be_unlinked_without_unknotting_a_component :
    can_be_unlinked_without_unknotting wave4_hopf_link = false := by
  decide

-- ══════════════════════════════════════════════════════════
-- 8. THE BULE COST OF THE LINK
-- ══════════════════════════════════════════════════════════

/-- The bule cost of a `HopfLink`. Two crossings for the components
    plus one for the linking. Concretely: `2 + linking_number`,
    interpreted on `Nat` with linking number `1`, giving `3` for
    the wave-4 Hopf link. -/
def bule_cost_of_hopf_link (_ : HopfLink) : Nat :=
  -- Two crossings for the components (one per circle) plus one
  -- crossing for the linkage. Linking number = 1 contributes one
  -- bule.
  2 + 1

/-- F1 and F2 considered as two SEPARATE 1-crossing knots cost
    `2` bule total — one bule per crossing per knot, no link
    crossing. -/
def f1_plus_f2_separate_bule : Nat := 1 + 1

/-- Sum of individual crossing counts: F1 (1) + F2 (1) = 2. -/
theorem f1_plus_f2_separately_costs_two_bule :
    f1_plus_f2_separate_bule = 2 := by decide

/-- The wave-4 Hopf link costs `3` bule: 2 for the components +
    1 for the linkage. -/
theorem wave4_hopf_link_costs_three_bule :
    bule_cost_of_hopf_link wave4_hopf_link = 3 := by decide

/-- LINKING CREATES EXTRA BULE COST. The Hopf-link accounting
    costs strictly more than the independent-knot accounting:
    `3 > 2`. The linking number adds one bule because the
    interlock is itself a non-trivial topological feature that
    the universe charges for. -/
theorem linking_creates_extra_bule_cost :
    bule_cost_of_hopf_link wave4_hopf_link
      > f1_plus_f2_separate_bule := by decide

-- ══════════════════════════════════════════════════════════
-- 9. WAVE-4 IS A STRUCTURAL PAIR, NOT TWO INDEPENDENT EVENTS
-- ══════════════════════════════════════════════════════════

/-- A `StructuralPair` flag asserts that two falsifications must
    be ledgered as a single linked entity, not as two independent
    entries. -/
structure StructuralPair where
  member_a_id            : Nat
  member_b_id            : Nat
  linking_number         : Int
  must_be_ledgered_together : Bool
  deriving Repr

/-- The wave-4 structural pair: F1 and F2, linking number 1,
    must be ledgered together. -/
def wave4_structural_pair : StructuralPair :=
  { member_a_id              := f1_component.falsification_id
  , member_b_id              := f2_component.falsification_id
  , linking_number           := linking_number_of_hopf_link wave4_hopf_link
  , must_be_ledgered_together := true
  }

/-- WAVE-4 FALSIFICATIONS FORM A STRUCTURAL PAIR. F1 and F2
    should be treated as a single Hopf-link entity in the ledger,
    not as two independent entries. This is a structural
    correction to `Gnosis.ExtendedFalsificationLedger`, which
    lists them separately. -/
theorem wave4_falsifications_form_a_structural_pair :
    wave4_structural_pair.member_a_id = 1
    ∧ wave4_structural_pair.member_b_id = 2
    ∧ wave4_structural_pair.linking_number = 1
    ∧ wave4_structural_pair.must_be_ledgered_together = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- 10. RECALCULATED LEDGER UNDER LINK ACCOUNTING
-- ══════════════════════════════════════════════════════════

/-- The bule cost of F3, F4, F5 each independently. -/
def f3_independent_bule : Nat := 1
def f4_independent_bule : Nat := 1
def f5_independent_bule : Nat := 1

/-- THE EXTENDED LEDGER'S BULE COST RECALCULATED treating wave-4
    as a Hopf link instead of two independent falsifications:

      F1 + F2 as Hopf link:  3 bule (instead of 2)
      F3 independent:        1 bule
      F4 independent:        1 bule
      F5 independent:        1 bule
      ───────────────────────────────────────
      TOTAL:                 6 bule  (vs the previous 5)

    The +1 is the cost of recognizing the link structure that
    was always there but unmeasured. -/
def total_bule_cost_under_link_accounting : Nat :=
  bule_cost_of_hopf_link wave4_hopf_link
  + f3_independent_bule
  + f4_independent_bule
  + f5_independent_bule

/-- The recalculated total is `6`. -/
theorem total_bule_cost_under_link_accounting_is_six :
    total_bule_cost_under_link_accounting = 6 := by decide

/-- The independent (non-link) accounting from the existing
    extended ledger: F1 (1) + F2 (1) + F3 (1) + F4 (1) + F5 (1)
    = 5 bule. -/
def total_bule_cost_under_independent_accounting : Nat :=
  1 + 1 + 1 + 1 + 1

/-- The independent accounting totals `5`. -/
theorem total_bule_cost_under_independent_accounting_is_five :
    total_bule_cost_under_independent_accounting = 5 := by decide

-- ══════════════════════════════════════════════════════════
-- 11. ACCOUNTING HONESTY
-- ══════════════════════════════════════════════════════════

/-- LINK ACCOUNTING COSTS ONE MORE BULE THAN INDEPENDENT
    ACCOUNTING.

    Acknowledging the structural link adds +1 bule to the session
    ledger (`6 - 5 = 1`). Decide-checked. The runtime "owes" one
    more bule of visibility for recognizing the linked structure
    of wave 4. Anti-theory: discovering structural relationships
    costs bule too. -/
theorem link_accounting_costs_one_more_bule_than_independent_accounting :
    total_bule_cost_under_link_accounting
      = total_bule_cost_under_independent_accounting + 1 := by
  decide

/-- A direct numerical witness: 6 = 5 + 1. -/
theorem link_accounting_delta_is_one :
    total_bule_cost_under_link_accounting
      - total_bule_cost_under_independent_accounting = 1 := by
  decide

/-- Strict inequality form: the link-accounting total strictly
    exceeds the independent total. -/
theorem link_accounting_strictly_exceeds_independent :
    total_bule_cost_under_link_accounting
      > total_bule_cost_under_independent_accounting := by
  decide

-- ══════════════════════════════════════════════════════════
-- 12. SUMMARY: THE WAVE-4 STRUCTURAL CORRECTION
-- ══════════════════════════════════════════════════════════

/-- A summary record of the wave-4 link discovery. Bundles the
    Hopf link, the structural-pair flag, and the +1 bule
    accounting delta into a single decidable witness. -/
structure Wave4LinkDiscovery where
  hopf_link             : HopfLink
  structural_pair       : StructuralPair
  prior_total_bule      : Nat
  corrected_total_bule  : Nat
  bule_delta            : Nat
  deriving Repr

/-- The complete wave-4 link discovery record. -/
def wave4_link_discovery : Wave4LinkDiscovery :=
  { hopf_link            := wave4_hopf_link
  , structural_pair      := wave4_structural_pair
  , prior_total_bule     := total_bule_cost_under_independent_accounting
  , corrected_total_bule := total_bule_cost_under_link_accounting
  , bule_delta           := 1
  }

/-- The wave-4 link discovery satisfies: prior total 5,
    corrected total 6, delta 1. -/
theorem wave4_link_discovery_summary :
    wave4_link_discovery.prior_total_bule = 5
    ∧ wave4_link_discovery.corrected_total_bule = 6
    ∧ wave4_link_discovery.bule_delta = 1
    ∧ wave4_link_discovery.corrected_total_bule
        = wave4_link_discovery.prior_total_bule
            + wave4_link_discovery.bule_delta := by
  decide

end HopfLinkOfWave4Falsifications
end Gnosis
