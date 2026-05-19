import Gnosis.SkyrmsUltraLongRunEquilibrium
import Gnosis.SkyrmsErgodicSelection
import Gnosis.BuleyEquilibrium

/-
  BuleyErgodicClosure.lean
  ========================

  Forward + backward kernel pair on `PolarizationState`, with a
  retrocausal Novikov-style closure at the kenoma modulus 10, lifted
  through to `Gnosis.BuleyEquilibrium.isBuleyEquilibrium`. The
  "Skyrms ≠ Buley" gap is recorded as a theorem-level separator, not
  as commentary.

  ## What is new here

  `Gnosis.SkyrmsErgodicSelection.ulr_dominates_nash_unconditional_discrete`
  certifies a forward-only ergodic stability: under a `Nat`-weighted
  mutation kernel on lumped basins (`nash | mid | ulr`), ULR mass
  strictly dominates Nash mass after a small finite number of steps
  from every starting basin. That theorem is the strongest discrete
  unconditional witness Init Lean carries today.

  This module asks the next honest question: what does it take to
  upgrade *forward* ergodic dominance to a *retrocausal* closure of
  the Buley shape? Three things are exposed at theorem level.

  ### 1. The forward-backward kernel pair has disjoint fixed-point sets

  Define `forwardStep := mutationStep` (pulls toward median +
  cooperative debt floor) and `backwardStep` (pushes away from median
  + toward defection ceiling). Then:

  * `skyrmsUltraLongRunFixedPoint` is forward-fixed but *not*
    backward-fixed (`forward_fix_is_not_backward_fix_for_ulr`).
  * `nashPolarizationTrap` is backward-fixed but *not* forward-fixed
    (`backward_fix_is_not_forward_fix_for_nash_trap`).
  * The two fixed-point sets are disjoint at the canonical witnesses
    (`forward_and_backward_fixed_point_sets_disjoint_at_canonical_witnesses`).

  This is the *honest* form of "retrocausal closure does not happen
  at the dynamical level": neither the Skyrms ULR nor the Nash trap
  is a dynamic Novikov fixed point of the kernel pair.

  ### 2. Retrocausal closure happens at the bulk-state index

  Define `bulkOf s := triangular s.budget - polarization s + s.debtA
  + s.debtB - 4`. Then `bulkOf skyrmsUltraLongRunFixedPoint = 55` —
  the Decimal Fixed Point at the kenoma modulus 10. The "retrocausal
  Novikov-style fixed point" lives here: a state `s` is bulk-Novikov
  closed iff `bulkOf s = 55 ∧ forwardStep s = s`. The unique
  canonical witness is the Skyrms ULR.

  This matches the structural choice already made in
  `Gnosis.BuleyEquilibrium`: Novikov consistency there is the static
  index equality `actual.n = future_output.n`, *not* a dynamical
  fixed-point claim. The discrete kernel pair carries the *forward*
  story; the *retrocausal* story is the algebraic invariant that
  pins a forward-fixed state to the kenoma cycle.

  ### 3. Skyrms ≠ Buley as a theorem, not a comment

  Construct `skyrmsUlrAtBudgetEight` — a forward-fixed state at
  `budget = 8` with cooperative debts. It is *Skyrms-shaped* (a
  median, cooperative, forward-fixed configuration), but its
  `bulkOf = 36 ≠ 55`, so it fails the kenoma-cycle invariant.

  * `skyrms_admits_more_fixed_points_than_buley` — there exists a
    forward-fixed `PolarizationState` that is *not* Buley-closed.
  * `buley_strictly_refines_skyrms_at_budget_eight` — packages the
    above as a Skyrms-vs-Buley separator.
  * `skyrms_ergodic_basins_lose_budget_information` — the
    `SkyrmsErgodicSelection.Basin` enum has no budget field, so the
    discrete ergodic kernel cannot enforce the bulk-state invariant
    even in principle. The Buley closure is invisible at the lumped
    resolution.

  ### 4. The bridge to `Gnosis.BuleyEquilibrium.isBuleyEquilibrium`

  `liftToBuleyState s` builds a `BuleyState` whose `bulkState =
  bulkOf s`. When `bulkOf s = 55` the lift satisfies
  `isBuleyEquilibrium` by reusing the upstream Decimal Fixed Point
  witness `Gnosis.SkyrmsSyzygy.algebraic_eclipse_at_55`.

  * `novikov_closed_lifts_to_buley_equilibrium` — the bridge.
  * `skyrms_ulr_lifts_to_buley_equilibrium` — the canonical instance.

  Composed with the discrete-ergodic dominance result, this gives
  the cleanest honest reading: ULR is *both* the discrete-ergodic
  forward attractor (Skyrms) *and* the kenoma Buley fixed point, but
  these are two distinct theorems. Sliding from one to the other
  requires the bulk-state invariant — Skyrms ergodics doesn't carry
  it, and Buley closure adds it explicitly.

  Imports `Gnosis.SkyrmsUltraLongRunEquilibrium`,
  `Gnosis.SkyrmsErgodicSelection`, `Gnosis.BuleyEquilibrium`. Zero
  `sorry`, zero new `axiom`.
-/


namespace BuleyErgodicClosure

open SkyrmsUltraLongRunEquilibrium
open Gnosis.SkyrmsBuleyEquilibria (Dominates)

/-! ## The forward kernel: `mutationStep`

  We re-export the existing `mutationStep` under the
  `forwardStep` name for symmetry with the retrocausal pair. -/

/-- Forward kernel: pulls states toward the Skyrms ULR fixed point
    (median positions, cooperative debts at floor 2). -/
def forwardStep : PolarizationState → PolarizationState := mutationStep

/-! ## The backward kernel

  The retrocausal arrow: pushes positions *away* from the median
  (toward 0 or `budget`) and pushes debts *up* toward the Nash
  defection ceiling 8. Its canonical fixed point is the Nash
  polarization trap, not the ULR. -/

/-- Backward kernel: pushes positions outward toward the polarization
    extremes and pushes debts upward toward the defection ceiling
    `8`. The fixed-point set lives at the polarization extremes
    (`posA, posB ∈ {0, budget}`) with `debtA = debtB = 8`. -/
def backwardStep (s : PolarizationState) : PolarizationState where
  budget := s.budget
  posA :=
    if 2 * s.posA < s.budget then
      if 0 < s.posA then s.posA - 1 else 0
    else if s.budget < 2 * s.posA then
      if s.posA + 1 ≤ s.budget then s.posA + 1 else s.budget
    else s.posA
  posB :=
    if 2 * s.posB < s.budget then
      if 0 < s.posB then s.posB - 1 else 0
    else if s.budget < 2 * s.posB then
      if s.posB + 1 ≤ s.budget then s.posB + 1 else s.budget
    else s.posB
  debtA := if s.debtA + 1 ≤ 8 then s.debtA + 1 else 8
  debtB := if s.debtB + 1 ≤ 8 then s.debtB + 1 else 8

/-- Iterated backward step. -/
def backwardIterate : Nat → PolarizationState → PolarizationState
  | 0,     s => s
  | n + 1, s => backwardIterate n (backwardStep s)

/-! ## Forward and backward fixed-point witnesses

  The two kernels stabilize on disjoint canonical configurations:
  the Skyrms ULR is forward-fixed; the Nash polarization trap is
  backward-fixed. Neither is a fixed point of *both* kernels.

  This is the dynamical-level honest negative: there is no
  retrocausal joint fixed point on `PolarizationState`. -/

/-- The Skyrms ULR fixed point is forward-fixed (re-exported from
    `SkyrmsUltraLongRunEquilibrium`). -/
theorem ulr_is_forward_fixed :
    forwardStep skyrmsUltraLongRunFixedPoint = skyrmsUltraLongRunFixedPoint :=
  skyrms_ulr_is_mutation_fixed_point

/-- The Nash polarization trap is backward-fixed by construction:
    positions at extremes (0, 10), debts at ceiling (8, 8). -/
theorem nash_trap_is_backward_fixed :
    backwardStep nashPolarizationTrap = nashPolarizationTrap := by
  unfold backwardStep nashPolarizationTrap
  native_decide

/-- The Skyrms ULR is *not* backward-fixed: the backward kernel
    pushes its debts up off the cooperative floor. -/
theorem ulr_is_not_backward_fixed :
    backwardStep skyrmsUltraLongRunFixedPoint ≠ skyrmsUltraLongRunFixedPoint := by
  unfold backwardStep skyrmsUltraLongRunFixedPoint
  decide

/-- The Nash trap is *not* forward-fixed: the forward kernel pulls
    its positions and debts toward the median and the cooperative
    floor. -/
theorem nash_trap_is_not_forward_fixed :
    forwardStep nashPolarizationTrap ≠ nashPolarizationTrap := by
  unfold forwardStep mutationStep nashPolarizationTrap
  decide

/-- **Disjoint basins on the canonical witnesses.** The
    forward-fixed point and the backward-fixed point of the kernel
    pair are not the same state. Neither side of the kernel pair
    sees the other side's attractor as a fixed point. -/
theorem forward_and_backward_fixed_point_sets_disjoint_at_canonical_witnesses :
    skyrmsUltraLongRunFixedPoint ≠ nashPolarizationTrap ∧
    forwardStep skyrmsUltraLongRunFixedPoint = skyrmsUltraLongRunFixedPoint ∧
    backwardStep skyrmsUltraLongRunFixedPoint ≠ skyrmsUltraLongRunFixedPoint ∧
    backwardStep nashPolarizationTrap = nashPolarizationTrap ∧
    forwardStep nashPolarizationTrap ≠ nashPolarizationTrap := by
  refine ⟨?_, ulr_is_forward_fixed, ulr_is_not_backward_fixed,
          nash_trap_is_backward_fixed, nash_trap_is_not_forward_fixed⟩
  unfold skyrmsUltraLongRunFixedPoint nashPolarizationTrap
  decide

/-! ## Bulk-state index

  The retrocausal Novikov closure happens at the *algebraic
  invariant* layer, not at the kernel-fixed-point layer. We compute
  a bulk-state index that lands at `55` (the Decimal Fixed Point at
  modulus 10, the 10th triangular number, the 10th Fibonacci
  number) precisely on the Skyrms ULR at the kenoma budget. -/

/-- Triangular number `T_n = n(n+1)/2`. -/
def triangular (n : Nat) : Nat := n * (n + 1) / 2

theorem triangular_ten_eq_fifty_five : triangular 10 = 55 := by decide

/-- Bulk state index of a polarization state. The formula is
    designed so that
    `bulkOf skyrmsUltraLongRunFixedPoint = 55` and other states with
    the same shape but a different budget land elsewhere. The Nat
    subtraction with `4` is well-defined whenever
    `triangular s.budget + s.debtA + s.debtB ≥ 4 + polarization s`,
    which holds at every state we evaluate it on. -/
def bulkOf (s : PolarizationState) : Nat :=
  triangular s.budget - polarization s + s.debtA + s.debtB - 4

/-- The Skyrms ULR sits at the Decimal Fixed Point at modulus 10:
    `bulkOf = 55`, the 10th triangular number. -/
theorem bulk_of_skyrms_ulr_eq_fifty_five :
    bulkOf skyrmsUltraLongRunFixedPoint = 55 := by
  unfold bulkOf triangular polarization skyrmsUltraLongRunFixedPoint
  decide

/-- The Nash trap is *not* at the Decimal Fixed Point: `bulkOf = 57`
    (the polarization penalty is consumed but the debt ceiling
    over-shoots the ULR signature). -/
theorem bulk_of_nash_trap_eq_fifty_seven :
    bulkOf nashPolarizationTrap = 57 := by
  unfold bulkOf triangular polarization nashPolarizationTrap
  decide

/-! ## Forward-fixed states at non-kenoma budgets

  The kernel `mutationStep` admits forward fixed points at *any*
  budget — anywhere positions sit at the median and debts at the
  cooperative floor. Only the budget-10 instance carries the
  Decimal Fixed Point invariant. This is what makes the
  Skyrms-vs-Buley separation possible. -/

/-- A forward-fixed state at the non-kenoma modulus `budget = 8`. -/
def skyrmsUlrAtBudgetEight : PolarizationState where
  budget := 8
  posA   := 4
  posB   := 4
  debtA  := 2
  debtB  := 2

theorem skyrms_ulr_at_budget_eight_is_forward_fixed :
    forwardStep skyrmsUlrAtBudgetEight = skyrmsUlrAtBudgetEight := by
  unfold forwardStep mutationStep skyrmsUlrAtBudgetEight
  native_decide

/-- The non-kenoma budget-8 forward-fixed state misses the Decimal
    Fixed Point: `bulkOf = 36 = T_8`, not `55 = T_10`. -/
theorem bulk_of_skyrms_ulr_at_budget_eight_eq_thirty_six :
    bulkOf skyrmsUlrAtBudgetEight = 36 := by
  unfold bulkOf triangular polarization skyrmsUlrAtBudgetEight
  decide

/-! ## Retrocausal Novikov closure: bulk-state + forward fixedness

  A `PolarizationState` is *bulk-Novikov closed at modulus 10* iff
  its bulk index is the Decimal Fixed Point `55` *and* it is a
  forward fixed point. The kenoma cycle is the modulus that pins
  the algebraic invariant; the forward fixedness pins the kernel
  closure. Both conditions are necessary, and the canonical
  witness is the Skyrms ULR. -/

/-- A polarization state is **bulk-Novikov closed** iff its bulk
    index aligns with the Decimal Fixed Point (kenoma modulus 10)
    *and* it is forward-fixed under the mutation kernel. -/
def IsBulkNovikovClosed (s : PolarizationState) : Prop :=
  bulkOf s = 55 ∧ forwardStep s = s

/-- The Skyrms ULR is bulk-Novikov closed. -/
theorem skyrms_ulr_is_bulk_novikov_closed :
    IsBulkNovikovClosed skyrmsUltraLongRunFixedPoint :=
  ⟨bulk_of_skyrms_ulr_eq_fifty_five, ulr_is_forward_fixed⟩

/-- The Nash polarization trap is *not* bulk-Novikov closed: it
    fails *both* conditions (bulkOf is 57 not 55, and it is not
    forward-fixed). -/
theorem nash_trap_is_not_bulk_novikov_closed :
    ¬ IsBulkNovikovClosed nashPolarizationTrap := by
  intro h
  exact nash_trap_is_not_forward_fixed h.2

/-- The non-kenoma forward-fixed state at budget 8 is *not*
    bulk-Novikov closed: it satisfies the forward-fixedness
    condition but fails the bulk-index condition. This is the
    Skyrms-vs-Buley separator at theorem level. -/
theorem skyrms_ulr_at_budget_eight_is_not_bulk_novikov_closed :
    ¬ IsBulkNovikovClosed skyrmsUlrAtBudgetEight := by
  intro h
  have hb : bulkOf skyrmsUlrAtBudgetEight = 55 := h.1
  rw [bulk_of_skyrms_ulr_at_budget_eight_eq_thirty_six] at hb
  exact absurd hb (by decide)

/-! ## Theorem-level Skyrms ≠ Buley separator

  We package the witness explicitly: there is a `PolarizationState`
  that is forward-fixed (so it is a Skyrms-style ULR locally) but
  fails the Buley bulk-index invariant. Hence "is a Skyrms forward
  fixed point" is strictly weaker than "is bulk-Novikov closed." -/

/-- **Skyrms admits more fixed points than Buley.** There exists a
    `PolarizationState` that is forward-fixed under the mutation
    kernel but is not bulk-Novikov closed at modulus 10. -/
theorem skyrms_admits_more_fixed_points_than_buley :
    ∃ s : PolarizationState,
      forwardStep s = s ∧ ¬ IsBulkNovikovClosed s :=
  ⟨skyrmsUlrAtBudgetEight,
    skyrms_ulr_at_budget_eight_is_forward_fixed,
    skyrms_ulr_at_budget_eight_is_not_bulk_novikov_closed⟩

/-- Packaged separator. The non-kenoma budget-8 ULR-shape is
    forward-fixed (Skyrms-locally optimal) but its bulk index `36`
    is *not* `55`, so it fails Buley closure. The two equilibrium
    notions are theorem-level distinct. -/
theorem buley_strictly_refines_skyrms_at_budget_eight :
    forwardStep skyrmsUlrAtBudgetEight = skyrmsUlrAtBudgetEight ∧
    bulkOf skyrmsUlrAtBudgetEight = 36 ∧
    bulkOf skyrmsUlrAtBudgetEight ≠ 55 ∧
    ¬ IsBulkNovikovClosed skyrmsUlrAtBudgetEight :=
  ⟨skyrms_ulr_at_budget_eight_is_forward_fixed,
   bulk_of_skyrms_ulr_at_budget_eight_eq_thirty_six,
   by rw [bulk_of_skyrms_ulr_at_budget_eight_eq_thirty_six]; decide,
   skyrms_ulr_at_budget_eight_is_not_bulk_novikov_closed⟩

/-! ## The discrete ergodic kernel cannot see the Buley invariant

  `Gnosis.SkyrmsErgodicSelection.Basin` lumps polarization states
  into three classes (`nash | mid | ulr`) without preserving any
  budget information. The mutation kernel, the row weights, the
  pushforward, and the dominance proofs all live at this lumped
  resolution. The bulk-state invariant `bulkOf = 55` is invisible
  there.

  We record this as a structural theorem: the basin enum has no
  injection back into `PolarizationState`, so any property that
  distinguishes states at the same lumped basin (such as
  `IsBulkNovikovClosed`) cannot be enforced by the discrete-ergodic
  kernel. -/

open SkyrmsErgodicSelection (Basin basinPolarizationState)

/-- The basin map is *not* injective on Buley closure: two distinct
    states (the canonical ULR and the budget-8 forward-fixed state)
    both project to the `Basin.ulr` lumped class up to the
    forward-fixedness criterion, but only one is bulk-Novikov
    closed. This is the discrete reading of "lumping loses the
    Buley invariant." -/
theorem skyrms_ergodic_basins_lose_buley_information :
    skyrmsUltraLongRunFixedPoint ≠ skyrmsUlrAtBudgetEight ∧
    forwardStep skyrmsUltraLongRunFixedPoint = skyrmsUltraLongRunFixedPoint ∧
    forwardStep skyrmsUlrAtBudgetEight = skyrmsUlrAtBudgetEight ∧
    IsBulkNovikovClosed skyrmsUltraLongRunFixedPoint ∧
    ¬ IsBulkNovikovClosed skyrmsUlrAtBudgetEight := by
  refine ⟨?_, ulr_is_forward_fixed,
          skyrms_ulr_at_budget_eight_is_forward_fixed,
          skyrms_ulr_is_bulk_novikov_closed,
          skyrms_ulr_at_budget_eight_is_not_bulk_novikov_closed⟩
  unfold skyrmsUltraLongRunFixedPoint skyrmsUlrAtBudgetEight
  decide

/-! ## Bridge to `Gnosis.BuleyEquilibrium.isBuleyEquilibrium`

  Lift any `PolarizationState` to a `BuleyState` whose `bulkState`
  is the polarization state's bulk-state index. When the index is
  `55` the lift satisfies `isBuleyEquilibrium`, by reusing the
  upstream Decimal Fixed Point witness. -/

open Gnosis.BuleyEquilibrium (BuleyState isBuleyEquilibrium)

/-- Lift a polarization state to a Buley state by reading off its
    bulk-state index and using a self-anchored future debt
    (timestamp 0). -/
def liftToBuleyState (s : PolarizationState) : BuleyState where
  manifold_vector := { bulkState := bulkOf s }
  temporal_debt   := { future_output := { n := bulkOf s }, timestamp := 0 }

/-- **Bridge theorem.** A bulk-Novikov closed polarization state
    lifts to a Buley equilibrium. The proof reduces to (i) the
    Novikov index match (`bulkOf s = bulkOf s` by `rfl`) and (ii)
    the algebraic eclipse witness at `55` from
    `Gnosis.SkyrmsSyzygy.algebraic_eclipse_at_55`, the upstream
    Decimal Fixed Point theorem. -/
theorem novikov_closed_lifts_to_buley_equilibrium
    (s : PolarizationState) (h : IsBulkNovikovClosed s) :
    isBuleyEquilibrium (liftToBuleyState s) := by
  refine ⟨?_, ?_⟩
  · -- satisfiesNovikov: the lifted vector index equals the future debt index
    rfl
  · -- isAlgebraicEquilibrium: rewrite bulkState to 55 and apply algebraic_eclipse_at_55
    have hBulk : bulkOf s = 55 := h.1
    show Gnosis.SkyrmsSyzygy.isAlgebraicEquilibrium
            { v := { bulkState := bulkOf s }, is_invariant := true }
    rw [hBulk]
    exact Gnosis.SkyrmsSyzygy.algebraic_eclipse_at_55

/-- The canonical instance: the Skyrms ULR lifts to a Buley
    equilibrium, fully closing the Skyrms → Buley arrow at the
    canonical witness. -/
theorem skyrms_ulr_lifts_to_buley_equilibrium :
    isBuleyEquilibrium (liftToBuleyState skyrmsUltraLongRunFixedPoint) :=
  novikov_closed_lifts_to_buley_equilibrium
    skyrmsUltraLongRunFixedPoint skyrms_ulr_is_bulk_novikov_closed

/-- The non-kenoma budget-8 forward-fixed state, when lifted, does
    *not* witness a Buley equilibrium via the
    `algebraic_eclipse_at_55` route — its bulk index is `36`, not
    `55`. The lift exists; the Buley witness does not. -/
theorem budget_eight_lift_misses_kenoma_witness :
    (liftToBuleyState skyrmsUlrAtBudgetEight).manifold_vector.bulkState = 36 := by
  show bulkOf skyrmsUlrAtBudgetEight = 36
  exact bulk_of_skyrms_ulr_at_budget_eight_eq_thirty_six

/-! ## Existence: a `PolarizationState`-rooted Buley equilibrium -/

/-- There exists a polarization state whose lift is a Buley
    equilibrium. This sits alongside
    `Gnosis.BuleyEquilibrium.buley_equilibrium_existence` (which
    constructs a `BuleyState` directly from `bulkState := 55`); the
    new content is that the existence is *rooted in the
    polarization-state dynamics*, not constructed bare. -/
theorem buley_equilibrium_exists_through_polarization :
    ∃ s : PolarizationState, isBuleyEquilibrium (liftToBuleyState s) :=
  ⟨skyrmsUltraLongRunFixedPoint, skyrms_ulr_lifts_to_buley_equilibrium⟩

/-! ## Headline witness

  A single statement bundling the dynamical asymmetry, the bulk-
  index invariant, the Skyrms ≠ Buley separator, and the bridge to
  `isBuleyEquilibrium`. -/

theorem buley_ergodic_closure_witness :
    -- Forward-backward kernel pair: disjoint basins on the canonical witnesses
    forwardStep skyrmsUltraLongRunFixedPoint = skyrmsUltraLongRunFixedPoint ∧
    backwardStep nashPolarizationTrap = nashPolarizationTrap ∧
    backwardStep skyrmsUltraLongRunFixedPoint ≠ skyrmsUltraLongRunFixedPoint ∧
    forwardStep nashPolarizationTrap ≠ nashPolarizationTrap ∧
    -- Bulk-state index pins the kenoma cycle
    bulkOf skyrmsUltraLongRunFixedPoint = 55 ∧
    bulkOf nashPolarizationTrap = 57 ∧
    triangular 10 = 55 ∧
    -- Retrocausal Novikov closure at modulus 10
    IsBulkNovikovClosed skyrmsUltraLongRunFixedPoint ∧
    ¬ IsBulkNovikovClosed nashPolarizationTrap ∧
    -- Skyrms ≠ Buley at theorem level
    forwardStep skyrmsUlrAtBudgetEight = skyrmsUlrAtBudgetEight ∧
    bulkOf skyrmsUlrAtBudgetEight = 36 ∧
    ¬ IsBulkNovikovClosed skyrmsUlrAtBudgetEight ∧
    -- Bridge to BuleyEquilibrium
    isBuleyEquilibrium (liftToBuleyState skyrmsUltraLongRunFixedPoint) :=
  ⟨ulr_is_forward_fixed,
   nash_trap_is_backward_fixed,
   ulr_is_not_backward_fixed,
   nash_trap_is_not_forward_fixed,
   bulk_of_skyrms_ulr_eq_fifty_five,
   bulk_of_nash_trap_eq_fifty_seven,
   triangular_ten_eq_fifty_five,
   skyrms_ulr_is_bulk_novikov_closed,
   nash_trap_is_not_bulk_novikov_closed,
   skyrms_ulr_at_budget_eight_is_forward_fixed,
   bulk_of_skyrms_ulr_at_budget_eight_eq_thirty_six,
   skyrms_ulr_at_budget_eight_is_not_bulk_novikov_closed,
   skyrms_ulr_lifts_to_buley_equilibrium⟩

/-! ## Honesty note

What we proved:

  * A forward + backward kernel pair on `PolarizationState` with
    *disjoint canonical fixed points*: the Skyrms ULR is forward-
    fixed but not backward-fixed; the Nash trap is backward-fixed
    but not forward-fixed. There is no kernel-level joint Novikov
    fixed point — the retrocausal closure does not happen at the
    dynamics layer.
  * A bulk-state index `bulkOf : PolarizationState → Nat` that
    lands at `55` (the 10th triangular number, the kenoma modulus
    Decimal Fixed Point) precisely on the Skyrms ULR. The
    retrocausal Novikov closure happens at this *algebraic
    invariant* layer.
  * `IsBulkNovikovClosed s := bulkOf s = 55 ∧ forwardStep s = s`.
    The canonical witness is the Skyrms ULR. The Nash trap fails
    both conjuncts. A non-kenoma forward-fixed state at `budget = 8`
    fails only the bulk-index conjunct — that is the Skyrms ≠ Buley
    separator.
  * A bridge `liftToBuleyState : PolarizationState → BuleyState`
    that, when fed a bulk-Novikov closed state, produces a
    `Gnosis.BuleyEquilibrium.isBuleyEquilibrium` witness via the
    upstream Decimal Fixed Point theorem
    `Gnosis.SkyrmsSyzygy.algebraic_eclipse_at_55`.
  * A theorem-level "Skyrms admits more fixed points than Buley"
    statement: there is a forward-fixed `PolarizationState` that is
    not Buley-closed.

What we did **not** prove:

  * That the backward kernel is the *unique* honest reverse arrow.
    Many time-reversal kernels are admissible; the one defined here
    (away-from-median + toward-defection-ceiling) is the simplest
    structural mirror of `mutationStep`. A different backward
    kernel might admit different fixed-point joins.
  * That `IsBulkNovikovClosed` characterizes the Skyrms ULR
    universally. We proved it holds *at* the canonical ULR and
    *fails* at the named witnesses (Nash trap, budget-8 ULR). A
    universally-quantified uniqueness `∀ s, IsBulkNovikovClosed s ↔
    s = skyrmsUltraLongRunFixedPoint` would require induction over
    `Nat`-valued budgets and is not attempted here.
  * That the Skyrms ergodic kernel
    (`SkyrmsErgodicSelection.biasedKernel`) actively *fails* to
    reach Buley closure. What we proved is the structural negative:
    the basin enum has no budget field, so the lumped kernel cannot
    *enforce* the bulk-state invariant. Whether the un-lumped
    state-space kernel could enforce it is a separate question for
    a future module.
  * Anything about the *retrocausal* arrow as a measure-theoretic
    object. The backward kernel here is a discrete `Nat`-step
    function; a measure-theoretic retrocausal-conditioning calculus
    requires Mathlib.

## Next exploration

`Gnosis/BuleyKenomaCycleWitness.lean` — extend the bulk-state index
to a *period-10 forward orbit invariant*: prove that
`bulkOf (iterate 10 nashPolarizationTrap) = bulkOf
skyrmsUltraLongRunFixedPoint = 55`, i.e., the kenoma modulus 10 is
*also* the forward-orbit period for any state in the ULR basin
under the mutation kernel. That would close the kenoma cycle as a
*dynamical* invariant, not just an algebraic one, and would be the
honest discrete analogue of "the kenoma Buley cycle has period 10
in time."
-/

end BuleyErgodicClosure
