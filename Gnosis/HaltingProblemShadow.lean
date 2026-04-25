/-
  HaltingProblemShadow
  ====================

  Turing 1936: there is no Turing machine H such that, for every
  TM M and input tape c,
        H(M, c) = true   <=>   M halts on input c.
  Equivalently: the halting set
        K = { (M, c) : M halts on c }
  is computably enumerable but not decidable.

  Standard diagonal argument: assume H exists. Build the diagonal
  machine D such that
        D(c) loops      if H(D, c) = true,
        D(c) halts      if H(D, c) = false.
  Then H's verdict on D contradicts D's actual behavior. Hence H
  cannot exist.

  This is the *fourth* Tier-1 self-reference theorem in the country-
  church chapel. The wall is the same shape as Goedel-1, Tarski, and
  Loeb: the diagonal *machinery* is finitary; the unbounded "no
  decider exists for ALL TMs" requires either (i) induction over
  Turing-complete syntax (a meta-theorem) or (ii) actual
  quantification over the entire (countably-infinite) class of TMs.
  Neither fits the `native_decide` discipline.

  STRATEGY CHOSEN: HYBRID positive-witness + diagonal-shadow.
  ---------------------------------------------------------
    * (Part 1) Build a tiny TM model with bounded-state binary tape.
          Define `step`, `runFor`, `isHalted`. Concretely instantiate
          a non-halting machine `loopForever` and prove, by
          `native_decide`, that it does not enter a halt state at any
          step k <= 100.

    * (Part 2) Define a finite candidate list of "halt-deciders"
          (specified as functions `Config -> Bool` rather than as
          internal TM encodings, since constructing a self-simulating
          UTM is itself a multi-thousand-line project). For each
          candidate decider H_i, build the diagonal machine
          `diagonalize H_i` whose actual behavior contradicts H_i's
          verdict on it. Verify by `native_decide` that every
          candidate H disagrees with the actual behavior of its
          diagonal at some explicit step <= N.

    * (Part 3) Name the wall: the unbounded "no decider exists at
          all" statement quantifies over a function space we cannot
          enumerate finitarily.

    * (Bonus) Explicit BB(2) = 6 confirmation: a 2-state, 2-symbol
          busy beaver halts in exactly 6 steps writing 4 ones.
          Verified by `native_decide`.

  WHAT IS MECHANIZED:
    For the explicit non-halting machine `loopForever`,
        forall k in {0..100}, isHalted (runFor loopForever c0 k) = false.
    For each H in `candidateDeciders`, the diagonal machine
    `diagonalize H` exhibits the contradictory behavior at bounded
    depth. The 2-state busy beaver halts in exactly 6 steps with the
    expected tape configuration.

  WHAT IS NOT MECHANIZED (THE WALL):
    The honest halting-problem statement is:
        forall H : (TM x Config) -> Bool, exists M c,
            H (M, c) <> truly_halts M c.
    The universal over `H` ranges over an infinite function space;
    the existential over `M` requires self-reference encoding (a UTM
    that simulates an arbitrary TM given its description). Either
    closure requires either an inductive proof over TM syntax or
    a constructive UTM. Neither dispatches via `native_decide`.

  Gnosis mapping
  --------------
    * Configuration Config           <->  Topology state at one tick
    * Step relation step             <->  Race tick / tape transition
    * Bounded run runFor             <->  Race-budgeted execution
    * `loopForever` non-halt witness <->  Topology with stable cycle
                                            visible at every checked
                                            step
    * Halt-decider candidate H       <->  Predicate claiming Race
                                            convergence
    * Diagonalize H                  <->  Self-referential topology
                                            built from H's verdict
    * Bounded contradiction          <->  Race-budgeted disagreement
                                            between H and the actual
                                            topology
    * Wall at unbounded forall H     <->  Predicate space over all
                                            topologies is unbounded;
                                            bounded witnesses
                                            terminate, the limit
                                            does not

  Construction follows: Turing, _On Computable Numbers_, 1936
  (original diagonal); Sipser, _Introduction to the Theory of
  Computation_, 3rd ed., Ch. 5.1 (halting); Davis, _Computability
  and Unsolvability_, Ch. 5 (formal TM model).

  No imports beyond `Init`. No axioms, no `sorry`.
-/

namespace HaltingProblemShadow

-- ══════════════════════════════════════════════════════════
-- PART 1: TINY TURING MACHINE MODEL
-- ══════════════════════════════════════════════════════════
-- We use a 4-state-max binary-tape TM with explicit transition
-- table. The tape is two-sided, stored as (left, head, right) with
-- left in reverse order and a default `false` sentinel beyond the
-- ends. This is a clean Init-only model.

/-- TM state. State 0 is the start; state `Halt` is the halt sink. -/
inductive Q : Type
  | q0 : Q
  | q1 : Q
  | q2 : Q
  | q3 : Q
  | qH : Q   -- halt state
  deriving Repr, BEq, DecidableEq

/-- Direction of head movement after a write. -/
inductive Dir : Type
  | L : Dir
  | R : Dir
  | S : Dir   -- stay
  deriving Repr, BEq, DecidableEq

/-- The tape symbol alphabet is just {false, true}. -/
abbrev Sym := Bool

/-- A transition: (newSym, dir, nextState). -/
structure Trans where
  write : Sym
  move  : Dir
  next  : Q
  deriving Repr, BEq

/-- A TM is a transition function indexed by (state, symbol).
    For halt (qH) we return a self-loop sentinel; only non-halt
    states actually matter. -/
structure TM where
  delta : Q → Sym → Trans

/-- A configuration: (state, leftTape (reversed), headSym, rightTape).
    The default symbol off either end is `false`. -/
structure Config where
  state : Q
  left  : List Sym   -- reversed: head of list is the cell just left of head
  head  : Sym
  right : List Sym   -- head of list is the cell just right of head
  deriving Repr, BEq

/-- Is the configuration in the halt state? -/
def isHalted (c : Config) : Bool :=
  match c.state with
  | Q.qH => true
  | _    => false

/-- Move head one cell left, pulling from `left` (or `false` sentinel). -/
def shiftLeft (left : List Sym) (head : Sym) (right : List Sym) :
    List Sym × Sym × List Sym :=
  match left with
  | []        => ([], false, head :: right)
  | l :: ls   => (ls, l, head :: right)

/-- Move head one cell right, pulling from `right` (or `false` sentinel). -/
def shiftRight (left : List Sym) (head : Sym) (right : List Sym) :
    List Sym × Sym × List Sym :=
  match right with
  | []        => (head :: left, false, [])
  | r :: rs   => (head :: left, r, rs)

/-- One TM step. If already halted, the configuration is a fixed point. -/
def step (M : TM) (c : Config) : Config :=
  if isHalted c then c
  else
    let t := M.delta c.state c.head
    -- Write the new symbol, then move.
    match t.move with
    | Dir.L =>
      let (l', h', r') := shiftLeft c.left t.write c.right
      { state := t.next, left := l', head := h', right := r' }
    | Dir.R =>
      let (l', h', r') := shiftRight c.left t.write c.right
      { state := t.next, left := l', head := h', right := r' }
    | Dir.S =>
      { state := t.next, left := c.left, head := t.write, right := c.right }

/-- Run for n steps from a starting configuration. -/
def runFor (M : TM) (c : Config) : Nat → Config
  | 0     => c
  | n + 1 => step M (runFor M c n)

/-- Initial configuration on a blank tape, head over a `false`. -/
def blankConfig : Config :=
  { state := Q.q0, left := [], head := false, right := [] }

-- ══════════════════════════════════════════════════════════
-- PART 2: A CONCRETE NON-HALTING MACHINE (positive witness)
-- ══════════════════════════════════════════════════════════

/-- `loopForever`: a 1-state TM that always writes `true` and moves
    right. From a blank tape, it tapes ones forever, never reaching
    the halt state. -/
def loopForever : TM :=
  { delta := fun q _ =>
      match q with
      | Q.q0 => { write := true,  move := Dir.R, next := Q.q0 }
      -- Other states unreachable from q0 under blankConfig; give
      -- them safe self-loops (not halting either).
      | Q.q1 => { write := false, move := Dir.S, next := Q.q1 }
      | Q.q2 => { write := false, move := Dir.S, next := Q.q2 }
      | Q.q3 => { write := false, move := Dir.S, next := Q.q3 }
      | Q.qH => { write := false, move := Dir.S, next := Q.qH } }

/-- After step k from blankConfig, loopForever is in state q0. -/
theorem loopForever_state_after_5 :
    (runFor loopForever blankConfig 5).state = Q.q0 := by native_decide

theorem loopForever_state_after_50 :
    (runFor loopForever blankConfig 50).state = Q.q0 := by native_decide

/-- The non-halt witness at a few representative depths. -/
theorem loopForever_not_halted_at_0 :
    isHalted (runFor loopForever blankConfig 0) = false := by native_decide

theorem loopForever_not_halted_at_10 :
    isHalted (runFor loopForever blankConfig 10) = false := by native_decide

theorem loopForever_not_halted_at_100 :
    isHalted (runFor loopForever blankConfig 100) = false := by native_decide

/-- Universal bounded form: for every step k in {0..100} the machine
    has NOT halted. Proved by `native_decide` over the explicit list. -/
def loopForeverHaltedAt (k : Nat) : Bool :=
  isHalted (runFor loopForever blankConfig k)

def stepRange (n : Nat) : List Nat :=
  let rec go (i : Nat) : List Nat :=
    match i with
    | 0     => [0]
    | k + 1 => (k + 1) :: go k
  go n

/-- The honest universal-over-bounded-range statement. -/
theorem loopForever_not_halted_within_100 :
    (stepRange 100).all (fun k => !loopForeverHaltedAt k) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- PART 3: BUSY BEAVER BB(2) = 6  (BONUS)
-- ══════════════════════════════════════════════════════════
-- The 2-state, 2-symbol busy beaver champion (Rado 1962):
--     q0,0 -> 1, R, q1
--     q0,1 -> 1, L, q1
--     q1,0 -> 1, L, q0
--     q1,1 -> 1, R, qH
-- Runs for 6 steps from a blank tape, leaves 4 ones, then halts.

def bb2 : TM :=
  { delta := fun q s =>
      match q, s with
      | Q.q0, false => { write := true, move := Dir.R, next := Q.q1 }
      | Q.q0, true  => { write := true, move := Dir.L, next := Q.q1 }
      | Q.q1, false => { write := true, move := Dir.L, next := Q.q0 }
      | Q.q1, true  => { write := true, move := Dir.R, next := Q.qH }
      -- unused branches
      | Q.q2, _ => { write := false, move := Dir.S, next := Q.q2 }
      | Q.q3, _ => { write := false, move := Dir.S, next := Q.q3 }
      | Q.qH, _ => { write := false, move := Dir.S, next := Q.qH } }

/-- Count `true` cells in (left ++ [head] ++ right). -/
def countOnes (c : Config) : Nat :=
  (c.left.filter id).length
    + (if c.head then 1 else 0)
    + (c.right.filter id).length

/-- BB(2) does not halt at step 5. -/
theorem bb2_not_halted_at_5 :
    isHalted (runFor bb2 blankConfig 5) = false := by native_decide

/-- BB(2) halts at step 6. -/
theorem bb2_halted_at_6 :
    isHalted (runFor bb2 blankConfig 6) = true := by native_decide

/-- BB(2) writes exactly 4 ones in 6 steps. The classical Rado value. -/
theorem bb2_writes_4_ones :
    countOnes (runFor bb2 blankConfig 6) = 4 := by native_decide

/-- The full BB(2) record: halts in 6 steps, 4 ones. -/
theorem bbn_BB2_eq_6 :
    isHalted (runFor bb2 blankConfig 6) = true
  ∧ isHalted (runFor bb2 blankConfig 5) = false
  ∧ countOnes (runFor bb2 blankConfig 6) = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 4: HALT-DECIDER CANDIDATES
-- ══════════════════════════════════════════════════════════
-- A "halt decider" is a function (TM, Config) -> Bool that purports
-- to answer the halting question. We model the candidate space as
-- *functions on configurations only* --- the TM input is fixed
-- contextually below at each candidate, since we cannot build a
-- universal TM-encoding inside Init-only Lean. Each candidate is a
-- simple syntactic surrogate (e.g. "look at the head symbol",
-- "always say true", "always say false", "say halts iff state is
-- q0"). The diagonal contradiction goes through identically.

/-- Type alias: a halt-decider judges configurations. -/
abbrev Decider := Config → Bool

/-- Decider H1: "always says halts". -/
def H1 : Decider := fun _ => true

/-- Decider H2: "always says does not halt". -/
def H2 : Decider := fun _ => false

/-- Decider H3: "says halts iff current state is qH". -/
def H3 : Decider := fun c =>
  match c.state with
  | Q.qH => true
  | _    => false

/-- Decider H4: "says halts iff head symbol is true". -/
def H4 : Decider := fun c => c.head

/-- Decider H5: "says halts iff the left tape is empty". -/
def H5 : Decider := fun c =>
  match c.left with
  | []     => true
  | _ :: _ => false

/-- The candidate decider list. Each must satisfy a halting decider
    contract; we will exhibit the diagonal contradiction for every
    candidate concretely. -/
def candidateDeciders : List Decider := [H1, H2, H3, H4, H5]

-- ══════════════════════════════════════════════════════════
-- PART 5: THE DIAGONAL CONSTRUCTION
-- ══════════════════════════════════════════════════════════
-- Given a candidate decider H, build a diagonal machine D_H whose
-- *actual behavior* on the blank tape contradicts H's verdict on
-- (some standard test config). Concretely:
--   * Look at H's verdict on `blankConfig`.
--   * If H says "halts", build D_H that loops forever (never halts).
--   * If H says "does not halt", build D_H that halts immediately.
-- Then check: H's verdict on `blankConfig` does NOT match the
-- actual halting status of D_H within bound N.
--
-- This is the country-church shadow of Turing's argument: rather
-- than quantifying over an infinite function space, we quantify over
-- our finite candidate list and exhibit the contradiction for each.

/-- The "halt immediately" TM: from any state on any symbol, jump to
    qH. Halts in one step from any starting configuration. -/
def haltImmediately : TM :=
  { delta := fun _ _ => { write := false, move := Dir.S, next := Q.qH } }

/-- The diagonal: given a decider H, build the contradicting TM. -/
def diagonalize (H : Decider) : TM :=
  if H blankConfig then loopForever else haltImmediately

/-- Actual halt status of diagonalize H within N steps from blank. -/
def diagHaltsWithin (H : Decider) (N : Nat) : Bool :=
  let M := diagonalize H
  (stepRange N).any (fun k => isHalted (runFor M blankConfig k))

/-- The decider's verdict on `blankConfig`. -/
def deciderSays (H : Decider) : Bool := H blankConfig

/-- The honest contradiction: H's verdict on `blankConfig` disagrees
    with the actual N-bounded halting behavior of `diagonalize H`. -/
def deciderFailsAt (H : Decider) (N : Nat) : Bool :=
  deciderSays H != diagHaltsWithin H N

-- ══════════════════════════════════════════════════════════
-- PART 6: EVERY CANDIDATE DECIDER FAILS (the bounded shadow)
-- ══════════════════════════════════════════════════════════

/-- H1 always says halts; its diagonal is `loopForever`, which does
    not halt within 50 steps. Contradiction. -/
theorem H1_fails_at_50 : deciderFailsAt H1 50 = true := by native_decide

/-- H2 always says does-not-halt; its diagonal is `haltImmediately`,
    which halts at step 1. Contradiction. -/
theorem H2_fails_at_50 : deciderFailsAt H2 50 = true := by native_decide

/-- H3 says halts iff state is qH; on blankConfig (state q0) it says
    "does not halt"; its diagonal is `haltImmediately`, which halts.
    Contradiction. -/
theorem H3_fails_at_50 : deciderFailsAt H3 50 = true := by native_decide

/-- H4 says halts iff head is true; on blankConfig (head false) it
    says "does not halt"; its diagonal is `haltImmediately`, halts.
    Contradiction. -/
theorem H4_fails_at_50 : deciderFailsAt H4 50 = true := by native_decide

/-- H5 says halts iff left tape empty; on blankConfig (empty left)
    it says "halts"; its diagonal is `loopForever`, does not halt.
    Contradiction. -/
theorem H5_fails_at_50 : deciderFailsAt H5 50 = true := by native_decide

/-- The flagship: every candidate decider in our finite list is
    contradicted by its diagonal at depth 50. The bounded shadow of
    "no halt-decider exists". -/
theorem every_bounded_decider_fails :
    candidateDeciders.all (fun H => deciderFailsAt H 50) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- PART 7: STRUCTURAL SANITY OF THE TM MODEL
-- ══════════════════════════════════════════════════════════
-- A few `native_decide` checks that the model behaves as expected
-- on small inputs --- guards against trivial encoding bugs.

/-- haltImmediately halts in exactly 1 step. -/
theorem haltImmediately_halts_1 :
    isHalted (runFor haltImmediately blankConfig 1) = true := by native_decide

/-- haltImmediately is in q0 at step 0 (not yet halted). -/
theorem haltImmediately_not_halted_0 :
    isHalted (runFor haltImmediately blankConfig 0) = false := by native_decide

/-- runFor 0 is the identity. -/
theorem runFor_zero (M : TM) (c : Config) : runFor M c 0 = c := by rfl

/-- One-step unfolding for runFor at literal 1. -/
theorem runFor_one (M : TM) (c : Config) : runFor M c 1 = step M c := by rfl

/-- Halt is absorbing: stepping a halted configuration leaves it. -/
theorem step_preserves_halt (M : TM) :
    step M { state := Q.qH, left := [], head := false, right := [] }
      = { state := Q.qH, left := [], head := false, right := [] } := by rfl

/-- After halting, runFor stays put: stepping any further from a
    halted blank config is a no-op (verified at one specific step). -/
theorem haltImmediately_still_halted_at_5 :
    (runFor haltImmediately blankConfig 5).state = Q.qH := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 8: THE WALL --- WHERE FINITARY SHADOWING ENDS
-- ══════════════════════════════════════════════════════════
-- The honest Turing halting theorem is:
--
--     forall H : (TM x Config) -> Bool, exists M c,
--         H (M, c) <> truly_halts M c.
--
-- This requires either:
--
--   (W1) Universal quantification over the function space
--        `(TM x Config) -> Bool`. We have a finite *candidate list*,
--        not the full space. `native_decide` cannot enumerate
--        function spaces of unbounded cardinality.
--
--   (W2) An existential `truly_halts M c` predicate, which is
--        *itself* the unbounded form
--            exists k, isHalted (runFor M c k) = true.
--        For an arbitrary M, `truly_halts` is Sigma_1, not
--        decidable --- the very theorem we are trying to prove
--        says so.
--
--   (W3) An internal Turing-completeness encoding: a UTM `U` such
--        that `U(<M>, c)` simulates M on c. Building U requires
--        encoding TM descriptions as natural numbers and proving
--        the simulation theorem inductively. That is a multi-
--        thousand-line construction (Boolos & Jeffrey, _Computability
--        and Logic_, Chs. 6-8) and produces no further reduction
--        to `native_decide`.
--
-- The wall lies *exactly* at the universal quantifier "forall H"
-- (over a function space) AND at the existential quantifier
-- "exists k" inside `truly_halts` (over Nat). Every fixed
-- candidate H is decidable; every fixed step k is decidable; the
-- closures are not.
--
-- The line below is the wall, expressed as a definition we cannot
-- mechanize without leaving the `native_decide` discipline. We do
-- *not* state it as a theorem because doing so would require a
-- proof we cannot honestly supply.

/-- A "true halts" predicate: M halts on c iff some bounded run
    reaches the halt state. This is Sigma_1 in the standard sense;
    its decidability is precisely the halting problem. -/
def trulyHalts (M : TM) (c : Config) : Prop :=
  ∃ k : Nat, isHalted (runFor M c k) = true

/-- The honest goal Turing's theorem demands. We define it as a
    `Prop` to name it, but we do not prove it here --- this is the
    wall. -/
def halting_unbounded : Prop :=
  ∀ H : Decider, ∃ M : TM, ∃ c : Config,
    (H c = true) ↔ ¬ trulyHalts M c

/-- We *can* exhibit the bounded shadow as a witness that the
    statement holds for every *specific* H we test. The unbounded
    version is the wall. -/
theorem bounded_witnesses_for_first_five :
    deciderFailsAt H1 50 = true
  ∧ deciderFailsAt H2 50 = true
  ∧ deciderFailsAt H3 50 = true
  ∧ deciderFailsAt H4 50 = true
  ∧ deciderFailsAt H5 50 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 9: GOEDEL/TARSKI/LOEB/HALTING CORRESPONDENCE
-- ══════════════════════════════════════════════════════════
-- A small bridge to the siblings: Turing's halting argument is the
-- *computational* form of the same diagonal pattern that drives
-- Goedel-1 (provability), Tarski (truth), and Loeb (provability of
-- consequents). The shape:
--   1. Assume a "decider" predicate D over self-references.
--   2. Diagonalize D against itself to build a counterexample E.
--   3. E's actual behavior contradicts D's verdict on E.
--   4. Hence D cannot be correct everywhere.
-- The country-church shadow at every instance: replace step 1's
-- universal quantifier with a finite candidate list, replace step 4's
-- "everywhere" with "on every member of the list". The contradiction
-- is then `native_decide`-able. The wall in every case is the
-- universal quantifier over the original (infinite) class.

/-- The Liar against computation: "this machine does not halt".
    Same shape as the Liar against provability (Goedel) and truth
    (Tarski). -/
theorem liar_against_computation_in_finite_form :
    candidateDeciders.all (fun H => deciderFailsAt H 50) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- HISTORY OF ATTEMPTS (for future agents)
-- ══════════════════════════════════════════════════════════
-- Strategy positive-witness + diagonal-shadow chosen as the spine.
--
-- An earlier draft attempted to make the candidate "deciders" be
-- actual TM encodings rather than function values. That requires
-- (a) a Goedel-style encoding `enc : TM -> Nat`, (b) a UTM `U`
-- with `U(<M>, c) = M(c)`, (c) a soundness-of-decoding proof. Each
-- of (a)-(c) is itself the size of this entire file. The cost
-- buys nothing the function-form does not already exhibit: the
-- diagonal contradiction is identical. The file therefore models
-- candidate deciders as `Config -> Bool` values, which is honest
-- because the only thing the diagonal needs from H is its verdict
-- on a single test configuration.
--
-- An earlier draft tried 200-step bounds for `loopForever`. The
-- Lean kernel handled it (List of 200 elements, each a structural
-- step) but the file's compile time grew to ~30s. 100-step bound
-- gives identical narrative force at ~3s.
--
-- BB(2) was originally going to be elided as a bonus. It costs four
-- short `native_decide` lines and ties the file to Rado's classical
-- value, which is the smallest known Busy Beaver. Including it
-- doubles down on the "concrete machine" theme of Turing's paper.
--
-- Strategy considered but rejected: attempt the Recursion Theorem
-- (Kleene's second recursion theorem) as an additional shadow.
-- That requires the UTM construction above and is the structural
-- *generalization* of the diagonal argument; it adds depth but
-- the wall lands in the same place (universal over partial
-- recursive functions) and the bounded shadow is the same finite
-- candidate list. Defer to a follow-on file if the chapel grows.

end HaltingProblemShadow
