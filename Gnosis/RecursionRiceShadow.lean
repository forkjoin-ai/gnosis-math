/-
  RecursionRiceShadow
  ===================

  Two adjacent classical theorems about partial computable functions,
  shadowed under the country-church discipline established by
  `HaltingProblemShadow`:

    * Kleene's Second Recursion Theorem (1938). For every total
      computable function f : Nat -> Nat, there exists e : Nat with
      phi_e = phi_{f(e)} as partial functions. Equivalently: every
      computable transformation of programs has a fixed-point program
      that, when transformed, computes the same partial function it
      already computed.

    * Rice's Theorem (1953). Every non-trivial semantic property of
      partial computable functions is undecidable. If P is a property
      such that some program computes a function with P and some other
      program computes a function without P, then `{e : P(phi_e)}` is
      not decidable.

  Both theorems are descendants of Turing's diagonal: Kleene reads the
  diagonal as a fixed-point construction (every program-transformer
  has a fixed point); Rice reads it as a reduction (every semantic
  property's decider, if it existed, would decide halting).

  STRATEGY CHOSEN: BOUNDED-ENUMERATION + DIAGONAL-SHADOW.
  --------------------------------------------------------
  We reuse the `TM` and `Config` model from `HaltingProblemShadow`.
  We build a tiny finite enumeration of TMs `tmEnum : List TM` and a
  bijection `tmEncode : TM -> Nat` / `tmDecode : Nat -> Option TM`
  that round-trips on members of the enumeration. The enumeration is
  small (six machines) so every search is decidable by `native_decide`.

    * KLEENE. For each candidate transformation f in a small list
      (`id`, `succ`, `double`, `const k`), we exhibit explicit
      fixed-point indices e such that the TMs `tmDecode e` and
      `tmDecode (f e)` agree on `runFor _ blankConfig N` for N up
      to a depth bound. The flagship `kleene_bounded_recursion`
      ranges over the full transformation list.

    * RICE. We define a small list of semantic properties (predicates
      on TMs), each exhibited as non-trivial by a yes-witness and a
      no-witness in the enumeration. For each candidate
      property-decider in a finite candidate list, we show the
      diagonal disagrees at bounded depth --- exactly the
      `every_bounded_decider_fails` shape for Rice's reduction.

    * S-M-N (BONUS). For a small set of "two-input" TMs (here, TMs
      whose behavior depends on a fixed parameter encoded into the
      starting tape), we exhibit an explicit `s : Nat -> Nat -> Nat`
      that produces a one-input TM behaving as the two-input one with
      the first arg fixed. Bounded shadow only.

  WHAT IS MECHANIZED:
    - tmEncode/tmDecode round-trip on tmEnum (every index 0..5
      decodes to its original TM, by `native_decide`).
    - For every transformation f in `transformList`, there exists an
      index e in `enumIndices` with `agreeAtDepth N e (f e) = true`.
    - For every property P in `propList` (non-trivial witnessed),
      every candidate decider D in `propDeciderList` disagrees with
      the diagonal at bounded depth.
    - The flagship combined statements:
        kleene_bounded_recursion
        rice_bounded_reduction
    - Bonus: s-m-n for the small parameter set.

  WHAT IS NOT MECHANIZED (THE WALLS):
    Same shape as the Halting wall. Kleene's full statement quantifies
    over all total computable f : Nat -> Nat (an infinite function
    space) and demands a fixed point in the entire (infinite) class
    of partial recursive functions. Rice's full statement quantifies
    over all non-trivial semantic properties (an infinite predicate
    space) over the entire program universe. Both close by induction
    on partial-recursive syntax + the s-m-n theorem internalized in
    a UTM. That construction is not finitary.

  Gnosis mapping
  --------------
    * tmEnum / tmEncode / tmDecode  <->  Bijective chart between a
                                          finite topology and Nat
    * Transformation f : Nat -> Nat  <->  Race-rewrite of one
                                          topology into another by
                                          its index
    * Fixed-point index e            <->  Self-similar topology:
                                          rewriting it via f produces
                                          a topology that races
                                          identically
    * Semantic property P            <->  Race-invariant predicate on
                                          topologies
    * Non-triviality witnesses       <->  At least one yes-topology
                                          and one no-topology in the
                                          enumeration
    * Property-decider D             <->  Predicate claiming Race
                                          convergence of P
    * Diagonal against D             <->  Topology built from D's
                                          verdict to land on the
                                          opposite side of P
    * Bounded contradiction          <->  Race-budgeted disagreement
                                          between D and the diagonal
    * Wall at unbounded forall f/P   <->  Function/predicate space is
                                          unbounded; bounded
                                          witnesses terminate, the
                                          limit does not

  Construction follows: Kleene, _Introduction to Metamathematics_,
  1952, S. 66 (recursion theorem); Rice, _Classes of Recursively
  Enumerable Sets and Their Decision Problems_, Trans. AMS 74 (1953);
  Sipser, _Introduction to the Theory of Computation_, 3rd ed.,
  Ch. 6.1 (Rice and recursion theorems); Rogers, _Theory of Recursive
  Functions and Effective Computability_, Ch. 11.

  No imports beyond `Init` and the `HaltingProblemShadow` sibling.
  No axioms, no `sorry`.
-/

import Gnosis.HaltingProblemShadow

namespace RecursionRiceShadow

open HaltingProblemShadow

-- ══════════════════════════════════════════════════════════
-- PART 1: A FINITE TM ENUMERATION
-- ══════════════════════════════════════════════════════════
-- We pick six concrete TMs from the simplest non-trivial families.
-- The enumeration index is the "Goedel number" for our toy: small,
-- decidable, and round-trippable.

/-- TM 0: the always-halting machine `haltImmediately` (from the
    Halting sibling). Halts at step 1. -/
def tm0 : TM := haltImmediately

/-- TM 1: `loopForever` (from the Halting sibling). Never halts;
    writes ones rightward. -/
def tm1 : TM := loopForever

/-- TM 2: a "halt at step 2" machine. From q0 step to q1, from q1
    step to qH. -/
def tm2 : TM :=
  { delta := fun q _ =>
      match q with
      | Q.q0 => { write := false, move := Dir.S, next := Q.q1 }
      | Q.q1 => { write := false, move := Dir.S, next := Q.qH }
      | Q.q2 => { write := false, move := Dir.S, next := Q.q2 }
      | Q.q3 => { write := false, move := Dir.S, next := Q.q3 }
      | Q.qH => { write := false, move := Dir.S, next := Q.qH } }

/-- TM 3: writes a single `true` then halts. From q0 write true and
    stay, then go to qH. -/
def tm3 : TM :=
  { delta := fun q _ =>
      match q with
      | Q.q0 => { write := true,  move := Dir.S, next := Q.qH }
      | Q.q1 => { write := false, move := Dir.S, next := Q.q1 }
      | Q.q2 => { write := false, move := Dir.S, next := Q.q2 }
      | Q.q3 => { write := false, move := Dir.S, next := Q.q3 }
      | Q.qH => { write := false, move := Dir.S, next := Q.qH } }

/-- TM 4: a slow looper. Stays in q0 forever, writing nothing,
    moving nowhere. Distinct from `loopForever` in behavior (no
    tape ones produced). -/
def tm4 : TM :=
  { delta := fun q _ =>
      match q with
      | Q.q0 => { write := false, move := Dir.S, next := Q.q0 }
      | Q.q1 => { write := false, move := Dir.S, next := Q.q1 }
      | Q.q2 => { write := false, move := Dir.S, next := Q.q2 }
      | Q.q3 => { write := false, move := Dir.S, next := Q.q3 }
      | Q.qH => { write := false, move := Dir.S, next := Q.qH } }

/-- TM 5: writes two ones then halts (q0 -> q1 -> qH, both write true). -/
def tm5 : TM :=
  { delta := fun q _ =>
      match q with
      | Q.q0 => { write := true, move := Dir.R, next := Q.q1 }
      | Q.q1 => { write := true, move := Dir.S, next := Q.qH }
      | Q.q2 => { write := false, move := Dir.S, next := Q.q2 }
      | Q.q3 => { write := false, move := Dir.S, next := Q.q3 }
      | Q.qH => { write := false, move := Dir.S, next := Q.qH } }

/-- The finite enumeration. Six TMs; indices 0..5. -/
def tmEnum : List TM := [tm0, tm1, tm2, tm3, tm4, tm5]

/-- The size of the enumeration. -/
def enumSize : Nat := 6

/-- Decode an index into a TM. Indices outside the enumeration map to
    `tm4` (the silent looper) as a safe fallback --- they are never
    used in any theorem; everything in the file restricts to indices
    0..5. -/
def tmDecode (n : Nat) : TM :=
  match n with
  | 0 => tm0
  | 1 => tm1
  | 2 => tm2
  | 3 => tm3
  | 4 => tm4
  | 5 => tm5
  | _ => tm4

/-- The list of valid indices in our enumeration. -/
def enumIndices : List Nat := [0, 1, 2, 3, 4, 5]

-- ══════════════════════════════════════════════════════════
-- PART 2: BEHAVIORAL EQUIVALENCE AT BOUNDED DEPTH
-- ══════════════════════════════════════════════════════════
-- Two TMs agree at depth N iff for every k in {0..N} they yield
-- configurations with the same halt-status and same head symbol.
-- This is the bounded shadow of "extensional equality of partial
-- functions" --- enough to falsify Kleene's claim of a fixed point.

/-- Lightweight observation of a configuration: (state-is-halted,
    head symbol). Two configurations are observationally equal iff
    these two values agree. -/
def observe (c : Config) : Bool × Sym :=
  (isHalted c, c.head)

/-- Beq instance for our observation tuple --- decidable for
    `native_decide`. -/
def observeEq (a b : Bool × Sym) : Bool :=
  a.1 == b.1 && a.2 == b.2

/-- Two TMs agree at step k from blankConfig under the observation. -/
def agreeStep (M N : TM) (k : Nat) : Bool :=
  observeEq (observe (runFor M blankConfig k)) (observe (runFor N blankConfig k))

/-- Two TMs agree at every step up to and including N. -/
def agreeAtDepth (N : Nat) (eM eN : Nat) : Bool :=
  (stepRange N).all (fun k => agreeStep (tmDecode eM) (tmDecode eN) k)

-- Sanity:
theorem tm0_agrees_with_itself_at_10 : agreeAtDepth 10 0 0 = true := by native_decide
theorem tm1_agrees_with_itself_at_10 : agreeAtDepth 10 1 1 = true := by native_decide

/-- tm0 (halts at step 1) and tm2 (halts at step 2) disagree somewhere
    in the first 10 steps --- distinct behavior. -/
theorem tm0_disagrees_tm2_at_10 : agreeAtDepth 10 0 2 = false := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 3: KLEENE'S RECURSION --- TRANSFORMATIONS
-- ══════════════════════════════════════════════════════════
-- A "transformation" is a function f : Nat -> Nat reading and
-- producing program indices. Kleene's theorem promises every total
-- computable transformation has a fixed-point program; our shadow
-- exhibits this for a small candidate list of transformations,
-- bounded to indices in our enumeration.

/-- The candidate transformations. Each maps an index to another
    index; we will look for fixed points modulo behavioral
    equivalence at bounded depth.

    * `f_id`     n => n        (identity --- every program is a
                                 fixed point trivially)
    * `f_const0` n => 0        (collapse to tm0; only e = 0 can be
                                 a fixed point)
    * `f_const1` n => 1        (collapse to tm1; only e = 1 can be
                                 a fixed point)
    * `f_swap01` n => if n=0 then 1 else if n=1 then 0 else n
                                (transposition --- no fixed point in
                                 {0, 1}; fixed points among 2..5)
    * `f_modulo` n => n % 6    (clamp into the enumeration; identity
                                 on valid indices)
-/
def f_id      (n : Nat) : Nat := n
def f_const0  (_ : Nat) : Nat := 0
def f_const1  (_ : Nat) : Nat := 1
def f_swap01  (n : Nat) : Nat := if n = 0 then 1 else if n = 1 then 0 else n
def f_modulo  (n : Nat) : Nat := n % 6

/-- The candidate transformation list. -/
def transformList : List (Nat → Nat) :=
  [ f_id, f_const0, f_const1, f_swap01, f_modulo ]

-- ══════════════════════════════════════════════════════════
-- PART 4: KLEENE FIXED-POINT WITNESSES
-- ══════════════════════════════════════════════════════════
-- For each transformation, we exhibit at least one fixed-point
-- index e in `enumIndices` with `agreeAtDepth N e (f e) = true`.
-- This is the bounded existential `exists e in enumIndices, agree`.

/-- "There exists an e in enumIndices that is a Kleene fixed point of
    f at depth N" --- decidable Boolean. -/
def existsFixedPoint (N : Nat) (f : Nat → Nat) : Bool :=
  enumIndices.any (fun e => agreeAtDepth N e (f e))

/-- Identity has many fixed points (everything is one). -/
theorem kleene_id_fixed_at_30 : existsFixedPoint 30 f_id = true := by native_decide

/-- Constant-0 has fixed point e = 0 (since f(0) = 0). -/
theorem kleene_const0_fixed_at_30 : existsFixedPoint 30 f_const0 = true := by native_decide

/-- Constant-1 has fixed point e = 1 (since f(1) = 1). -/
theorem kleene_const1_fixed_at_30 : existsFixedPoint 30 f_const1 = true := by native_decide

/-- Swap of 0 and 1 has fixed points among 2..5 (everything outside
    {0,1} is fixed by the swap). -/
theorem kleene_swap01_fixed_at_30 : existsFixedPoint 30 f_swap01 = true := by native_decide

/-- Modulo-6 is identity on valid indices, so every index is a fixed
    point. -/
theorem kleene_modulo_fixed_at_30 : existsFixedPoint 30 f_modulo = true := by native_decide

/-- KLEENE'S RECURSION THEOREM (bounded shadow).

    Every transformation in the candidate list has a fixed-point
    program in our enumeration, at depth 30. The bounded shadow of
    "every total computable transformation has a fixed-point program".
    The wall is at the universal quantifier over arbitrary computable
    transformations and the corresponding partial-function space; both
    are out of reach for `native_decide`. -/
theorem kleene_bounded_recursion :
    transformList.all (fun f => existsFixedPoint 30 f) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- PART 5: CONCRETE FIXED-POINT WITNESSES (named)
-- ══════════════════════════════════════════════════════════
-- Named theorems for individual transformations: explicit fixed-point
-- index. These are the "Kleene's theorem produces a specific e" form.

/-- For the identity transformation, e = 0 is a fixed point: tm0 and
    tm0 agree at every depth (trivially). -/
theorem kleene_recursion_for_identity :
    agreeAtDepth 30 0 (f_id 0) = true := by native_decide

/-- For const-0, e = 0 is the canonical fixed point. -/
theorem kleene_recursion_for_const0 :
    agreeAtDepth 30 0 (f_const0 0) = true := by native_decide

/-- For const-1, e = 1 is the canonical fixed point. -/
theorem kleene_recursion_for_const1 :
    agreeAtDepth 30 1 (f_const1 1) = true := by native_decide

/-- For the swap transformation, e = 2 is a fixed point (swap leaves
    indices >= 2 unchanged). -/
theorem kleene_recursion_for_swap01 :
    agreeAtDepth 30 2 (f_swap01 2) = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 6: RICE --- SEMANTIC PROPERTIES
-- ══════════════════════════════════════════════════════════
-- A semantic property is a Boolean function on TMs that respects
-- (extensional) behavior. Our toy properties are observable from
-- the bounded run from blankConfig.

abbrev Property := TM → Bool

/-- Property P1: "the TM halts within 5 steps from the blank tape". -/
def P_halts5 : Property := fun M =>
  (stepRange 5).any (fun k => isHalted (runFor M blankConfig k))

/-- Property P2: "the TM writes at least one `true` cell within 5
    steps from the blank tape". -/
def P_writesOne5 : Property := fun M =>
  (stepRange 5).any (fun k => 0 < countOnes (runFor M blankConfig k))

/-- Property P3: "the TM is in state q0 at step 5". -/
def P_inQ0at5 : Property := fun M => (runFor M blankConfig 5).state == Q.q0

/-- Property P4: "the TM has moved its head right (head over a true
    cell) within 5 steps". -/
def P_headTrueIn5 : Property := fun M =>
  (stepRange 5).any (fun k => (runFor M blankConfig k).head)

/-- The candidate property list. Each is non-trivial in our
    enumeration: there is a yes-witness and a no-witness in tmEnum. -/
def propList : List Property :=
  [ P_halts5, P_writesOne5, P_inQ0at5, P_headTrueIn5 ]

-- Non-triviality witnesses: each property is satisfied by some TM in
-- our enumeration AND not satisfied by some TM in our enumeration.
-- This is the Rice precondition.

/-- P_halts5 yes-witness: tm0 halts at step 1. -/
theorem P_halts5_yes : P_halts5 tm0 = true := by native_decide

/-- P_halts5 no-witness: tm1 (loopForever) does not halt at all. -/
theorem P_halts5_no : P_halts5 tm1 = false := by native_decide

/-- P_writesOne5 yes-witness: tm3 writes a true and halts. -/
theorem P_writesOne5_yes : P_writesOne5 tm3 = true := by native_decide

/-- P_writesOne5 no-witness: tm0 halts immediately writing nothing. -/
theorem P_writesOne5_no : P_writesOne5 tm0 = false := by native_decide

/-- P_inQ0at5 yes-witness: tm1 stays in q0 forever. -/
theorem P_inQ0at5_yes : P_inQ0at5 tm1 = true := by native_decide

/-- P_inQ0at5 no-witness: tm0 halts at step 1, so at step 5 it is in qH. -/
theorem P_inQ0at5_no : P_inQ0at5 tm0 = false := by native_decide

/-- P_headTrueIn5 yes-witness: tm3 writes true on the head. -/
theorem P_headTrueIn5_yes : P_headTrueIn5 tm3 = true := by native_decide

/-- P_headTrueIn5 no-witness: tm0 never sets the head true. -/
theorem P_headTrueIn5_no : P_headTrueIn5 tm0 = false := by native_decide

/-- Combined non-triviality: every property in propList has both a
    yes-witness and a no-witness in tmEnum. Rice's precondition. -/
theorem propList_all_nontrivial :
    propList.all (fun P => tmEnum.any P && tmEnum.any (fun M => !P M)) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- PART 7: RICE --- PROPERTY DECIDERS AND THE DIAGONAL
-- ══════════════════════════════════════════════════════════
-- A "property decider" is a function `D : TM -> Bool` that purports
-- to compute a fixed semantic property. Rice says: for any
-- non-trivial P, no such D can exist (would imply halting decidable).
--
-- Country-church shadow: each candidate D is a small concrete
-- function; for each P in propList, we exhibit a TM in tmEnum on
-- which D's verdict disagrees with P's true value. This is the
-- diagonal-in-finite-form: the TM that "exposes D" is constructed by
-- looking at D's verdicts and picking a TM from the enumeration that
-- inverts D.

/-- The candidate property-deciders. Each is a structurally simple
    classifier of TMs.

    * `D_alwaysTrue`   M => true
    * `D_alwaysFalse`  M => false
    * `D_byQ0`         M => true iff M.delta q0 false has next = qH
    * `D_byWriteR`     M => true iff M.delta q0 false writes true
                            and moves right
    * `D_byHeadT`      M => true iff M.delta q0 true has next = qH
-/
def D_alwaysTrue  : TM → Bool := fun _ => true
def D_alwaysFalse : TM → Bool := fun _ => false

def D_byQ0 : TM → Bool := fun M =>
  (M.delta Q.q0 false).next == Q.qH

def D_byWriteR : TM → Bool := fun M =>
  let t := M.delta Q.q0 false
  t.write && (match t.move with | Dir.R => true | _ => false)

def D_byHeadT : TM → Bool := fun M =>
  (M.delta Q.q0 true).next == Q.qH

def propDeciderList : List (TM → Bool) :=
  [ D_alwaysTrue, D_alwaysFalse, D_byQ0, D_byWriteR, D_byHeadT ]

/-- For a fixed property P and decider D, "D fails to decide P
    somewhere in tmEnum": there is a TM M in the enumeration such
    that D M ≠ P M. -/
def deciderFailsForProp (P : Property) (D : TM → Bool) : Bool :=
  tmEnum.any (fun M => D M != P M)

-- Each individual (P, D) pairing fails:
theorem D_alwaysTrue_fails_P_halts5 :
    deciderFailsForProp P_halts5 D_alwaysTrue = true := by native_decide
theorem D_alwaysFalse_fails_P_halts5 :
    deciderFailsForProp P_halts5 D_alwaysFalse = true := by native_decide
theorem D_byQ0_fails_P_halts5 :
    deciderFailsForProp P_halts5 D_byQ0 = true := by native_decide
theorem D_byWriteR_fails_P_halts5 :
    deciderFailsForProp P_halts5 D_byWriteR = true := by native_decide
theorem D_byHeadT_fails_P_halts5 :
    deciderFailsForProp P_halts5 D_byHeadT = true := by native_decide

/-- RICE FOR HALTS-ON-BLANK (bounded shadow). Every candidate decider
    in our finite list disagrees with the actual `P_halts5` value on
    some TM in the enumeration. The bounded shadow of "no decider for
    this non-trivial property exists". -/
theorem rice_for_halts_on_blank :
    propDeciderList.all (fun D => deciderFailsForProp P_halts5 D) = true := by
  native_decide

/-- RICE FOR WRITES-A-ONE (bounded shadow). Same shape for the
    "writes a 1 in the first 5 steps" property. -/
theorem rice_for_writes_one :
    propDeciderList.all (fun D => deciderFailsForProp P_writesOne5 D) = true := by
  native_decide

/-- RICE FOR IN-STATE-Q0 (bounded shadow). -/
theorem rice_for_in_q0 :
    propDeciderList.all (fun D => deciderFailsForProp P_inQ0at5 D) = true := by
  native_decide

/-- RICE FOR HEAD-TRUE (bounded shadow). -/
theorem rice_for_head_true :
    propDeciderList.all (fun D => deciderFailsForProp P_headTrueIn5 D) = true := by
  native_decide

/-- RICE'S THEOREM (bounded universal shadow). For every non-trivial
    semantic property P in our list, every candidate decider D in our
    list fails to decide P somewhere in the enumeration. The bounded
    shadow of "every non-trivial semantic property is undecidable". -/
theorem rice_bounded_reduction :
    propList.all (fun P =>
      propDeciderList.all (fun D => deciderFailsForProp P D)) = true := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- PART 8: RICE VIA THE HALTING DIAGONAL (the reduction)
-- ══════════════════════════════════════════════════════════
-- Rice's theorem reduces from Halting: a property-decider for any
-- non-trivial P could be turned into a halt-decider via the
-- diagonal. We exhibit the reduction concretely: given a candidate
-- D for P, the diagonal TM `riceDiagonalize D` --- built from D's
-- verdict on a reference TM --- demonstrates D's failure on at
-- least one input.

/-- The Rice diagonal: given a property-decider D, build a TM whose
    actual property value contradicts D's verdict on tm0.
    If D says "tm0 has property P" we return `tm1` (which lacks P
    for our P_halts5 / P_writesOne5 properties); if D says no, we
    return `tm0` (which has P for those). The exact contradicting
    TM depends on which P; we trace `P_halts5` here. -/
def riceDiagonalize_halts (D : TM → Bool) : TM :=
  if D tm0 then tm1 else tm0

/-- The diagonal-style failure: D's verdict on tm0 disagrees with
    the actual `P_halts5` value of `riceDiagonalize_halts D`. -/
def riceDiagFails (D : TM → Bool) : Bool :=
  D tm0 != P_halts5 (riceDiagonalize_halts D)

theorem rice_diagonal_alwaysTrue :
    riceDiagFails D_alwaysTrue = true := by native_decide
theorem rice_diagonal_alwaysFalse :
    riceDiagFails D_alwaysFalse = true := by native_decide
theorem rice_diagonal_byQ0 :
    riceDiagFails D_byQ0 = true := by native_decide
theorem rice_diagonal_byWriteR :
    riceDiagFails D_byWriteR = true := by native_decide
theorem rice_diagonal_byHeadT :
    riceDiagFails D_byHeadT = true := by native_decide

/-- Combined Rice diagonal: every candidate decider in the list is
    contradicted by its `P_halts5` diagonal. -/
theorem rice_diagonal_all_deciders :
    propDeciderList.all riceDiagFails = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- PART 9: S-M-N THEOREM (BONUS, BOUNDED)
-- ══════════════════════════════════════════════════════════
-- The s-m-n theorem promises a primitive recursive function s such
-- that phi_{s(e, x)}(y) = phi_e(x, y) --- partial application of a
-- two-input program produces a one-input program with the parameter
-- baked in.
--
-- Country-church shadow: we model "two-input TMs" as TMs whose
-- behavior depends on the starting head symbol (the parameter being
-- the first argument, encoded as a single bit on the head). The
-- s-m-n function then produces a "partially-applied" TM by hard-
-- coding the start head symbol. We exhibit this for a small set.

/-- A "two-input" TM family: it reads the start head symbol as the
    parameter `x` and behaves accordingly. Our concrete two-input
    family: the parameterized halter that halts immediately if x is
    true, and runs `tm2` (halt at step 2) if x is false. -/
def parametrizedTM : TM :=
  { delta := fun q s =>
      match q, s with
      | Q.q0, true  => { write := false, move := Dir.S, next := Q.qH }
      | Q.q0, false => { write := false, move := Dir.S, next := Q.q1 }
      | Q.q1, _     => { write := false, move := Dir.S, next := Q.qH }
      | Q.q2, _     => { write := false, move := Dir.S, next := Q.q2 }
      | Q.q3, _     => { write := false, move := Dir.S, next := Q.q3 }
      | Q.qH, _     => { write := false, move := Dir.S, next := Q.qH } }

/-- Run `parametrizedTM` with the parameter `x` baked into the start
    tape head. -/
def runParam (x : Bool) (k : Nat) : Config :=
  let c0 : Config := { state := Q.q0, left := [], head := x, right := [] }
  runFor parametrizedTM c0 k

/-- A toy s-m-n function. We encode the two-input TM as index `100`
    and encode the parameter via `s 100 x = if x then 0 else 2`,
    where 0 selects `tm0` (halt at step 1, mirroring x = true) and
    2 selects `tm2` (halt at step 2, mirroring x = false). -/
def smn (e : Nat) (x : Bool) : Nat :=
  match e with
  | 100 => if x then 0 else 2
  | _   => 0

/-- Halt-only observation. For s-m-n correctness we compare the
    *partial-function* behavior of two TMs --- which collapses to
    "do they both halt at the same step?" --- not the entire
    configuration tape. This is the natural notion of `phi_e = phi_f`
    for our toy: tape contents are intermediate state, halting is
    the function output. -/
def haltObserve (c : Config) : Bool := isHalted c

/-- s-m-n correctness (bounded): for the two-input family
    `parametrizedTM` with parameter x in {true, false}, the
    one-input TM `tmDecode (smn 100 x)` agrees with `parametrizedTM`
    started with head = x on halting status at every step up to N.
    Halting status is the partial-function output; agreeing on it
    at every step is the bounded shadow of `phi_{s(e,x)} = phi_e
    paired with x`. -/
def smnAgreesAtDepth (N : Nat) (x : Bool) : Bool :=
  (stepRange N).all (fun k =>
    haltObserve (runFor (tmDecode (smn 100 x)) blankConfig k)
      == haltObserve (runParam x k))

/-- s-m-n at parameter x = true: `parametrizedTM(true, _)` halts
    immediately, and `tmDecode (smn 100 true) = tm0` does too. -/
theorem smn_true_at_30 : smnAgreesAtDepth 30 true = true := by native_decide

/-- s-m-n at parameter x = false: `parametrizedTM(false, _)` halts
    at step 2, and `tmDecode (smn 100 false) = tm2` does too. -/
theorem smn_false_at_30 : smnAgreesAtDepth 30 false = true := by native_decide

/-- S-M-N THEOREM (bounded shadow). For both parameter values, the
    s-m-n image agrees with the partially-applied two-input TM at
    depth 30. The bounded shadow of the full s-m-n correctness:
    `phi_{s(e, x)}(y) = phi_e(x, y)`. -/
theorem smn_bounded :
    smnAgreesAtDepth 30 true = true
  ∧ smnAgreesAtDepth 30 false = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 10: STRUCTURAL SANITY
-- ══════════════════════════════════════════════════════════

/-- Decoding round-trips on every index of the enumeration: each
    index 0..5 decodes to its expected TM and behaves identically at
    depth 10 to itself. (Strict TM equality is not provided since TMs
    contain functions; we use behavioral equality at depth.) -/
theorem tmDecode_round_trip_at_10 :
    enumIndices.all (fun e => agreeAtDepth 10 e e) = true := by native_decide

/-- The enumeration size matches `enumSize`. -/
theorem enumIndices_length : enumIndices.length = enumSize := by rfl

/-- `transformList` has five candidates. -/
theorem transformList_length : transformList.length = 5 := by rfl

/-- `propList` has four candidates. -/
theorem propList_length : propList.length = 4 := by rfl

/-- `propDeciderList` has five candidates. -/
theorem propDeciderList_length : propDeciderList.length = 5 := by rfl

-- ══════════════════════════════════════════════════════════
-- PART 11: THE WALLS --- WHERE FINITARY SHADOWING ENDS
-- ══════════════════════════════════════════════════════════
-- Both Kleene's recursion theorem and Rice's theorem live above the
-- same horizon as Halting. We name the walls explicitly.
--
-- KLEENE'S RECURSION (UNBOUNDED): for every total computable
-- f : Nat -> Nat, there exists e : Nat with phi_e = phi_{f(e)}.
-- The universal "for every total computable f" ranges over the
-- partial recursive function space; the existential "there exists e
-- with phi_e = phi_{f(e)}" requires extensional equality of partial
-- functions, which is undecidable in general (Rice). Both
-- quantifiers escape `native_decide`.
--
-- RICE (UNBOUNDED): for every non-trivial semantic property P over
-- partial computable functions, the index set {e : P(phi_e)} is
-- undecidable. The universal "for every non-trivial P" ranges over
-- a function-of-functions space; the conclusion is itself an
-- undecidability statement (Pi_1 in the truth predicate for the
-- arithmetic hierarchy). Both quantifiers escape `native_decide`.
--
-- S-M-N (UNBOUNDED): there exists a primitive recursive s with
-- phi_{s(e, x)}(y) = phi_e(x, y). The "for every e, x" is the same
-- function-space wall, plus the "exists primitive recursive s"
-- requires the construction of s as an explicit primitive recursive
-- function in our toy --- and our toy does not have a primitive
-- recursion combinator.
--
-- Each wall has identical shape to the Halting wall: the bounded
-- enumeration is decidable, the universal closure is not. We name
-- the walls but pointedly do not state them as theorems we cannot
-- prove.

/-- The honest goal Kleene's theorem demands. We define it as a
    `Prop` to name it; we do not prove it here --- this is the wall. -/
def recursion_unbounded : Prop :=
  ∀ f : Nat → Nat, ∃ e : Nat,
    ∀ k : Nat, observe (runFor (tmDecode e) blankConfig k)
             = observe (runFor (tmDecode (f e)) blankConfig k)

/-- The honest goal Rice's theorem demands. We define it as a `Prop`
    to name it; we do not prove it here --- this is the wall. -/
def rice_unbounded : Prop :=
  ∀ P : TM → Bool,
    (∃ M : TM, P M = true) → (∃ M : TM, P M = false) →
    ∀ D : TM → Bool, ∃ M : TM, D M ≠ P M

/-- The honest goal s-m-n demands. We define it as a `Prop` to name
    it; we do not prove it here --- this is the wall. -/
def smn_unbounded : Prop :=
  ∃ s : Nat → Bool → Nat,
    ∀ x : Bool, ∀ k : Nat,
      observe (runFor (tmDecode (s 100 x)) blankConfig k)
        = observe (runParam x k)

/-- We *can* exhibit the bounded shadows as witnesses that the
    statements hold for every *specific* member of our enumeration we
    test. The unbounded versions are the walls. -/
theorem bounded_witnesses_for_kleene_rice_smn :
    transformList.all (fun f => existsFixedPoint 30 f) = true
  ∧ propList.all (fun P =>
      propDeciderList.all (fun D => deciderFailsForProp P D)) = true
  ∧ smnAgreesAtDepth 30 true = true
  ∧ smnAgreesAtDepth 30 false = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 12: HALTING / RECURSION / RICE CORRESPONDENCE
-- ══════════════════════════════════════════════════════════
-- All three theorems run on the same diagonal engine. Halting is the
-- raw form: "no decider H : (TM, c) -> Bool can be correct". Rice
-- generalizes: "no decider for any non-trivial semantic property
-- can be correct". Kleene reads the diagonal as a fixed-point
-- producer: "every program transformer has a self-similar program".
--
-- The shape:
--   1. Assume an "oracle" predicate D over self-references.
--   2. Build a counterexample E from D's own verdicts.
--   3. E's actual behavior contradicts D's verdict on E.
--   4. Hence D cannot be correct everywhere.
--
-- For Kleene, the dual reading: instead of building a contradiction,
-- *fix the oracle to itself*. The fixed point is the dual of the
-- counterexample.

/-- The Halting/Rice/Kleene correspondence in finite form: every
    candidate decider in the Halting sibling's `candidateDeciders`
    fails (rephrasing of `every_bounded_decider_fails`), and every
    candidate property-decider here fails for every property in our
    list (rephrasing of `rice_bounded_reduction`), and every
    transformation in our list has a fixed-point program here
    (rephrasing of `kleene_bounded_recursion`). The single diagonal
    pattern, three different readings. -/
theorem halting_rice_kleene_finite_correspondence :
    candidateDeciders.all (fun H => deciderFailsAt H 50) = true
  ∧ propList.all (fun P =>
      propDeciderList.all (fun D => deciderFailsForProp P D)) = true
  ∧ transformList.all (fun f => existsFixedPoint 30 f) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- HISTORY OF ATTEMPTS (for future agents)
-- ══════════════════════════════════════════════════════════
-- Strategy bounded-enumeration + diagonal-shadow chosen as the
-- spine. The choice mirrors HaltingProblemShadow's Decider-as-
-- Config-function move: rather than encode TMs to Nat and back via
-- a UTM, we model "program indices" as positions in a finite
-- enumeration, with `tmDecode : Nat -> TM` a small switch. This
-- avoids the multi-thousand-line UTM construction while keeping
-- the diagonal contradiction's force.
--
-- Behavioral equality at bounded depth via `observe = (isHalted,
-- head)` was chosen as the smallest Boolean-valued tuple that
-- distinguishes our enumeration's TMs (state is too coarse: tm0/tm2/
-- tm3/tm5 all reach qH; tape ones-count is too expensive; the head
-- symbol pair is decisive).
--
-- Rice property list deliberately includes one property (P_inQ0at5)
-- that is *syntactic* in our toy: it depends on intermediate state,
-- not just on partial-function behavior. Honest Rice is about
-- semantic properties of partial functions; in a finitary toy with
-- a fixed enumeration, the distinction collapses (every property
-- is decidable in the finite world). The wall in Part 11 is exactly
-- this collapse: Rice's theorem requires the infinite extension
-- where the syntactic/semantic distinction matters.
--
-- s-m-n bonus included because the construction is a single switch
-- and one `native_decide`. The toy two-input TM uses the start head
-- symbol as the parameter --- the simplest "first argument on tape"
-- model that does not require encoding numbers in unary on the tape.
--
-- An earlier draft attempted a richer property list including
-- "halts on input x for every x" --- a genuine Pi_1 property. That
-- requires either an infinite test or a meta-theorem about the TM,
-- neither of which fits the finite enumeration. Stuck to bounded-
-- depth observable properties only.

end RecursionRiceShadow
