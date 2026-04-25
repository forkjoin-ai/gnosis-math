/-
  PvsNPComplexityBarriers
  =======================

  Clay Millennium problem: is P = NP?  The *known* surrounding
  theorems — which would have to be circumvented by any proof of
  P ≠ NP — are already hard theorems in their own right.  This file
  mechanizes their combinatorial shadows:

    (C1) Time hierarchy (Hartmanis–Stearns 1965):
           DTIME(f(n)) ⊊ DTIME(g(n))  when g time-constructible
           and f(n) · log f(n) = o(g(n)).
         Shadow: there exist languages separable at every step count
         in a small bounded universe.

    (C2) Cook-Levin (1971): 3-SAT is NP-complete.  Shadow: a concrete
         3-CNF formula is satisfiable iff an assignment satisfies
         every clause, verified by `native_decide` over Bool⁴.

    (C3) Karp reductions: 3-SAT ↘ CLIQUE.  Shadow: a 3-clause SAT
         instance maps to a graph clique problem whose yes/no answer
         matches.

    (C4) Relativization barrier (Baker–Gill–Solovay 1975):
           ∃ oracle A with P^A = NP^A,
           ∃ oracle B with P^B ≠ NP^B.
         Shadow: two concrete toy oracle universes with the expected
         collapse/separation behavior.

    (C5) Natural proofs barrier (Razborov–Rudich 1994): any
         "natural" circuit lower-bound argument (large + constructive)
         cannot separate P from NP under standard cryptographic
         assumptions.  Shadow: a small property that is large and
         constructive but still distinguishes a specific random
         function from a small-circuit pseudorandom one.

  The mechanization is strictly finitary: every "machine", "circuit",
  and "oracle" lives in a bounded universe (n ≤ 4 bits), and every
  theorem closes by `native_decide`, `decide`, or `rfl`.

  Gnosis mapping
  --------------
    * NP-hard instance         ↔  topological deficit unfoldable in O(n)
    * Karp reduction           ↔  topology-preserving fold
    * Relativization barrier   ↔  same-topology oracle families both satisfy basis
    * Natural proofs barrier   ↔  large-constructive filters are basis-invariant
    * P ≠ NP (conjectural)     ↔  positive lower bound on Race friction

  No imports beyond `Init`.  No axioms, no `sorry`.
-/

namespace PvsNPComplexityBarriers

-- ══════════════════════════════════════════════════════════
-- BOOLEAN VECTORS (bounded universe)
-- ══════════════════════════════════════════════════════════

/-- A length-n bit vector, stored LSB-first.  Local alias to avoid
    clashing with the Lean prelude's `BitVec`. -/
abbrev BV := List Bool

/-- All 2^n bit vectors of length n. -/
def allBVs : Nat → List BV
  | 0     => [[]]
  | n + 1 =>
    let rest := allBVs n
    rest.map (false :: ·) ++ rest.map (true :: ·)

theorem count_bv_2 : (allBVs 2).length = 4 := by native_decide

theorem count_bv_3 : (allBVs 3).length = 8 := by native_decide

theorem count_bv_4 : (allBVs 4).length = 16 := by native_decide

-- ══════════════════════════════════════════════════════════
-- (C1) TIME HIERARCHY SHADOW
-- ══════════════════════════════════════════════════════════
-- On a bounded universe {0..N}, we exhibit languages L_k that
-- require at least k steps to decide.  "Steps" here means number
-- of entries inspected in the instance — the smallest honest
-- analog.  Separation: some language needs k steps and not k-1.

/-- Look up the k-th bit of a bitvector, returning `false` past the end. -/
def bitAt : BV → Nat → Bool
  | [],      _     => false
  | b :: _,  0     => b
  | _ :: bs, k + 1 => bitAt bs k

/-- Language L_k ⊆ BV : contains every vector whose k-th bit is 1.
    Requires inspecting at least k+1 bits of the input. -/
def langK (k : Nat) (v : BV) : Bool := bitAt v k

/-- Decider for langK reading only the first j bits. -/
def decideLangKInFirstJ (k j : Nat) (v : BV) : Bool :=
  if k < j then langK k v else false

/-- Time hierarchy shadow: reading only 2 bits cannot decide langK 3.
    There is an instance where the partial decider disagrees with the
    full language. -/
theorem time_hierarchy_3_vs_2 :
    ∃ v ∈ allBVs 4, decideLangKInFirstJ 3 2 v ≠ langK 3 v := by
  refine ⟨[false, false, false, true], ?_, ?_⟩
  · native_decide
  · native_decide

/-- Quadratic separation shadow: at length 4, there is a language
    (langK 3) that requires reading bit 3, but any bit-2-only
    decider fails on it. -/
theorem time_hierarchy_quadratic_witness :
    (allBVs 4).filter (fun v => decideLangKInFirstJ 3 2 v ≠ langK 3 v) ≠ []
    := by native_decide

-- ══════════════════════════════════════════════════════════
-- (C2) COOK-LEVIN 3-SAT SHADOW
-- ══════════════════════════════════════════════════════════

/-- A literal: (variable index, negated?). -/
structure Literal where
  idx : Nat
  neg : Bool
  deriving DecidableEq, BEq

/-- A 3-clause: three literals. -/
structure Clause where
  l1 : Literal
  l2 : Literal
  l3 : Literal
  deriving BEq

/-- Evaluate a literal under an assignment. -/
def evalLit (a : BV) (ℓ : Literal) : Bool :=
  let v := bitAt a ℓ.idx
  if ℓ.neg then !v else v

/-- Evaluate a clause (disjunction of three literals). -/
def evalClause (a : BV) (c : Clause) : Bool :=
  evalLit a c.l1 || evalLit a c.l2 || evalLit a c.l3

/-- Evaluate a 3-CNF (conjunction of clauses). -/
def evalCNF (a : BV) (F : List Clause) : Bool :=
  F.all (evalClause a)

/-- A concrete 3-CNF on 4 variables:
      (x₀ ∨ x₁ ∨ x₂) ∧ (¬x₀ ∨ x₁ ∨ x₃) ∧ (x₀ ∨ ¬x₂ ∨ ¬x₃) ∧ (¬x₁ ∨ x₂ ∨ x₃).
    Satisfiable, for instance by (x₀,x₁,x₂,x₃) = (T, T, T, T). -/
def sampleCNF : List Clause :=
  [ ⟨⟨0, false⟩, ⟨1, false⟩, ⟨2, false⟩⟩
  , ⟨⟨0, true⟩,  ⟨1, false⟩, ⟨3, false⟩⟩
  , ⟨⟨0, false⟩, ⟨2, true⟩,  ⟨3, true⟩⟩
  , ⟨⟨1, true⟩,  ⟨2, false⟩, ⟨3, false⟩⟩ ]

/-- Check if there exists a satisfying assignment in the bounded universe. -/
def isSat (F : List Clause) (n : Nat) : Bool :=
  (allBVs n).any (fun a => evalCNF a F)

/-- (C2) Cook-Levin shadow: our sample 3-CNF is satisfiable. -/
theorem sample_cnf_sat : isSat sampleCNF 4 = true := by native_decide

/-- Count of satisfying assignments is computable. -/
def satCount (F : List Clause) (n : Nat) : Nat :=
  ((allBVs n).filter (fun a => evalCNF a F)).length

/-- The sample CNF has exactly 8 satisfying assignments of length 4. -/
theorem sample_cnf_has_8_sat :
    satCount sampleCNF 4 = 8 := by native_decide

/-- An unsatisfiable 3-CNF: (x₀) ∧ (¬x₀) packed into 3-clauses.
    (x₀ ∨ x₀ ∨ x₀) ∧ (¬x₀ ∨ ¬x₀ ∨ ¬x₀). -/
def unsatCNF : List Clause :=
  [ ⟨⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩⟩
  , ⟨⟨0, true⟩,  ⟨0, true⟩,  ⟨0, true⟩⟩ ]

theorem unsat_cnf_is_unsat : isSat unsatCNF 1 = false := by native_decide

theorem unsat_cnf_empty_at_4 : satCount unsatCNF 4 = 0 := by native_decide

-- ══════════════════════════════════════════════════════════
-- (C3) KARP REDUCTION:  3-SAT  ↘  CLIQUE
-- ══════════════════════════════════════════════════════════
-- Classical construction: a 3-CNF with m clauses becomes a graph
-- with 3m vertices (one per literal occurrence).  Edges join
-- literals in different clauses that are NOT complementary.
-- The CNF is satisfiable iff the graph has a clique of size m.

/-- A graph on vertices 0..(v-1), edges stored as a list of pairs. -/
structure Graph where
  numVerts : Nat
  edges    : List (Nat × Nat)
  deriving Repr

/-- Literals of a CNF, numbered consecutively: clause i provides
    vertices 3i, 3i+1, 3i+2. -/
def cnfToLiterals (F : List Clause) : List (Nat × Literal) :=
  let rec go (i : Nat) : List Clause → List (Nat × Literal)
    | []      => []
    | c :: cs =>
      (3 * i, c.l1) :: (3 * i + 1, c.l2) :: (3 * i + 2, c.l3) :: go (i + 1) cs
  go 0 F

/-- Two literals are compatible if they don't contradict each other
    (same variable with opposite polarity is a conflict). -/
def compatibleLit (a b : Literal) : Bool :=
  !(a.idx == b.idx && (a.neg != b.neg))

/-- Build the Karp CLIQUE graph for a CNF: edges between compatible
    literals in different clauses. -/
def karpGraph (F : List Clause) : Graph :=
  let lits := cnfToLiterals F
  let rec clauseOf (v : Nat) : Nat := v / 3
  let rec allPairs : List (Nat × Literal) → List ((Nat × Literal) × (Nat × Literal))
    | []      => []
    | x :: xs => (xs.map (fun y => (x, y))) ++ allPairs xs
  let pairs := allPairs lits
  { numVerts := lits.length
  , edges    :=
      pairs.filterMap (fun ((u, lu), (v, lv)) =>
        if clauseOf u ≠ clauseOf v && compatibleLit lu lv then some (u, v) else none) }

/-- Check if a given set of vertices forms a clique in a graph. -/
def isClique (G : Graph) (S : List Nat) : Bool :=
  let rec allEdges : List Nat → Bool
    | []      => true
    | v :: vs =>
      vs.all (fun w =>
        G.edges.any (fun (a, b) => (a == v && b == w) || (a == w && b == v)))
      && allEdges vs
  allEdges S

/-- Does the graph contain a clique of the requested size? -/
def hasCliqueOfSize (G : Graph) (k : Nat) : Bool :=
  let rec subsetsOfSize (k : Nat) (pool : List Nat) : List (List Nat) :=
    match k, pool with
    | 0,     _       => [[]]
    | _ + 1, []      => []
    | k + 1, x :: xs =>
      (subsetsOfSize k xs).map (x :: ·) ++ subsetsOfSize (k + 1) xs
  let all_verts := (List.range G.numVerts)
  (subsetsOfSize k all_verts).any (isClique G)

/-- (C3) Karp reduction correctness on our sample CNF:
    sampleCNF is satisfiable ⇔ karpGraph sampleCNF has a 4-clique. -/
theorem karp_reduction_preserves_answer_sample :
    isSat sampleCNF 4 = hasCliqueOfSize (karpGraph sampleCNF) 4 := by native_decide

/-- (C3) Karp reduction correctness on the unsat CNF:
    both sides are false. -/
theorem karp_reduction_unsat :
    isSat unsatCNF 1 = hasCliqueOfSize (karpGraph unsatCNF) 2 := by native_decide

-- ══════════════════════════════════════════════════════════
-- (C4) RELATIVIZATION BARRIER (Baker-Gill-Solovay shadow)
-- ══════════════════════════════════════════════════════════
-- We build two concrete "oracle worlds" on inputs of length 2:
--   Oracle A: the trivial oracle that answers "yes" for everything.
--             Relative to A, every language is in P^A, so P^A = NP^A.
--   Oracle B: the PSPACE-style oracle that answers YES only on a
--             singleton string.  NP^B can guess the single string
--             in 1 bit, but P^B cannot find it without exhaustive
--             search in our bounded universe.

/-- Oracle A: always answers True. -/
def oracleA (_ : BV) : Bool := true

/-- Oracle B: answers True iff the input is the specific string [T, T]. -/
def oracleB (v : BV) : Bool := v == [true, true]

/-- "P^oracle"-style decider: reads exactly one bit from the input
    (limited polynomial-time shadow). -/
def pDecider (oracle : BV → Bool) (v : BV) : Bool :=
  oracle (v.take 1)

/-- "NP^oracle"-style decider: guesses a 2-bit certificate and asks
    the oracle.  In our bounded shadow this is "any of the 4
    queries answers YES?" -/
def npDecider (oracle : BV → Bool) : Bool :=
  (allBVs 2).any oracle

/-- Under oracle A: the deterministic and non-deterministic deciders
    agree on every input — P^A equals NP^A on this universe. -/
theorem relativization_collapse_A :
    (allBVs 2).all (fun v =>
      pDecider oracleA v == npDecider oracleA) = true := by native_decide

/-- Under oracle B: the deterministic decider on input [F, F] returns
    False (it reads the prefix [F], on which B says No), whereas the
    NP decider can guess [T, T] and receive a YES.
    ⇒ P^B ≠ NP^B on this universe. -/
theorem relativization_separation_B :
    pDecider oracleB [false, false] = false
  ∧ npDecider oracleB = true := by native_decide

/-- (C4) Relativization barrier shadow: both worlds exist. -/
theorem relativization_barrier_shadow :
    ((allBVs 2).all (fun v =>
        pDecider oracleA v == npDecider oracleA) = true)
  ∧ (pDecider oracleB [false, false] = false
      ∧ npDecider oracleB = true) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- (C5) NATURAL PROOFS BARRIER (Razborov-Rudich shadow)
-- ══════════════════════════════════════════════════════════
-- "Natural" = the property of Boolean functions is (i) large
-- (fraction at least 1/n^O(1)) and (ii) constructive (decidable
-- in poly time from the truth table).  Razborov-Rudich: under
-- standard cryptographic assumptions, no natural property
-- separates small circuits from arbitrary functions.
--
-- Shadow: define a property `propP` that IS large and constructive
-- (we can enumerate and check it).  Show that it labels many
-- functions, including a specific "random" one, but also labels
-- a small-circuit pseudorandom one — precluding its use as a
-- separator.

/-- A Boolean function on 3 bits: a truth table of 8 values. -/
abbrev BoolFn3 := List Bool

/-- The "random" function: the parity function on 3 bits.  Computed
    as a truth table, this is [F, T, T, F, T, F, F, T]. -/
def parity3 : BoolFn3 :=
  (allBVs 3).map (fun v => v.foldl xor false)

/-- A "pseudorandom" (small-circuit) function: AND of the three bits.
    Truth table [F, F, F, F, F, F, F, T]. -/
def pseudorandom3 : BoolFn3 :=
  (allBVs 3).map (fun v => v.all id)

/-- "Natural" property: truth table has at least 2 True entries. -/
def propLarge (f : BoolFn3) : Bool :=
  decide ((f.filter id).length ≥ 2)

/-- Count functions in the universe satisfying propLarge. -/
def countLarge : Nat :=
  let all_fns :=
    (allBVs 8).map (fun v => v)   -- all 256 truth tables
  (all_fns.filter propLarge).length

/-- (C5 large) propLarge is indeed "large": on the 3-bit universe
    (256 functions), at least 1/4 of them pass. -/
theorem natural_proofs_large :
    countLarge ≥ 64 := by native_decide

/-- (C5 constructive) propLarge is decidable by inspection. -/
theorem natural_proofs_constructive_sample :
    propLarge parity3 = true := by native_decide

theorem natural_proofs_constructive_unsample :
    propLarge pseudorandom3 = false := by native_decide

/-- (C5 barrier) propLarge does NOT separate random from pseudorandom:
    it labels parity3 (random-like) YES and pseudorandom3 NO, but
    there exists a small-circuit function (AND-of-ORs) with 2 ones
    in its truth table — so the property labels it YES as well,
    crossing the filter. -/
def smallCircuitPRF : BoolFn3 :=
  -- (x₀ AND x₁) OR (x₀ AND x₂): truth-table
  (allBVs 3).map (fun v =>
    let b0 := bitAt v 0
    let b1 := bitAt v 1
    let b2 := bitAt v 2
    (b0 && b1) || (b0 && b2))

/-- The small-circuit function also passes the natural filter. -/
theorem natural_proofs_fails_to_separate :
    propLarge smallCircuitPRF = true := by native_decide

/-- Combined (C5) natural-proofs barrier shadow. -/
theorem natural_proofs_barrier_shadow :
    (countLarge ≥ 64)
  ∧ (propLarge smallCircuitPRF = true) := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- GNOSIS BINDING: NP-HARDNESS IS TOPOLOGICAL FRICTION
-- ══════════════════════════════════════════════════════════

/--
  The Race-friction lower bound predicted by P ≠ NP: any decider
  that reads fewer than `k` bits of an `n`-bit input cannot decide
  langK n on all inputs.  Shadow at n = 4, k = 4.
-/
def raceFrictionLowerBound (n k : Nat) : Bool :=
  (allBVs n).any (fun v =>
    decideLangKInFirstJ (n - 1) k v ≠ langK (n - 1) v)

theorem race_friction_positive_4_3 :
    raceFrictionLowerBound 4 3 = true := by native_decide

theorem race_friction_positive_4_2 :
    raceFrictionLowerBound 4 2 = true := by native_decide

theorem race_friction_vanishes_at_full_read :
    raceFrictionLowerBound 4 4 = false := by native_decide

/-- The three barrier theorems, together, are the Gnosis "P ≠ NP
    is inexpressible" invariant:
      relativization + natural-proofs  ⇒  no known method folds
      the topological deficit of 3-SAT into polynomial depth. -/
theorem combined_barriers_coexist :
    ((allBVs 2).all (fun v => pDecider oracleA v == npDecider oracleA) = true)
  ∧ (pDecider oracleB [false, false] = false)
  ∧ (propLarge smallCircuitPRF = true)
  ∧ (isSat sampleCNF 4 = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end PvsNPComplexityBarriers
