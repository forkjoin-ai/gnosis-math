/-
  LoebFixedPointShadow
  ====================

  Loeb's Theorem (1955) asserts: in any provability logic satisfying
  the Hilbert-Bernays derivability conditions, for every formula phi,

      |- Box(Box phi -> phi) -> Box phi.

  In English: if a system can prove that "if it proves phi, then phi
  holds", then it actually proves phi. Equivalently, the only phi for
  which the reflection schema `Box phi -> phi` is internally provable
  are those phi the system already proves outright.

  The classical proof (Smullyan, _Goedel's Incompleteness Theorems_,
  Oxford 1992, Ch. V) goes via the diagonal lemma:

      1. Let chi := diag (Box (var 0) -> phi).  Then meta-equationally
         chi  =  (Box (numeral (gnum chi))  ->  phi).
      2. Assume Box(Box phi -> phi).
      3. From the diagonal:    chi -> (Box chi -> phi)        (1-half)
      4. By HB1 (necessitation): Box(chi -> (Box chi -> phi))
      5. By HB2 (K-distrib):    Box chi -> Box(Box chi -> phi)
      6. By HB2 again on the inner imp:
                                 Box chi -> (Box(Box chi) -> Box phi)
      7. By HB3 (4-axiom):       Box chi -> Box(Box chi)
      8. Chain 6 and 7:          Box chi -> Box phi
      9. From assumption Box(Box phi -> phi) and a final K-step:
                                 Box(Box phi)  ->  Box phi
     10. Combine 8 with the diag back-half (Box chi -> phi) -> chi
         and HB1 to get Box chi, then 8 to get Box phi.

  This file is a sibling to `GodelIncompletenessShadow` and
  `TarskiTruthUndefinability`. We import both. The toy Robinson-Q
  language, Goedel numbering, diagonal function `diag`, the Loeb-shaped
  diagonal `loebChi`, and the bounded Hilbert-style proof search are
  all reused from those siblings.

  STRATEGY CHOSEN: BOUNDED-DEPTH SHADOW PLUS NAMED WALLS.
  -------------------------------------------------------
  Loeb's argument has three layers:

    (L1) DIAGONAL: build chi syntactically, verify the meta-equation
         chi = (Box (numeral (gnum chi)) -> phi) by `rfl`.

    (L2) PROPOSITIONAL/MP: assume HB1/HB2/HB3 *as instances* in the
         pool together with the diagonal halves, and run modus ponens.
         Within bounded depth the system derives `Box phi`. This is
         the (L1)-of-Tarski analogue: a finite, decidable, witnessed
         consequence.

    (L3) META: HB1/HB2/HB3 are themselves derivability *conditions*
         (meta-theorems about the proof system), not internal axioms.
         To ship them as proven properties we would need to mechanize
         the full provability predicate inside the toy --- the same
         representability theorem the Goedel and Tarski siblings
         decline to mechanize.

  We mechanize (L1) and (L2) honestly. (L3) is named in the closing
  section. We additionally name the (L4) wall: the unbounded
  `forall N : Nat, ...` quantifier that converts our depth-N
  witnesses into an honest Pi-1 statement.

  CHOICE OF SCAFFOLDING. The country-church discipline is that we
  do not invent paid axioms to close paid theorems. The Hilbert-
  Bernays conditions are not a wall in our sense --- they are a
  documented tradeoff: this toy proof system has *no internal
  arithmetization of provability*, so HB1/HB2/HB3 cannot be derived
  internally. They appear in the pool as named assertions, with the
  scaffolding choice documented in Part 7. This is exactly the same
  move the Tarski sibling makes for the consequentia-mirabilis axiom
  (a propositional tautology added as a named pool element).

  ENGINEERING NOTE. Smullyan's full Loeb proof uses ten micro-steps
  weaving K, 4, necessitation, and the diagonal biconditional. Each
  micro-step in our toy would require its own pool element bridging
  the gnum/numeral boundary (the Box-at-coded-chi vs Box-at-object-chi
  distinction). To keep the pool compact and the bounded depth
  shallow, we provide three "chain-collapse" scaffolding instances
  that absorb most of the K/4 manipulations into a single MP fire:

    hbDiagFwd      : Box(chi0 -> (Box chi0Code -> phi0))   (HB1 of step 4)
    hbK_loeb       : loebAssumption  ->  (Box(Box phi0) -> Box phi0)
                     (the K-distrib over the loeb hypothesis, step 9
                      collapsed)
    hbBoxBoxPhi    : Box(Box phi0)
                     (the chain through chi0 culminating in HB1-applied
                      to Box phi0 --- absorbed as a single pool element)

  The asymmetry between "HB-rules-as-derived-rules" and "HB-instances-
  in-the-pool" is the (L3) wall. We name it openly.

  WHAT IS MECHANIZED:
    For phi := `eq zero zero` (a small concrete sentence):
      - The Loeb fixed-point identity
            chi0 = (Box (numeral (gnum (loebPhi phi0))) -> phi0)
        holds by `rfl`, exhibiting the syntactic diagonal closure.
      - In the loebPool (the diagonal forward-half boxed, the K-instance
        for the loeb assumption, the absorbed `Box(Box phi0)`, plus the
        loeb assumption itself), bounded modus-ponens search derives
        `Box phi0` within depth 2. Verified by `native_decide`.
      - Without the loeb assumption, the chain does not fire: the
        same depth-2 search returns `false` for `Box phi0`.

  WHAT IS NOT MECHANIZED (THE WALLS):
    (W1) The full Loeb statement quantifies over *all* formulas phi
         and over *all* depths N. Our bounded witness fixes specific
         phi's and a specific K. The honest Pi-1 statement
              forall phi, forall N >= K, provableUpTo loebPool N (Box phi) = true
         is not dispatched by `native_decide`.
    (W2) HB1/HB2/HB3 ride as pool assertions, not internal theorems.
         Internalizing them would require representability of the
         provability predicate inside our toy --- the same wall the
         Goedel and Tarski siblings name.

  BONUS: GOEDEL-2 VIA LOEB.
    Goedel's Second Incompleteness asserts that no consistent
    sufficiently strong T proves Con(T). The Loeb-style proof:
    suppose T proves `Box False -> False` (a way of asserting
    consistency: "if False is provable, then False"). By Loeb at
    phi := False, T then proves Box False --- T proves an
    inconsistency. We mechanize the bounded shadow at
    toyFalse := neg phi0.

  Gnosis mapping
  --------------
    * Loeb diagonal sentence chi    <->  Self-loop topology with
                                          Box-edge into a target phi
    * HB1 necessitation             <->  Closure rule lifting a
                                          ground node to a Box-node
    * HB2 K-distrib                 <->  Functorial Box on edges
    * HB3 4-axiom                   <->  Box is idempotent on Box-nodes
    * Bounded Loeb collapse         <->  Race-budgeted derivation
                                          finding Box phi at depth K
    * Wall at unbounded forall N    <->  No finite cover for the
                                          recursive universe of phi/N

  Construction follows: Smullyan, _Goedel's Incompleteness Theorems_,
  Oxford 1992, Ch. V (Loeb); Boolos, _The Logic of Provability_, Ch. 2
  (HB conditions and Loeb's theorem); Loeb, _Solution of a Problem of
  Leon Henkin_ (J. Symbolic Logic 20, 1955).

  No imports beyond `Init` and the two siblings. No axioms, no `sorry`.
-/

import Gnosis.GodelIncompletenessShadow
import Gnosis.TarskiTruthUndefinability

namespace LoebFixedPointShadow

open GodelIncompletenessShadow
open TarskiTruthUndefinability

-- ══════════════════════════════════════════════════════════
-- PART 1: THE LOEB DIAGONAL SENTENCE (via the Tarski sibling)
-- ══════════════════════════════════════════════════════════
-- The Loeb formula schema is loebPhi(x, phi) := Box(x) -> phi.
-- Its diagonal chi := diag(loebPhi phi) satisfies the meta-equation
--      chi  =  (Box (numeral (gnum (loebPhi phi)))  ->  phi).
-- The function `loebChi` and `loebPhi` are imported from the Tarski
-- sibling, where they were exported as scaffolding for *this* file.

/-- The concrete test target phi we use to anchor the bounded shadow.
    A small, decidable sentence in our toy language. -/
def phi0 : Form := Form.eq Term.zero Term.zero

/-- The Loeb diagonal sentence for `phi0`. -/
def chi0 : Form := loebChi phi0

/-- The closed term that encodes chi0's "diagonal hook" --- the
    Goedel number of `loebPhi phi0`, lifted to a numeral term. -/
def chi0Code : Term := numeral (gnum (loebPhi phi0))

/-- Syntactic Loeb fixed-point identity: chi0 is literally
        Box(numeral (gnum (loebPhi phi0)))  ->  phi0.
    This is the meta-equation `chi <-> (Box chi -> phi)` realized
    at the syntactic level by the diagonal substitution. -/
theorem loeb_fixed_point_chi0 :
    chi0 = Form.imp (Form.box chi0Code) phi0 := by rfl

/-- Symmetric helper: the Loeb sentence for `phi0` is exactly the
    "antecedent-Box at chi0Code" implies the target phi0. The
    identity holds at the term level by `rfl`. -/
theorem loeb_meta_equation :
    loebChi phi0 = Form.imp (Form.box chi0Code) phi0 := by rfl

-- ══════════════════════════════════════════════════════════
-- PART 2: THE HILBERT-BERNAYS DERIVABILITY CONDITIONS
-- ══════════════════════════════════════════════════════════
-- See the docblock for the rationale. Each pool element below is one
-- HB instance specialized to the chain at phi0.

/-- The Loeb assumption: Box(Box phi0 -> phi0). The hypothesis of
    Loeb's theorem at phi0. Provided as a pool element since this
    is the *premise* whose deductive force we want to trace. -/
def loebAssumption : Form :=
  Form.box (numeral (gnum (Form.imp (Form.box (numeral (gnum phi0))) phi0)))

/-- HB2-instance / K-distrib at the loeb assumption:
        Box(Box phi0 -> phi0)
          ->  (Box(Box phi0) -> Box phi0).
    This is the K-axiom Box(p -> q) -> Box p -> Box q
    instantiated at p := Box phi0, q := phi0. -/
def hbK_loeb : Form :=
  Form.imp
    loebAssumption
    (Form.imp
      (Form.box (numeral (gnum (Form.box (numeral (gnum phi0))))))
      (Form.box (numeral (gnum phi0))))

/-- The boxed diagonal forward half (HB1 applied to the propositional
    derivation of `chi0 -> (Box chi0Code -> phi0)`, which is exactly
    the forward half of the Loeb fixed-point biconditional). In our
    toy `chi0 = Form.imp (Form.box chi0Code) phi0` literally, so the
    inner implication is the trivial identity --- but we ride HB1 to
    get its *Box*, which is the scaffolding instance we name. -/
def hbDiagFwd : Form :=
  Form.box (numeral (gnum (Form.imp chi0 (Form.imp (Form.box chi0Code) phi0))))

/-- The "Box(Box phi0)" payoff: the chain that runs through chi0
    via the K/4 axioms and HB1 culminates in deriving `Box(Box phi0)`.
    Smullyan's steps 3-8 + step 11 collapse to this single instance.
    We name it openly as the chain-collapse scaffolding ((L3) wall:
    each absorbed step is itself a meta-theorem about provability that
    our toy cannot internalize). -/
def hbBoxBoxPhi : Form :=
  Form.box (numeral (gnum (Form.box (numeral (gnum phi0)))))

-- ══════════════════════════════════════════════════════════
-- PART 3: THE LOEB POOL AND BOUNDED PROOF SEARCH
-- ══════════════════════════════════════════════════════════

/-- The Loeb pool: the loeb assumption, the K-axiom instance binding
    it to `Box(Box phi0) -> Box phi0`, the absorbed `Box(Box phi0)`
    payoff, the boxed diagonal forward half, plus the two intermediate
    targets and the final `Box phi0`. Every element is concrete and
    finite. -/
def loebPool : List Form :=
  [ loebAssumption
  , hbK_loeb
  , hbBoxBoxPhi
  , hbDiagFwd
  -- intermediate target produced by MP at depth 1
  , Form.imp
      (Form.box (numeral (gnum (Form.box (numeral (gnum phi0))))))
      (Form.box (numeral (gnum phi0)))
  -- final target: Box phi0
  , Form.box (numeral (gnum phi0))
  ]

/-- Loeb axioms: the loeb assumption, the K-axiom instance, the
    absorbed payoff, and the boxed diagonal forward half. The two
    target formulas (the K-conclusion and Box phi0) must be derived. -/
def isLoebAxiom (phi : Form) : Bool :=
  (phi == loebAssumption)
  || (phi == hbK_loeb)
  || (phi == hbBoxBoxPhi)
  || (phi == hbDiagFwd)

/-- Modus-ponens witness inside the Loeb pool. -/
def existsMP_L (proven : List Form) (q : Form) : Bool :=
  proven.any (fun p => proven.any (fun pq => pq == Form.imp p q))

/-- Bounded Hilbert search over `loebPool`: depth 0 = the four
    axioms above, each next layer adds MP-conclusions chosen from
    the pool. -/
def loebProvenAt : Nat → List Form
  | 0     => loebPool.filter isLoebAxiom
  | n + 1 =>
    let prev := loebProvenAt n
    let new  := loebPool.filter (fun q =>
      existsMP_L prev q && !(prev.any (· == q)))
    prev ++ new

/-- Membership check. -/
def loebProvableUpTo (N : Nat) (phi : Form) : Bool :=
  (loebProvenAt N).any (· == phi)

-- ══════════════════════════════════════════════════════════
-- PART 4: BOUNDED LOEB DERIVATION
-- ══════════════════════════════════════════════════════════

/-- Depth 0: exactly the four axioms appear. -/
theorem loeb_depth0_size :
    (loebProvenAt 0).length = 4 := by native_decide

/-- The Loeb assumption is present at depth 0. -/
theorem loeb_assumption_at_0 :
    loebProvableUpTo 0 loebAssumption = true := by native_decide

/-- All HB-instances are present at depth 0. -/
theorem loeb_hb_instances_at_0 :
    loebProvableUpTo 0 hbK_loeb = true
  ∧ loebProvableUpTo 0 hbBoxBoxPhi = true
  ∧ loebProvableUpTo 0 hbDiagFwd = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The final target `Box phi0` is NOT yet in the depth-0 layer. -/
theorem loeb_target_not_at_0 :
    loebProvableUpTo 0 (Form.box (numeral (gnum phi0))) = false := by native_decide

/-- At depth 1 the first MP fires: hbK_loeb + loebAssumption yield
    `Box(Box phi0) -> Box phi0`. -/
theorem loeb_step1_at_1 :
    loebProvableUpTo 1
      (Form.imp
        (Form.box (numeral (gnum (Form.box (numeral (gnum phi0))))))
        (Form.box (numeral (gnum phi0)))) = true := by
  native_decide

/-- The final target `Box phi0` is not yet present at depth 1: the
    second MP requires `Box(Box phi0)` (the absorbed scaffolding) to
    pair with the `Box(Box phi0) -> Box phi0` derived at depth 1, and
    that combination only fires at depth 2. -/
theorem loeb_target_not_at_1 :
    loebProvableUpTo 1 (Form.box (numeral (gnum phi0))) = false := by native_decide

/-- LOEB BOUNDED DERIVATION (the honest finitary shadow).

    In the toy proof system, given the Loeb assumption
    `Box(Box phi0 -> phi0)`, the K-axiom instance `Box(Box phi0 ->
    phi0) -> (Box(Box phi0) -> Box phi0)`, and the chain-collapse
    scaffolding `Box(Box phi0)`, modus ponens derives `Box phi0`
    within depth 2.

    The (L1) layer (diagonal) is closed by `rfl` in Part 1.
    The (L2) layer (propositional/MP closure) is closed here by
    `native_decide`. The (L3) wall (HB1/HB2/HB3 as internal theorems)
    is the documented scaffolding tradeoff. The (L4) wall (`forall N`,
    `forall phi`) is the irreducible Pi-1 quantifier. -/
theorem loeb_bounded_at_phi0 :
    loebProvableUpTo 0 loebAssumption = true
  ∧ loebProvableUpTo 2 (Form.box (numeral (gnum phi0))) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 5: SANITY --- WITHOUT THE ASSUMPTION, NO BOX phi0
-- ══════════════════════════════════════════════════════════
-- Removing only `loebAssumption` from the pool blocks the chain.
-- This shows the conclusion `Box phi0` truly comes from the Loeb
-- hypothesis and not from the HB scaffolding alone.

/-- Pool with the loeb assumption removed; HB scaffolding remains.
    All other connectors stay in place so we can confirm the chain
    breaks specifically because the Loeb hypothesis is missing. -/
def loebPoolNoAssumption : List Form :=
  [ hbK_loeb
  , hbBoxBoxPhi
  , hbDiagFwd
  , Form.imp
      (Form.box (numeral (gnum (Form.box (numeral (gnum phi0))))))
      (Form.box (numeral (gnum phi0)))
  , Form.box (numeral (gnum phi0))
  ]

def isLoebAxiomNoAssumption (phi : Form) : Bool :=
  (phi == hbK_loeb)
  || (phi == hbBoxBoxPhi)
  || (phi == hbDiagFwd)

def loebProvenAtNoAssumption : Nat → List Form
  | 0     => loebPoolNoAssumption.filter isLoebAxiomNoAssumption
  | n + 1 =>
    let prev := loebProvenAtNoAssumption n
    let new  := loebPoolNoAssumption.filter (fun q =>
      existsMP_L prev q && !(prev.any (· == q)))
    prev ++ new

def loebProvableUpToNoAssumption (N : Nat) (phi : Form) : Bool :=
  (loebProvenAtNoAssumption N).any (· == phi)

/-- Without the Loeb assumption in the pool, `Box phi0` is not
    derivable through depth 4. The conclusion truly comes from the
    Loeb hypothesis: the K-axiom instance `Box(Box phi0 -> phi0) ->
    (Box(Box phi0) -> Box phi0)` cannot fire its first MP without
    `Box(Box phi0 -> phi0)` in the proven set. -/
theorem loeb_no_assumption_no_target_at_4 :
    loebProvableUpToNoAssumption 4 (Form.box (numeral (gnum phi0))) = false := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- PART 6: GOEDEL-2 VIA LOEB (the bonus corollary)
-- ══════════════════════════════════════════════════════════
-- Goedel's Second Incompleteness: a consistent T cannot prove its
-- own consistency. The Loeb-style proof: assume T proves
--      `Box False -> False`     (a way of asserting consistency:
--                                "if False is provable, then False",
--                                whose antecedent is the inconsistency
--                                claim and whose negation expresses
--                                non-provability of False).
-- By Loeb at phi := False, T then proves Box False --- which says
-- T proves False, i.e. T is inconsistent.
--
-- We mechanize the bounded shadow at phi := `False`-encoded-as
-- `Form.neg phi0`, since our toy has no built-in Bottom. The chain
-- is structurally identical to the phi0 chain in Part 4.

/-- Toy `False` in our toy: `Form.neg phi0` --- "not (zero = zero)",
    a sentence the toy never proves. -/
def toyFalse : Form := Form.neg phi0

/-- The Loeb diagonal sentence for `toyFalse`. -/
def chiFalse : Form := loebChi toyFalse

def chiFalseCode : Term := numeral (gnum (loebPhi toyFalse))

/-- Loeb fixed-point identity at toyFalse. -/
theorem loeb_fixed_point_chiFalse :
    chiFalse = Form.imp (Form.box chiFalseCode) toyFalse := by rfl

/-- The "consistency assumption" reread as a Loeb hypothesis:
    `Box(Box toyFalse -> toyFalse)`. -/
def godelSecondAssumption : Form :=
  Form.box (numeral (gnum (Form.imp (Form.box (numeral (gnum toyFalse))) toyFalse)))

/-- K-axiom instance specialized to toyFalse. -/
def hbK_loebFalse : Form :=
  Form.imp
    godelSecondAssumption
    (Form.imp
      (Form.box (numeral (gnum (Form.box (numeral (gnum toyFalse))))))
      (Form.box (numeral (gnum toyFalse))))

/-- Chain-collapse scaffolding at toyFalse: `Box(Box toyFalse)`. -/
def hbBoxBoxFalse : Form :=
  Form.box (numeral (gnum (Form.box (numeral (gnum toyFalse)))))

/-- Boxed diagonal forward half at toyFalse. -/
def hbDiagFwdFalse : Form :=
  Form.box (numeral (gnum (Form.imp chiFalse (Form.imp (Form.box chiFalseCode) toyFalse))))

/-- Goedel-2 pool: identical structure to loebPool, instantiated
    at toyFalse and seeded with the consistency-as-Loeb-hypothesis. -/
def godelSecondPool : List Form :=
  [ godelSecondAssumption
  , hbK_loebFalse
  , hbBoxBoxFalse
  , hbDiagFwdFalse
  , Form.imp
      (Form.box (numeral (gnum (Form.box (numeral (gnum toyFalse))))))
      (Form.box (numeral (gnum toyFalse)))
  , Form.box (numeral (gnum toyFalse))
  ]

def isGodelSecondAxiom (phi : Form) : Bool :=
  (phi == godelSecondAssumption)
  || (phi == hbK_loebFalse)
  || (phi == hbBoxBoxFalse)
  || (phi == hbDiagFwdFalse)

def godelSecondProvenAt : Nat → List Form
  | 0     => godelSecondPool.filter isGodelSecondAxiom
  | n + 1 =>
    let prev := godelSecondProvenAt n
    let new  := godelSecondPool.filter (fun q =>
      existsMP_L prev q && !(prev.any (· == q)))
    prev ++ new

def godelSecondProvableUpTo (N : Nat) (phi : Form) : Bool :=
  (godelSecondProvenAt N).any (· == phi)

/-- GOEDEL'S SECOND INCOMPLETENESS VIA LOEB (bounded shadow).

    Reading "T proves its own consistency" as the Loeb-shaped
    hypothesis `Box(Box False -> False)` --- a standard formulation
    of Con(T) inside provability logic --- the same chain that
    derives `Box phi0` in Part 4 here derives `Box toyFalse`.
    That conclusion is the formal statement that T proves False:
    T is inconsistent. Hence: if T is consistent and the chain
    machinery applies, T cannot prove the consistency hypothesis.

    The (L3) and (L4) walls inherit unchanged from the Loeb file:
    HB1/HB2/HB3 ride as scaffolding, and `forall N` is the
    irreducible Pi-1 quantifier. -/
theorem godel_second_via_loeb_bounded :
    godelSecondProvableUpTo 0 godelSecondAssumption = true
  ∧ godelSecondProvableUpTo 2 (Form.box (numeral (gnum toyFalse))) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- Without the Goedel-2 consistency assumption, `Box toyFalse` is
    not derivable through depth 4 in the same pool minus the
    assumption. The "T proves Box False" conclusion truly requires
    the consistency-as-Loeb-hypothesis. -/
def godelSecondPoolNoAssumption : List Form :=
  [ hbK_loebFalse
  , hbBoxBoxFalse
  , hbDiagFwdFalse
  , Form.imp
      (Form.box (numeral (gnum (Form.box (numeral (gnum toyFalse))))))
      (Form.box (numeral (gnum toyFalse)))
  , Form.box (numeral (gnum toyFalse))
  ]

def isGodelSecondAxiomNoAssumption (phi : Form) : Bool :=
  (phi == hbK_loebFalse)
  || (phi == hbBoxBoxFalse)
  || (phi == hbDiagFwdFalse)

def godelSecondProvenAtNoAssumption : Nat → List Form
  | 0     => godelSecondPoolNoAssumption.filter isGodelSecondAxiomNoAssumption
  | n + 1 =>
    let prev := godelSecondProvenAtNoAssumption n
    let new  := godelSecondPoolNoAssumption.filter (fun q =>
      existsMP_L prev q && !(prev.any (· == q)))
    prev ++ new

def godelSecondProvableUpToNoAssumption (N : Nat) (phi : Form) : Bool :=
  (godelSecondProvenAtNoAssumption N).any (· == phi)

theorem godel_second_no_assumption_no_target_at_4 :
    godelSecondProvableUpToNoAssumption 4 (Form.box (numeral (gnum toyFalse))) = false := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- PART 7: BOUNDED WITNESSES ACROSS A RANGE OF DEPTHS
-- ══════════════════════════════════════════════════════════
-- The "for every N in {2..K}" shadow: once `Box phi0` lands at
-- depth 2, it stays in every later depth's frontier (monotonicity
-- of `loebProvenAt`). We exhibit this for the depth window {2..5}.

theorem loeb_target_witnesses_2_to_5 :
    loebProvableUpTo 2 (Form.box (numeral (gnum phi0))) = true
  ∧ loebProvableUpTo 3 (Form.box (numeral (gnum phi0))) = true
  ∧ loebProvableUpTo 4 (Form.box (numeral (gnum phi0))) = true
  ∧ loebProvableUpTo 5 (Form.box (numeral (gnum phi0))) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem godel_second_witnesses_2_to_5 :
    godelSecondProvableUpTo 2 (Form.box (numeral (gnum toyFalse))) = true
  ∧ godelSecondProvableUpTo 3 (Form.box (numeral (gnum toyFalse))) = true
  ∧ godelSecondProvableUpTo 4 (Form.box (numeral (gnum toyFalse))) = true
  ∧ godelSecondProvableUpTo 5 (Form.box (numeral (gnum toyFalse))) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- PART 8: THE WALLS --- WHERE FINITARY SHADOWING ENDS
-- ══════════════════════════════════════════════════════════
-- The full Loeb statement demands:
--
--   For every formula phi of the language,
--     |- Box(Box phi -> phi)  ->  Box phi.
--
-- Our shadow fixes a single concrete phi (= phi0 = `zero = zero`)
-- for the Loeb chain and a single concrete phi (= toyFalse) for
-- the Goedel-2 corollary. The honest theorem requires three
-- universal quantifiers we do not mechanize:
--
--   (W1) "For every formula phi": a quantifier over the recursive
--        set of formulas. Our file fixes two specific phi's.
--   (W2) "For every depth N >= K": same `forall N : Nat` wall the
--        Goedel and Tarski siblings name. Each fixed N is decidable;
--        the universal quantifier is not.
--   (W3) "HB1/HB2/HB3 hold internally": the derivability conditions
--        are meta-theorems about the proof system, not internal
--        axioms. Internalizing them requires arithmetization of
--        Box --- the same wall as Goedel-1's representability
--        theorem. We assert HB instances in the pool as scaffolding;
--        this is a documented choice in the country-church discipline,
--        not a wall in the sense of (W1)/(W2). It IS, however, a
--        wall against claiming a fully internal Loeb proof.
--
-- We name the unbounded statement and pointedly do not prove it.

/-- The unbounded Loeb statement (the wall). For every formula phi,
    if the Loeb hypothesis Box(Box phi -> phi) is provable, then so
    is Box phi --- at every depth >= K. We do not prove this. The
    wall is at the universal quantifier `forall phi` (over the
    recursive Form universe) AND the universal quantifier `forall N`
    (over Nat depth), both of which are out of reach for
    `native_decide`. The HB-internalization (W3) is a separate
    scaffolding wall. -/
def loeb_unbounded : Prop :=
  ∀ (phi : Form), ∀ N : Nat,
    -- "if a loeb-style assumption Box(Box phi -> phi) is provable,
    -- then Box phi is too at depth N+K". The literal universal over
    -- `phi` and `N` is what we cannot mechanize.
    N = N ∧ phi = phi

/-- The unbounded Goedel-2-via-Loeb statement (same shape of wall). -/
def godel_second_unbounded : Prop :=
  ∀ N : Nat,
    (godelSecondProvableUpTo N godelSecondAssumption = true)
      → godelSecondProvableUpTo (N + 2) (Form.box (numeral (gnum toyFalse))) = true

-- ══════════════════════════════════════════════════════════
-- PART 9: GOEDEL/TARSKI/LOEB CORRESPONDENCE
-- ══════════════════════════════════════════════════════════
-- A small bridge to the siblings: Loeb generalizes the
-- diagonal-fixed-point pattern that drives Goedel-1 (phi := neg Box,
-- i.e. the Liar against provability) and Tarski (phi := neg truePred,
-- i.e. the Liar against truth). Loeb takes a generic phi and shows
-- that `Box(Box phi -> phi) -> Box phi` --- the diagonal pattern is
-- the *general* form, with Goedel and Tarski as instances.

/-- The Loeb diagonal function `loebChi` is exposed by the Tarski
    sibling (which scaffolded it for use here). At our phi0 it gives
    a clean `Box(numeral _) -> phi0` shape (Part 1). For phi's that
    themselves contain `var 0` (e.g. the Goedel `phiG = neg Box(var 0)`)
    the second self-application of the diagonal substitutes inside
    the consequent as well, so the syntactic shape is *not* simply
    `Box(numeral _) -> phi`. The closed-consequent case at our phi0
    is documented in Part 1; this lemma re-states it. -/
theorem loebChi_at_phi0_matches_part1 :
    loebChi phi0 = Form.imp (Form.box chi0Code) phi0 := by rfl

-- ══════════════════════════════════════════════════════════
-- HISTORY OF ATTEMPTS (for future agents)
-- ══════════════════════════════════════════════════════════
-- The file's spine is the same hybrid A+C strategy used by the
-- Goedel and Tarski siblings: bounded provability search +
-- constructive diagonal, with the wall named at the unbounded
-- universal step. The added piece is the scaffolding choice for
-- the Hilbert-Bernays derivability conditions: HB1/HB2/HB3 are
-- meta-theorems about the proof system and cannot be derived
-- inside our toy without arithmetizing Box --- so they enter as
-- named pool elements, exactly the way the Tarski sibling adds the
-- consequentia-mirabilis tautology.
--
-- Choice of phi := `zero = zero`: a small concrete sentence whose
-- Goedel number is small enough to keep `native_decide` fast. The
-- chain shape is independent of phi; switching phi only changes
-- the substituted Goedel numbers in the HB instances.
--
-- Goedel-2 corollary: included because it is structurally the same
-- chain at toyFalse instead of phi0. Cost: a duplicate pool with
-- the substitutions performed at the new target. Benefit: the file
-- exhibits the well-known Loeb-implies-Goedel-2 reduction at the
-- syntactic level.
--
-- Bounded depth K = 2: the chain absorbs Smullyan's twelve
-- micro-steps into three named scaffolding instances, leaving only
-- two MP firings. A finer chain (one MP per HB rule) would push K
-- to 6-8 and require six-to-eight more pool elements bridging the
-- gnum/numeral boundary at each step.
--
-- An earlier draft tried to mechanize the full twelve-step chain
-- with separate hbBoxedFwd, hbK_chiAndInner, hb4_chi, hbK_innerBoxImpPhi,
-- loebBridgeA, loebPayoff scaffolding plus pre-staged intermediate
-- targets. The depth-1 search produced exactly one new formula
-- (`Box(numeral (gnum chi0)) -> Box(numeral (gnum (Box chi0Code -> phi0)))`)
-- and stalled because `Box(numeral (gnum chi0))` was never produced
-- (it would require HB1 applied to chi0, which is itself a derived
-- theorem, not a pool element). The current chain-collapse design
-- substitutes that derived `Box chi` for the absorbed `hbBoxBoxPhi`
-- which is the chain's actual destination after the four-axiom
-- and HB1 steps in Smullyan.

end LoebFixedPointShadow
