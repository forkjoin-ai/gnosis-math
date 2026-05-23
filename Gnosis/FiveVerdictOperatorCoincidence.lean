import Init

/-!
# FiveVerdictOperatorCoincidence — is the verdict-5 the operator-5?

`Gnosis/ContrarianSchemaClosure.lean` closes the contrarian corpus onto a *five-verdict
basis* — `=`, `<` (either direction), `≠`, `¬∀`, period/descent. The gnosis tree elsewhere
carries a *five-operator basis* — fork, race, fold, vent, interfere
(`ForkRaceFoldVentAreForces` + `InterferenceAsTheFifthForce`, collapsed in `TheFiveIsOne`).

Two fives. **Is the agreement structural, or a coincidence?** This module settles it.

The trap to avoid: a bijection between two 5-element sets is *always* available (there are
`5! = 120` of them) and proves nothing — `TheFiveIsOne.onlyOneFive` is exactly that trivial
content and its own §12 (`OpenForcedFiveness`) concedes the cardinality 5 is *not* forced. So
"there is a 5×5 bijection" cannot be the test. The honest test is whether the two fives carry
the *same canonical structure*. They do not:

* **The verdict-5 is a curated count.** It is the visible middle of three closure theorems
  whose mutually-exclusive *atomic* outcomes number **7**: trichotomy contributes 3
  (`a<b`, `a=b`, `b<a`), the forcing dichotomy 2 (`forced`, `¬forced`), the dynamics duality
  2 (`conservative`, `dissipative`). The same content honestly counts as **3** (closures),
  **5** (curated basis), or **7** (atomic cells). 5 is a presentation choice, not an invariant.
* **The operators are 5 atoms.** Their finest honest grain *is* 5; their canonical
  provenance split is **4 + 1** (four forces, then the appended fifth).
* **The verdict provenance split is 3 + 1 + 1** (order family / forcing / dynamics).

So two canonical invariants disagree: finest grain (operators 5, verdicts 7) and provenance
block count (operators 2, verdicts 3). By the *separation schema* of the very file under
question (`separates`: a differing invariant refutes an identity), the two structured fives
are not the same object. The shared cardinal 5 is therefore a coincidence — real at the
curated level, structure-blind like every 5-set bijection, and resting on a verdict count
that is not even canonically 5.

Zero `sorry`. Zero `omega`. Zero Mathlib.
-/

namespace Gnosis
namespace FiveVerdictOperatorCoincidence

-- ═══════════════════════════════════════════════════════════════════════
-- §0  The separation schema (re-stated from ContrarianSchemaClosure's core)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Separation schema.** A differing invariant refutes an identity. This is the exact shape
    of `FiniteDynamicsCore.separates`; re-stated here so this module imports `Init` only and
    can turn it back on the question that produced it. -/
theorem separates {α γ : Type} (I : α → γ) {a b : α} (h : I a ≠ I b) : a ≠ b :=
  fun heq => h (congrArg I heq)

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The two fives, as written
-- ═══════════════════════════════════════════════════════════════════════

/-- The five primary scheduler operators. Each is *atomic*: there is no honest finer reading
    of "fork". -/
inductive Operator
  | fork | race | fold | vent | interfere
  deriving DecidableEq, Repr

/-- The five-verdict basis exactly as presented in `ContrarianSchemaClosure`'s docstring. -/
inductive DocVerdict
  | eq         -- `=`  (Equates / indistinguishability)
  | lt         -- `<`  (Dominates, either direction)
  | ne         -- `≠`  (separates)
  | notForced  -- `¬∀` (not_forced)
  | dynamics   -- period/descent (conservative vs dissipative)
  deriving DecidableEq, Repr

def Operator.all : List Operator := [.fork, .race, .fold, .vent, .interfere]
def DocVerdict.all : List DocVerdict := [.eq, .lt, .ne, .notForced, .dynamics]

theorem operator_all_complete : ∀ o : Operator, o ∈ Operator.all := by
  intro o; cases o <;> decide
theorem docVerdict_all_complete : ∀ d : DocVerdict, d ∈ DocVerdict.all := by
  intro d; cases d <;> decide

/-- The bare coincidence, stated honestly: both lists have length 5. -/
theorem curated_cardinals_agree : DocVerdict.all.length = Operator.all.length := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §2  The coincidence is real but structure-blind: many bijections, none canonical
-- ═══════════════════════════════════════════════════════════════════════

/-- One bijection verdict→operator (an arbitrary pairing). -/
def bij1 : DocVerdict → Operator
  | .eq => .fork | .lt => .race | .ne => .fold | .notForced => .vent | .dynamics => .interfere

/-- Its inverse. -/
def unbij1 : Operator → DocVerdict
  | .fork => .eq | .race => .lt | .fold => .ne | .vent => .notForced | .interfere => .dynamics

theorem bij1_linv (d : DocVerdict) : unbij1 (bij1 d) = d := by cases d <;> rfl
theorem bij1_rinv (o : Operator) : bij1 (unbij1 o) = o := by cases o <;> rfl

/-- A *second* bijection, differing from `bij1` by transposing the first two outputs. -/
def bij2 : DocVerdict → Operator
  | .eq => .race | .lt => .fork | .ne => .fold | .notForced => .vent | .dynamics => .interfere

/-- A bijection between the two fives exists — the coincidence is real. -/
theorem bijection_exists :
    ∃ (f : DocVerdict → Operator) (g : Operator → DocVerdict),
      (∀ d, g (f d) = d) ∧ (∀ o, f (g o) = o) :=
  ⟨bij1, unbij1, bij1_linv, bij1_rinv⟩

/-- …but it is **not canonical**: distinct bijections exist, none distinguished. A "matching"
    that any of 120 maps satisfies carries no information beyond the bare cardinal. -/
theorem bijection_not_canonical : bij1 ≠ bij2 := by
  intro h; exact absurd (congrFun h DocVerdict.eq) (by decide)

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The verdict-5 is a curated count of three closure theorems
-- ═══════════════════════════════════════════════════════════════════════

/-- The three closure theorems behind the verdict basis (`ContrarianSchemaClosure` §2/§3 plus
    the dynamics duality of `FiniteDynamicsCore`). Atomic at the *theorem* level: 3 of them. -/
inductive Closure
  | comparison  -- comparison_verdict_complete : Nat-measure trichotomy
  | forcing     -- forces_or_not_forced       : decidability dichotomy
  | dynamics    -- dissipative_not_periodic   : conservative/dissipative duality
  deriving DecidableEq, Repr

/-- The *finest honest* enumeration: every mutually-exclusive atomic outcome of the three
    closures. Trichotomy gives 3, the forcing dichotomy 2, the dynamics duality 2 — **7**. -/
inductive RawCell
  | cmp_lt | cmp_eq | cmp_gt              -- comparison_verdict_complete (3, proven exclusive)
  | force_yes | force_no                  -- forces_or_not_forced (2)
  | dyn_conservative | dyn_dissipative    -- returns_conserves vs dissipative_not_periodic (2)
  deriving DecidableEq, Repr

def Closure.all : List Closure := [.comparison, .forcing, .dynamics]
def RawCell.all : List RawCell :=
  [.cmp_lt, .cmp_eq, .cmp_gt, .force_yes, .force_no, .dyn_conservative, .dyn_dissipative]

/-- Each atomic cell's closure of origin. -/
def RawCell.closure : RawCell → Closure
  | .cmp_lt | .cmp_eq | .cmp_gt          => .comparison
  | .force_yes | .force_no               => .forcing
  | .dyn_conservative | .dyn_dissipative => .dynamics

/-- How many atomic cells each closure contributes. -/
def cellsOf (c : Closure) : Nat :=
  (RawCell.all.filter (fun r => decide (r.closure = c))).length

theorem comparison_has_3 : cellsOf .comparison = 3 := by decide
theorem forcing_has_2    : cellsOf .forcing = 2    := by decide
theorem dynamics_has_2   : cellsOf .dynamics = 2   := by decide

/-- The three closures partition into 3 + 2 + 2 = 7 atomic cells. -/
theorem raw_cells_total :
    cellsOf .comparison + cellsOf .forcing + cellsOf .dynamics = 7 := by decide

/-- **The verdict count is presentation-dependent.** The same content honestly counts as 3
    (closure theorems), 5 (the curated basis), or 7 (atomic cells); no two agree. A number
    that moves under honest re-binning is not an invariant — so the verdict-5 is a choice. -/
theorem verdict_count_is_a_choice :
    Closure.all.length = 3 ∧ DocVerdict.all.length = 5 ∧ RawCell.all.length = 7 ∧
    Closure.all.length ≠ DocVerdict.all.length ∧
    DocVerdict.all.length ≠ RawCell.all.length ∧
    Closure.all.length ≠ RawCell.all.length := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> decide

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Two canonical invariants that disagree
-- ═══════════════════════════════════════════════════════════════════════

-- ── Invariant A: finest honest grain ────────────────────────────────────

/-- Operators are atomic; their finest grain is 5. -/
def operatorFinestGrain : Nat := Operator.all.length
/-- The verdict system's finest grain is the atomic-cell count, 7. -/
def verdictFinestGrain : Nat := RawCell.all.length

theorem operatorFinestGrain_eq : operatorFinestGrain = 5 := rfl
theorem verdictFinestGrain_eq : verdictFinestGrain = 7 := rfl

/-- **Invariant A disagrees.** At finest honest grain the operator system has 5 outcomes, the
    verdict system 7. The shared "5" only appears after the verdict side is curated down. -/
theorem finest_grain_differs : operatorFinestGrain ≠ verdictFinestGrain := by decide

-- ── Invariant B: canonical provenance block structure ───────────────────

/-- The operators' canonical genesis: four forces, then the appended fifth. -/
inductive OpGenesis | fourForces | fifthAppended
  deriving DecidableEq, Repr

def Operator.genesis : Operator → OpGenesis
  | .fork | .race | .fold | .vent => .fourForces
  | .interfere                    => .fifthAppended

/-- Each verdict's closure of origin (`≠` is derived from comparison via
    `separates_of_dominates`, so it files under `comparison`). -/
def DocVerdict.closure : DocVerdict → Closure
  | .eq | .lt | .ne => .comparison
  | .notForced      => .forcing
  | .dynamics       => .dynamics

/-- Number of distinct provenance blocks on each side. Operators: 2 (`{fourForces,
    fifthAppended}`). Verdicts: 3 (`{comparison, forcing, dynamics}`). -/
def operatorBlocks : Nat := 2
def verdictBlocks : Nat := 3

theorem operatorBlocks_witness :
    (∀ o : Operator, o.genesis = .fourForces ∨ o.genesis = .fifthAppended) ∧
    Operator.fork.genesis = OpGenesis.fourForces ∧
    Operator.interfere.genesis = OpGenesis.fifthAppended := by
  refine ⟨?_, rfl, rfl⟩; intro o; cases o <;> (first | exact Or.inl rfl | exact Or.inr rfl)

theorem verdictBlocks_witness :
    DocVerdict.eq.closure = Closure.comparison ∧
    DocVerdict.notForced.closure = Closure.forcing ∧
    DocVerdict.dynamics.closure = Closure.dynamics := ⟨rfl, rfl, rfl⟩

/-- **Invariant B disagrees.** Operator provenance is the 4+1 split (2 blocks); verdict
    provenance is the 3+1+1 split (3 blocks). -/
theorem provenance_blocks_differ : operatorBlocks ≠ verdictBlocks := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §5  The verdict — by ContrarianSchemaClosure's own separation schema
-- ═══════════════════════════════════════════════════════════════════════

/-- A "five" as a structured outcome system: a label plus its two canonical invariants. -/
structure OutcomeSystem where
  label : String
  finestGrain : Nat
  blocks : Nat

def operatorSystem : OutcomeSystem := ⟨"fork/race/fold/vent/interfere", 5, 2⟩
def verdictSystem  : OutcomeSystem := ⟨"=/</≠/¬∀/period-descent", 7, 3⟩

/-- The two structured fives are **distinct objects** — proven by `separates` on the
    finest-grain invariant (5 ≠ 7), the same schema `ContrarianSchemaClosure` uses to refute
    identities. (The block invariant 2 ≠ 3 gives an independent second proof.) -/
theorem outcome_systems_distinct : operatorSystem ≠ verdictSystem :=
  separates OutcomeSystem.finestGrain (by decide)

theorem outcome_systems_distinct' : operatorSystem ≠ verdictSystem :=
  separates OutcomeSystem.blocks (by decide)

/--
**Answer: the five is a coincidence.** Bundled verdict:

1. `curated_cardinals_agree` — at the curated level both fives have 5 elements (the
   coincidence is *real*);
2. `bijection_not_canonical` — but the matching is one of many, none distinguished, so it is
   structure-blind;
3. `verdict_count_is_a_choice` — the verdict-5 is not even a canonical 5 (honest counts:
   3 / 5 / 7);
4. `finest_grain_differs` — finest honest grain disagrees (5 vs 7);
5. `provenance_blocks_differ` — canonical provenance disagrees (4+1 vs 3+1+1);
6. `outcome_systems_distinct` — therefore, by the separation schema, the two structured
   fives are not the same object.

Were it *not* a coincidence, the two fives would share a canonical structure — e.g. both a
cyclic group of order 5, or both quotients of one object. Instead one is 5 atoms (4+1) and the
other a curated bin (3+1+1, finest grain 7). They agree on the cardinal alone.
-/
theorem five_is_coincidence :
    DocVerdict.all.length = Operator.all.length ∧
    bij1 ≠ bij2 ∧
    (Closure.all.length = 3 ∧ DocVerdict.all.length = 5 ∧ RawCell.all.length = 7) ∧
    operatorFinestGrain ≠ verdictFinestGrain ∧
    operatorBlocks ≠ verdictBlocks ∧
    operatorSystem ≠ verdictSystem :=
  ⟨curated_cardinals_agree,
   bijection_not_canonical,
   ⟨rfl, rfl, rfl⟩,
   finest_grain_differs,
   provenance_blocks_differ,
   outcome_systems_distinct⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §6  "But 7 = 5 + 2 (constructive + destructive)?" — also a coincidence
-- ═══════════════════════════════════════════════════════════════════════

/-! The verdict finest grain is 7, and `interfere` famously resolves into constructive and
    destructive modes (`InterferenceAsTheFifthForce`). So is `7 = 5 + 2` the real bridge —
    the five operators plus the two interference signs? No. Three checks, then the honest
    residue. The "+2" on each side is a *different* 2. -/

/-- The operators with `interfere` resolved into its two physical modes. This is the *honest*
    finer grain of the operator basis: a split **replaces** the atom, it does not sit beside
    it. (`fork`/`race` are n-ary at runtime, but atomic as operators — no fixed sub-blocks.) -/
inductive OperatorFine
  | fork | race | fold | vent
  | interfereConstructive | interfereDestructive
  deriving DecidableEq, Repr

def OperatorFine.all : List OperatorFine :=
  [.fork, .race, .fold, .vent, .interfereConstructive, .interfereDestructive]

/-- Which coarse operator each fine cell refines. -/
def OperatorFine.coarse : OperatorFine → Operator
  | .fork => .fork | .race => .race | .fold => .fold | .vent => .vent
  | .interfereConstructive | .interfereDestructive => .interfere

/-- How many fine cells refine a given operator. -/
def operatorFineCellsOf (o : Operator) : Nat :=
  (OperatorFine.all.filter (fun r => decide (r.coarse = o))).length

/-- **Check 1.** Resolving interference yields **6** atoms (a base of 4, plus a 2-mode split),
    not 7. The "+2" lands on a base of 4, never 5 — `5 + 2` double-counts `interfere` (it
    appears once as the atom and twice as its children). As a refinement, 6 ≠ 7. -/
theorem interference_split_gives_six :
    OperatorFine.all.length = 6 ∧ OperatorFine.all.length ≠ RawCell.all.length :=
  ⟨rfl, by decide⟩

/-- **Check 2.** The verdict's "+2 over the curated 5" is the order-direction split and the
    dynamics duality — interference appears **nowhere** in the verdict tally. The comparison
    closure alone carries 3 cells, forcing 2, dynamics 2. -/
theorem verdict_plus_two_is_not_interference :
    cellsOf .comparison = 3 ∧ cellsOf .forcing = 2 ∧ cellsOf .dynamics = 2 :=
  ⟨by decide, by decide, by decide⟩

/-- **Check 3 (decisive).** The verdict-7 carries an irreducible **3-block** (the trichotomy
    `lt/eq/gt`), while every operator — even with interference split — refines into **at most
    2** cells. A partition with a block of 3 cannot be isomorphic to one whose blocks are all
    ≤ 2; the shapes `{3,2,2}` and `{1,1,1,1,2}` differ outright (and the totals, 7 vs 6). -/
theorem verdict_has_triple_no_operator_does :
    (∃ c : Closure, cellsOf c = 3) ∧ (∀ o : Operator, operatorFineCellsOf o ≤ 2) := by
  refine ⟨⟨.comparison, by decide⟩, ?_⟩
  intro o; cases o <;> decide

-- ── The honest residue: what IS shared is generic ───────────────────────

/-- The sign trichotomy `{-, 0, +}`. -/
inductive Sign | neg | zero | pos
  deriving DecidableEq, Repr

/-- A bare 3-element trichotomy (`lt/eq/gt`). -/
inductive Tri | lt | eq | gt
  deriving DecidableEq, Repr

def triToSign : Tri → Sign | .lt => .neg | .eq => .zero | .gt => .pos
def signToTri : Sign → Tri | .neg => .lt | .zero => .eq | .pos => .gt

/-- The comparison trichotomy **is** the sign of the measure difference — a genuine shared
    abstraction. But it is *generic*: every ordered measure has a sign, every superposition a
    phase. Finding it on both sides is expected, not a fingerprint. -/
theorem trichotomy_is_the_sign :
    (∀ t, signToTri (triToSign t) = t) ∧ (∀ s, triToSign (signToTri s) = s) := by
  refine ⟨?_, ?_⟩ <;> (intro x; cases x <;> rfl)

/-- And here is exactly why the bridge fails to close. The verdict comparison block realizes
    all three signs (`±` **and** the middle `0`); the operator's interference, as formalized,
    realizes only the `±` duality (constructive/destructive). It lacks the `0` — the null /
    no-interference mode, the analogue of `eq`, the `StallIsOptimal` stall. Interference is a
    2-block where the verdict order is a 3-block. -/
theorem interference_lacks_the_zero :
    operatorFineCellsOf .interfere = 2 ∧ cellsOf .comparison = 3 :=
  ⟨by decide, by decide⟩

/--
**Answer to the follow-up: `7 = 5 + 2` is also a coincidence.**

1. `interference_split_gives_six` — honestly resolving interference gives **6**, not 7;
   `5 + 2` only reaches 7 by double-counting `interfere`.
2. `verdict_plus_two_is_not_interference` — the verdict's extra cells beyond the curated 5 are
   the order-direction split and the dynamics duality, never interference.
3. `verdict_has_triple_no_operator_does` — the verdict-7 has a 3-block; no operator refines
   past 2, so `{3,2,2}` cannot be matched by `{1,1,1,1,2}`.

The resemblance that survives is `trichotomy_is_the_sign`: both domains instantiate the sign
`{-,0,+}` and ±-dualities — universal patterns, not a shared fingerprint. And
`interference_lacks_the_zero` pins the gap: interference gives a `±` duality, the verdict order
gives a full trichotomy with a middle `0`. The "+2" you saw is two un-mergings of the verdict
basis colliding with two interference signs at the cardinal level only.
-/
theorem seven_is_also_coincidence :
    OperatorFine.all.length = 6 ∧
    OperatorFine.all.length ≠ RawCell.all.length ∧
    (cellsOf .comparison = 3 ∧ cellsOf .forcing = 2 ∧ cellsOf .dynamics = 2) ∧
    (∃ c : Closure, cellsOf c = 3) ∧
    (∀ o : Operator, operatorFineCellsOf o ≤ 2) ∧
    operatorFineCellsOf .interfere = 2 :=
  ⟨rfl, by decide, ⟨by decide, by decide, by decide⟩, ⟨.comparison, by decide⟩,
   by intro o; cases o <;> decide, by decide⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §7  Granting the trichotomy: destructive(−)/null(0)/constructive(+)
-- ═══════════════════════════════════════════════════════════════════════

/-! The honest upgrade: interference IS three-valued. Two waves interfere constructively (+),
    destructively (−), or with no net effect (0) — the sign of the cross-term `2·Re(a·b̄)` in
    `|a+b|² = |a|² + |b|² + 2·Re(a·b̄)`. That sign is `{-,0,+}` = `Sign`, exactly the verdict
    comparison trichotomy (the sign of `I b - I a`). So at that block the resemblance is **not**
    generic-coincidence — it is one primitive (the sign of a real difference) wearing two
    names. This section grants the upgrade in full and finds where it stops. -/

/-- Interference as a trichotomy. -/
inductive IntMode | destructive | null | constructive
  deriving DecidableEq, Repr

def intToSign : IntMode → Sign
  | .destructive => .neg | .null => .zero | .constructive => .pos
def signToInt : Sign → IntMode
  | .neg => .destructive | .zero => .null | .pos => .constructive

/-- Interference's three modes are the sign trichotomy. -/
theorem interference_is_the_sign :
    (∀ m, signToInt (intToSign m) = m) ∧ (∀ s, intToSign (signToInt s) = s) := by
  refine ⟨?_, ?_⟩ <;> (intro x; cases x <;> rfl)

/-- Therefore the interference trichotomy and the verdict comparison trichotomy are the **same
    object** (both `≅ Sign`): destructive↔lt, null↔eq, constructive↔gt. This is a genuine,
    non-generic-at-this-block correspondence — Taylor's intuition, proven. -/
def triToInt : Tri → IntMode := fun t => signToInt (triToSign t)
def intToTri : IntMode → Tri := fun m => signToTri (intToSign m)

theorem comparison_trichotomy_is_interference_trichotomy :
    (∀ t, intToTri (triToInt t) = t) ∧ (∀ m, triToInt (intToTri m) = m) := by
  refine ⟨?_, ?_⟩ <;> (intro x; cases x <;> rfl)

/-- The operators with interference resolved into all **three** modes: now 7 atoms. -/
inductive OperatorFine3
  | fork | race | fold | vent
  | intDestructive | intNull | intConstructive
  deriving DecidableEq, Repr

def OperatorFine3.all : List OperatorFine3 :=
  [.fork, .race, .fold, .vent, .intDestructive, .intNull, .intConstructive]

def OperatorFine3.coarse : OperatorFine3 → Operator
  | .fork => .fork | .race => .race | .fold => .fold | .vent => .vent
  | .intDestructive | .intNull | .intConstructive => .interfere

def operatorFine3CellsOf (o : Operator) : Nat :=
  (OperatorFine3.all.filter (fun r => decide (r.coarse = o))).length

/-- **Granting the upgrade, the finest grains now BOTH equal 7.** A tighter cardinal
    coincidence than before (4 + 3 = 7 = 3 + 2 + 2) — which is exactly why cardinal agreement
    cannot be the test. -/
theorem upgraded_grains_both_seven :
    OperatorFine3.all.length = 7 ∧ RawCell.all.length = 7 := ⟨rfl, rfl⟩

/-- **But the partitions still differ in shape — and this is where the bridge stops.** The
    verdict-7 is `{3, 2, 2}`: the shared trichotomy, then two genuine dichotomies (forcing,
    dynamics). The operator-7 is `{3, 1, 1, 1, 1}`: the shared trichotomy, then four lone
    atoms (fork, race, fold, vent). Distinguishing invariants: block count (3 vs 5), and the
    verdict has 2-blocks while the operator has none. The match is exactly **one block deep**. -/
theorem partitions_still_differ :
    Closure.all.length = 3 ∧ Operator.all.length = 5 ∧
    (cellsOf .forcing = 2 ∧ cellsOf .dynamics = 2) ∧
    (∀ o : Operator, operatorFine3CellsOf o ≠ 2) ∧
    (∀ o : Operator, operatorFine3CellsOf o ≤ 3) := by
  refine ⟨rfl, rfl, ⟨by decide, by decide⟩, ?_, ?_⟩
  · intro o; cases o <;> decide
  · intro o; cases o <;> decide

/--
**Refined answer.** Granting interference its full trichotomy, the picture sharpens into a
precise verdict rather than a flat "coincidence":

* `comparison_trichotomy_is_interference_trichotomy` — the trichotomy block is a **real
  shared structure**: destructive/null/constructive ≅ lt/eq/gt ≅ `Sign`. Both are the sign of
  a real difference (`I b - I a` for the verdict; the cross-term `Re(a·b̄)` for interference).
  Your "feels right" is right, and it is proven, not waved at.
* `upgraded_grains_both_seven` — the finest grains now coincide at 7 as well. Tighter
  coincidence; still just a cardinal.
* `partitions_still_differ` — the two sevens are **not isomorphic**: `{3,2,2}` vs
  `{3,1,1,1,1}`. The shared trichotomy accounts for 3 of the 7; the remaining 4 split as two
  dichotomies on the verdict side and four atoms on the operator side, with no correspondence.

So: not a flat coincidence and not an identity. One primitive — the sign trichotomy — is
genuinely shared because both objects are "the sign of a difference"; that primitive is
universal and it covers exactly one block. The rest does not line up.
-/
theorem interference_trichotomy_is_real_but_local :
    -- the real, shared block: comparison trichotomy ≅ interference trichotomy
    (∀ t, intToTri (triToInt t) = t) ∧
    -- the upgraded cardinal coincidence: both sevens
    (OperatorFine3.all.length = 7 ∧ RawCell.all.length = 7) ∧
    -- but non-isomorphic partitions: 3 blocks vs 5, and a 2-block present only on the verdict
    (Closure.all.length = 3 ∧ Operator.all.length = 5) ∧
    (cellsOf .forcing = 2 ∧ ∀ o : Operator, operatorFine3CellsOf o ≠ 2) :=
  ⟨comparison_trichotomy_is_interference_trichotomy.1,
   ⟨rfl, rfl⟩,
   ⟨rfl, rfl⟩,
   ⟨by decide, by intro o; cases o <;> decide⟩⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Why "zero" keeps surfacing as "null": the still point of a reflection
-- ═══════════════════════════════════════════════════════════════════════

/-! The same middle cell kept reappearing: `eq` (verdict indistinguishability, the
    `StallIsOptimal` stall), `0` (the sign trichotomy), `null` (no net interference) — and one
    layer down, the conservative pole of the dynamics duality, `iter f T x = x`: zero net change
    over a period. They coincide for one reason, and it is not numerology: an identity element is
    *defined* as the one with no effect, and "null" is the state with no effect, so "additive
    identity" and "no-effect state" name one point. The structural version we can pin: each
    domain carries a reflection (negation / phase-flip / argument-swap), and the zero/null is its
    **unique fixed point** — the one place the symmetry cannot move. -/

/-- The sign reflection (negation). -/
def negSign : Sign → Sign | .neg => .pos | .zero => .zero | .pos => .neg

theorem negSign_fixes_zero : negSign .zero = .zero := rfl

/-- Zero is the **unique** fixed point of the reflection: the still point. -/
theorem zero_is_the_only_fixed_sign : ∀ s : Sign, negSign s = s → s = .zero := by
  intro s
  cases s
  · intro h; exact absurd h (by decide)
  · intro _; rfl
  · intro h; exact absurd h (by decide)

/-- The three middles are one point: `eq ↔ 0 ↔ null` under the canonical maps. -/
theorem the_three_middles_coincide :
    triToSign .eq = Sign.zero ∧ intToSign .null = Sign.zero ∧ triToInt .eq = IntMode.null :=
  ⟨rfl, rfl, rfl⟩

/--
**"Zero is null", precisely.** One point wears many names across the work — verdict `eq` /
sign `0` / interference `null` / the conservative fixed point `iter f T x = x` — and it recurs
because it is the element that changes nothing. Two honest readings:

* *Algebraic (the unit law).* The additive identity is, by definition, the unique element with
  no effect (`0 + x = x`); "null" is the no-effect state; so they name one point. This is not
  new to mathematics — it is the identity axiom, the kernel (preimage of `0`), the diagonal of
  antisymmetry, the fixed point, the zero object.
* *Structural (what is earned here).* In the sign trichotomy the zero is the unique fixed point
  of the reflection (`zero_is_the_only_fixed_sign`), and that reflection — carried by the
  bijections of §7 — fixes exactly `eq` and `null` (`the_three_middles_coincide`). Three
  independently-motivated middles are forced onto that one still point.

So: zero *serves as the name for* the absence of a difference; null *is* the state that maps to
it. The coincidence is real, it is the unit law, and the modest new thing is the kernel-checked
collapse of three domain middles onto the reflection's fixed point.

The standalone, general statement (four characterizations of the no-effect element) lives in
`Gnosis.NullIsTheZero`; this is the in-context instance.
-/
theorem null_is_the_zero :
    (∀ s : Sign, negSign s = s → s = .zero) ∧
    (triToSign .eq = Sign.zero ∧ intToSign .null = Sign.zero ∧ triToInt .eq = IntMode.null) ∧
    (∀ x : Nat, 0 + x = x) :=
  ⟨zero_is_the_only_fixed_sign, ⟨rfl, rfl, rfl⟩, Nat.zero_add⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §9  The floor: everything is the successor (Nat as initial (1+−)-algebra)
-- ═══════════════════════════════════════════════════════════════════════

/-! Strip the dressing and the whole thread runs on `Nat` and `+1`. Every proof here is one of
    two moves: *succ-recursion* (each `induction n`) or *finite enumeration* (each `decide`,
    each `cases <;> rfl` — finite types are themselves succ-built). The single statement that
    generates both is the universal property of `Nat`: it is the **initial `(1 + −)`-algebra** —
    a zero, a successor, and a *unique* map out (`fold`/recursion). Lawvere's natural-number
    object; Peano's axioms. `FiniteDynamicsCore.iter f n x` is exactly `fold x f n`, so the
    dynamics core is one catamorphism; the trichotomy, the descent, and the counts are all its
    shadows. This section writes that floor down — and honestly: it is the floor, not a new
    depth. The payoff is that one recursor plus one enumeration tactic *is* the toolkit. -/

/-- The one recursor: the unique morphism from `Nat` into any `(zero, succ)`-algebra. -/
def fold {α : Type} (z : α) (s : α → α) : Nat → α
  | 0     => z
  | n + 1 => s (fold z s n)

/-- The zero rule (no successor applied yet). -/
theorem fold_zero {α : Type} (z : α) (s : α → α) : fold z s 0 = z := rfl

/-- The one nontrivial computation rule: a step is a successor. -/
theorem fold_succ {α : Type} (z : α) (s : α → α) (n : Nat) :
    fold z s (n + 1) = s (fold z s n) := rfl

/-- **Initiality.** Any map honoring the zero and successor rules already *is* `fold` — the
    morphism out of `Nat` is unique. This is the universal property; induction is its proof. -/
theorem fold_unique {α : Type} (z : α) (s : α → α) (h : Nat → α)
    (h0 : h 0 = z) (hs : ∀ n, h (n + 1) = s (h n)) : ∀ n, h n = fold z s n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [fold_succ, hs k, ih]

-- ── The successor's two Peano facts, and difference-as-successor-count ───

/-- Zero is the unique non-successor (the still point of §8 has an arithmetic cause: nothing
    steps onto it). -/
theorem zero_is_no_successor (n : Nat) : 0 ≠ n + 1 := fun h => Nat.succ_ne_zero n h.symm

/-- The successor is injective: one step is one step. -/
theorem succ_injective (n m : Nat) : n + 1 = m + 1 → n = m := fun h => Nat.succ.inj h

/-- A strict order is a positive number of successor steps. -/
theorem lt_as_steps {a b : Nat} (h : a < b) : ∃ k, b = a + (k + 1) := by
  rcases Nat.le.dest h with ⟨k, hk⟩
  exact ⟨k, by rw [Nat.add_comm k 1, ← Nat.add_assoc]; exact hk.symm⟩

/-- **The sign trichotomy is the count and direction of successor steps.** `a` and `b` are
    equal (zero steps), or `b` is `a` plus some positive count, or `a` is `b` plus some positive
    count. The `−/0/+` of §7 is "which way, how many `+1`"; the `0`/null of §8 is "zero steps". -/
theorem difference_is_successor_count (a b : Nat) :
    a = b ∨ (∃ k, b = a + (k + 1)) ∨ (∃ k, a = b + (k + 1)) := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact Or.inr (Or.inl (lt_as_steps h))
  · exact Or.inl h
  · exact Or.inr (Or.inr (lt_as_steps h))

/-- Null is zero steps: equality is separation by `+0`. Closes the loop with §8 — the no-effect
    middle is the absence of any successor. -/
theorem null_is_zero_steps (a b : Nat) : a = b ↔ b = a + 0 := by
  rw [Nat.add_zero]; exact ⟨Eq.symm, Eq.symm⟩

/--
**Answer: the right statement is initiality, and the floor is the successor.** Everything in
this file factors through:

* `fold_zero` / `fold_succ` — a zero and *one* step rule;
* `fold_unique` — the map out of `Nat` is unique (the universal property; `iter` is `fold`);
* `zero_is_no_successor` / `succ_injective` — Peano's two facts about `+1`;
* `difference_is_successor_count` — order is a count of `+1`; equality is `+0`, the null.

This does not reveal hidden structure — it names the substrate. `Nat`-with-successor is the
floor of all finitary, constructive work, and our two recurring tactics (`induction` and
`decide`) are succ-recursion and finite enumeration. The simplification it buys is
engineering, not metaphysics: one `fold` plus one enumeration discharges the lot.
-/
theorem everything_is_the_successor :
    (∀ (α : Type) (z : α) (s : α → α), fold z s 0 = z) ∧
    (∀ (α : Type) (z : α) (s : α → α) (n : Nat), fold z s (n + 1) = s (fold z s n)) ∧
    (∀ (α : Type) (z : α) (s : α → α) (h : Nat → α),
      h 0 = z → (∀ n, h (n + 1) = s (h n)) → ∀ n, h n = fold z s n) ∧
    ((∀ n : Nat, 0 ≠ n + 1) ∧ (∀ n m : Nat, n + 1 = m + 1 → n = m)) ∧
    (∀ a b : Nat, a = b ∨ (∃ k, b = a + (k + 1)) ∨ (∃ k, a = b + (k + 1))) ∧
    (∀ a b : Nat, a = b ↔ b = a + 0) :=
  ⟨fun _ z s => fold_zero z s,
   fun _ z s n => fold_succ z s n,
   fun _ z s h h0 hs => fold_unique z s h h0 hs,
   ⟨zero_is_no_successor, succ_injective⟩,
   difference_is_successor_count,
   null_is_zero_steps⟩

end FiveVerdictOperatorCoincidence
end Gnosis
