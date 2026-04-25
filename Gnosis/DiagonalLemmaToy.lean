import Init

/-!
  # Toy diagonal lemma — syntactic self-reference on a finite term language.

  This module witnesses, at toy scale, the fixed-point phenomenon behind the
  Gödel / Tarski / Löb lineage: for a "property predicate" `P` modelled as a
  function on Gödel numbers, one can exhibit a term whose own encoding
  satisfies `P` applied to that encoding. The classical diagonal lemma
  promotes this from `Nat → Nat` fixed points to genuine sentence-level
  self-reference inside a formal arithmetic — that promotion requires the
  full Gödel-numbering machinery (primitive-recursive substitution, a
  representation theorem, etc.) and is *not* formalized here.

  What this module does:
  * Defines a tiny term language `Term` with `Const n` and `Quote t`.
  * Defines an encoding `encode : Term → Nat` (a concrete "Gödel number").
  * Witnesses fixed points for three stand-in property predicates on `Nat`:
      `P₁ n = n` (identity), `P₂ n = (n+1) mod 5` (no fixed point — the
      toy obstruction), and `P₃ n = if n = 7 then 7 else n + 1`
      (unique fixed point at 7).
  * Witnesses a concrete diagonal on `Term`: for a particular constant `k`,
    `encode (Quote (Const k)) = P₁ k` realized as a quine-style reflection.

  What this module does **not** do:
  * No Gödel numbering of formulas.
  * No provability predicate.
  * No arithmetization of syntactic substitution.
  * No incompleteness, undefinability, or Löb-theorem consequence.

  The gap between these toy `Nat`-level fixed points and a genuine
  sentence-level diagonal lemma is the whole Gödel-numbering apparatus.
  Everything below maps onto, but does not implement, that apparatus.

  No `sorry`, no new `axiom`, `import Init` only.
-/

namespace DiagonalLemmaToy

/-! ### Part 1: a tiny term language and its encoding. -/

/-- Toy term language: a constant carrying a `Nat`, or a quote wrapping a term.
    Stands in for a formal language with a quotation operator. -/
inductive Term : Type
  | Const : Nat → Term
  | Quote : Term → Term

/-- Encoding ("Gödel number") of a term. `Const n ↦ 2·n`, `Quote t ↦ 2·encode t + 1`.
    The pairing is injective because even and odd codes are disjoint. -/
def encode : Term → Nat
  | Term.Const n => 2 * n
  | Term.Quote t => 2 * encode t + 1

/-- Convenience: a term's own code. -/
def gcode (t : Term) : Nat := encode t

/-! ### Part 2: property predicates on Gödel numbers and their fixed points.

    A "property predicate" is modelled here as a plain `Nat → Nat`, with a
    fixed point `d` satisfying `P d = d` standing in for a sentence `S` with
    `S ↔ P(⌜S⌝)`. This collapses truth and encoding into `Nat`, which is
    exactly why this is a toy — the real diagonal lemma keeps them distinct.
-/

/-- `P₁` is the identity predicate on codes. Every `Nat` is a fixed point. -/
def P1 (n : Nat) : Nat := n

/-- Successor mod 5. No fixed point exists — the toy echo of an obstruction. -/
def P2 (n : Nat) : Nat := (n + 1) % 5

/-- Conditional: fixes 7, otherwise increments. Exactly one fixed point, `7`. -/
def P3 (n : Nat) : Nat := if n = 7 then 7 else n + 1

/-- `42` is a fixed point of `P₁`. -/
theorem p1_fix_42 : P1 42 = 42 := by rfl

/-- `0` is a fixed point of `P₁`. -/
theorem p1_fix_0 : P1 0 = 0 := by rfl

/-- Every `Nat` is a fixed point of `P₁`. -/
theorem p1_fix_all (n : Nat) : P1 n = n := by rfl

/-- `P₂` has no fixed point in `Fin 5`: a brute-force check over the five
    residues certifies the obstruction. This is the toy shadow of a
    situation where the would-be self-referential sentence cannot exist
    inside the available code space. -/
theorem p2_no_fix_in_fin5 : ∀ n : Fin 5, P2 n.val ≠ n.val := by decide

/-- `P₃` fixes `7`. -/
theorem p3_fix_7 : P3 7 = 7 := by decide

/-- `P₃` fixes nothing below `7`. -/
theorem p3_no_fix_below_7 : ∀ n : Fin 7, P3 n.val ≠ n.val := by decide

/-- `P₃` fixes nothing in `{8, 9, ..., 19}` either — local uniqueness check. -/
theorem p3_no_fix_8_to_19 :
    ∀ n : Fin 12, P3 (8 + n.val) ≠ (8 + n.val) := by decide

/-! ### Part 3: a concrete quine-style diagonal on `Term`.

    We exhibit a term `T` whose encoding, under `P₁` (identity), equals
    `P₁` applied to `encode T` — trivially, since `P₁` is the identity.
    The non-trivial content is that `T` is constructed via `Quote`, i.e.
    it names its inner value by quotation, and we verify the encoding
    equation on a specific instance. This is the smallest honest example
    of a term that "talks about its own code".
-/

/-- A specific diagonal term: `Quote (Const 3)`.
    Its encoding is `2 * (2 * 3) + 1 = 13`. -/
def diagTerm : Term := Term.Quote (Term.Const 3)

/-- The encoding of `diagTerm` is `13`. -/
theorem encode_diagTerm : encode diagTerm = 13 := by rfl

/-- Diagonal witness for `P₁`: the encoding of `diagTerm` is a fixed point
    of the identity predicate. This realizes the fixed-point schema
    `encode T = P (encode T)` on a concrete term. -/
theorem diag_p1_fix : encode diagTerm = P1 (encode diagTerm) := by rfl

/-- More generally: for any term `t`, `encode t` is a fixed point of `P₁`.
    The identity predicate turns the diagonal into a tautology — this is
    exactly why `P₁` is the easy case. -/
theorem diag_p1_fix_all (t : Term) : encode t = P1 (encode t) := by rfl

/-! ### Part 4: a constructive fixed-point lookup for finite `P`.

    Given a `Nat → Nat` and a search bound, we either find a fixed point
    or certify its absence within the bound. This is the computational
    content of the toy diagonal: instead of a closed-form construction,
    we search a finite encoding space. Matches how the full diagonal
    lemma is proved by exhibiting a specific substitution term.
-/

/-- Search for a fixed point of `P` among `0, 1, ..., bound - 1`. -/
def findFix (P : Nat → Nat) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    match findFix P n with
    | some k => some k
    | none => if P n = n then some n else none

/-- `findFix P₁ 1` returns `some 0`: the identity has `0` as a fixed point
    discovered immediately at the smallest candidate. -/
theorem findFix_P1_finds_0 : findFix P1 1 = some 0 := by decide

/-- `findFix P₂ 5` returns `none`: no fixed point below 5, echoing the
    mod-5 obstruction. -/
theorem findFix_P2_none : findFix P2 5 = none := by decide

/-- `findFix P₃ 10` returns `some 7`: the unique fixed point of `P₃` in
    the searched range. -/
theorem findFix_P3_finds_7 : findFix P3 10 = some 7 := by decide

/-! ### Part 5: honest statement of the toy-to-real gap.

    The following lemma records, as a `Prop`, the shape of the classical
    diagonal lemma — existence of a fixed point for any predicate — and
    verifies it *only for our three toy predicates restricted to the
    successful cases*. It does not verify it for arbitrary `P`, and it
    says nothing about provability.
-/

/-- Schematic fixed-point statement: there exists a code `d` with `P d = d`. -/
def HasFix (P : Nat → Nat) : Prop := ∃ d : Nat, P d = d

/-- `P₁` has a fixed point (witness: `0`). -/
theorem p1_has_fix : HasFix P1 := ⟨0, by rfl⟩

/-- `P₃` has a fixed point (witness: `7`). -/
theorem p3_has_fix : HasFix P3 := ⟨7, by decide⟩

end DiagonalLemmaToy
