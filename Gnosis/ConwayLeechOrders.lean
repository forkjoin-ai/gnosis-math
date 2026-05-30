/-
  ConwayLeechOrders
  =================

  The group-order arithmetic of Conway's automorphism groups of the
  Leech lattice — `Co₀ = Aut(Λ₂₄) = 2.Co₁` and its simple quotient
  `Co₁` — proved as FINITE, DECIDABLE integer facts, the next rung of
  the moonshine-arithmetic tower begun in `E8LeechMonsterTower` and
  `LeechLatticeArithmetic`.

  WHAT IS PROVED (and ONLY what is proved).  Two integer order
  factorisations and the index-2 relation between them:

    • |Co₀| = 8315553613086720000 = 2²²·3⁹·5⁴·7²·11·13·23
    • |Co₀| = 2·|Co₁|,  |Co₁| = 4157776806543360000

  Nothing else.  The GROUP-THEORETIC content — that `Co₀` is the
  automorphism group of the Leech lattice, that it is a 2-fold central
  extension `2.Co₁`, that `Co₁` is a sporadic simple group and one of
  the twenty "Happy Family" sporadic subquotients of the Monster, and
  that `Co₁` arises as a quotient of an involution centraliser inside
  the Monster — is CITED, not constructed.  Those constructions need
  far more than `Init` (they need the actual Leech lattice, its
  isometry group, central extensions, and the Monster itself).  Here we
  formalise only the order arithmetic that those theorems would imply.

  We never write "X IS the Y": we say `Co₀` "has order", the order
  "factorises as", "equals twice".  See `deferred_scope`.

  INIT-ONLY (no Mathlib).  Every theorem closes by kernel `decide` /
  `rfl` — NEVER `native_decide`, NO `sorry`, NO `axiom`, NO `Classical`.
  The 19-digit products are large but decidable; the Lean kernel's GMP
  bignum `Nat` arithmetic evaluates `2²²·3⁹·5⁴·7²·11·13·23` and the
  `2·|Co₁|` doubling in a fraction of a second.  Footprints are
  axiom-free (`#print axioms` reports "does not depend on any axioms").

  HONESTY (read before trusting any number).  Every arithmetic claim
  below was COMPUTED and checked before being proved.  In particular
  `2²²·3⁹·5⁴·7²·11·13·23` was computed independently and confirmed to
  equal `8315553613086720000` BEFORE the theorem was written; its half
  `4157776806543360000` was likewise confirmed.  No claim from the
  design brief had to be corrected here — both offered numbers verified
  exactly.

  PRIOR ART (extended, not duplicated).
    • `LeechLatticeArithmetic` proves the Leech kissing number 196560,
      its `2⁴·3³·5·7·13` factorisation, the `240·819` ladder, and the
      Conway three-orbit decomposition `196560 = 1104 + 97152 + 98304`
      under the action of `Co₀ = 2.Co₁`.  We CITE that orbit action;
      196560 happens to divide `|Co₀|` (its primes are all dominated),
      but that quotient carries no group meaning — see
      `kissing_divides_co0_order`, where we prove the divisibility yet
      decline to dress it as an order identity.
    • `E8LeechMonsterTower` proves the Monster floor 196884 and the
      McKay–Thompson `c(1) = 196884 = 196883 + 1`, where 196883 is the
      dimension of the Monster's smallest faithful irreducible
      representation.  We CITE 196883 to state the Monster tie-in; we
      prove no Monster order here.
    NEW here: the Conway group orders `|Co₀|` and `|Co₁|`, their shared
    prime-power factorisation, and the index-2 extension arithmetic.
-/

namespace ConwayLeechOrders

-- ══════════════════════════════════════════════════════════
-- |Co₀| = |Aut(Λ₂₄)| — THE ORDER AND ITS FACTORISATION
-- ══════════════════════════════════════════════════════════
-- Co₀ (Conway's group "dot-zero") is the automorphism group of the
-- Leech lattice Λ₂₄ — the group of all 24×24 orthogonal integer
-- matrices fixing the lattice setwise.  Conway (1968) computed its
-- order.  It is a perfect 2-fold central extension 2.Co₁ of the
-- sporadic simple group Co₁; the central involution is −I (negation of
-- every lattice vector), which fixes the lattice but is not in Co₁.

/-- Order of `Co₀ = Aut(Λ₂₄) = 2.Co₁` — Conway's "dot-zero" group, the
    full automorphism group of the Leech lattice.  Cited constant
    (Conway 1968), not constructed. -/
def co0Order : Nat := 8315553613086720000

/-- **|Co₀| prime-power factorisation (VERIFIED).**
    `|Co₀| = 2²²·3⁹·5⁴·7²·11·13·23`.

    The product was computed independently and confirmed to equal
    `8315553613086720000` before this theorem was written.  Kernel
    `decide` re-evaluates the 19-digit product and the equality. -/
theorem co0_factorisation :
    co0Order = 2^22 * 3^9 * 5^4 * 7^2 * 11 * 13 * 23 := by decide

/-- The seven prime-power factors of `|Co₀|`, each as its literal value,
    so the factorisation can be read off term by term:
    `2²² = 4194304`, `3⁹ = 19683`, `5⁴ = 625`, `7² = 49`. -/
theorem co0_prime_powers :
    (2^22 : Nat) = 4194304
    ∧ (3^9 : Nat) = 19683
    ∧ (5^4 : Nat) = 625
    ∧ (7^2 : Nat) = 49 := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- The largest prime dividing `|Co₀|` is 23 (the Leech lattice lives in
    dimension 24, and 23 is the largest prime ≤ 24).  A decidable
    divisibility witness: `|Co₀|` is a multiple of 23. -/
theorem co0_divisible_by_23 : co0Order % 23 = 0 := by decide

-- ══════════════════════════════════════════════════════════
-- |Co₁| AND THE INDEX-2 EXTENSION  Co₀ = 2.Co₁
-- ══════════════════════════════════════════════════════════
-- Co₁ = Co₀ / {±I} is the sporadic simple group; it is one of the
-- twenty "Happy Family" sporadic groups that are subquotients of the
-- Monster.  Its order is exactly half of |Co₀|: the only difference is
-- the central involution −I.

/-- Order of the sporadic simple group `Co₁ = Co₀ / {±I}`.  Cited
    constant, not constructed.  `|Co₁| = |Co₀| / 2`. -/
def co1Order : Nat := 4157776806543360000

/-- **Index-2 extension arithmetic (VERIFIED).**  `Co₀ = 2.Co₁` is a
    2-fold central extension, so `|Co₀| = 2·|Co₁|`.  The factor 2 is the
    central involution `−I` of the Leech lattice. -/
theorem co0_is_double_co1 : co0Order = 2 * co1Order := by decide

/-- Equivalently `|Co₁| = |Co₀| / 2`, and the division is exact
    (`|Co₀|` is even). -/
theorem co1_is_half_co0 :
    co1Order = co0Order / 2 ∧ co0Order % 2 = 0 := by
  exact ⟨by decide, by decide⟩

/-- `|Co₁|` inherits all of `|Co₀|`'s odd prime structure and one fewer
    factor of 2:  `|Co₁| = 2²¹·3⁹·5⁴·7²·11·13·23`.  Computed and
    confirmed before proving. -/
theorem co1_factorisation :
    co1Order = 2^21 * 3^9 * 5^4 * 7^2 * 11 * 13 * 23 := by decide

-- ══════════════════════════════════════════════════════════
-- THE KISSING-NUMBER / ORDER LINK  (an arithmetic accident, NOT meaning)
-- ══════════════════════════════════════════════════════════
-- The Leech kissing number 196560 (`LeechLatticeArithmetic`) is the
-- size of the UNION of Co₀'s three minimal-vector orbits.  Its prime
-- factorisation 2⁴·3³·5·7·13 is dominated termwise by |Co₀|'s
-- 2²²·3⁹·5⁴·7²·11·13·23, so 196560 DOES divide |Co₀| — but the
-- quotient |Co₀|/196560 = 42305421312000 has NO group-theoretic
-- meaning (the orbit-stabiliser counts are per-orbit, not a global
-- |Co₀|/196560).  We prove the divisibility as the bare arithmetic
-- fact it is, and explicitly DECLINE to dress it as an order identity.
-- (The verify-first kernel `decide` caught an earlier draft that
-- wrongly claimed 196560 ∤ |Co₀|; the true fact is the opposite.)

/-- The Leech kissing number 196560 divides `|Co₀|` as an arithmetic
    consequence of `196560 = 2⁴·3³·5·7·13` being dominated termwise by
    `|Co₀| = 2²²·3⁹·5⁴·7²·11·13·23`.  This is an arithmetic accident,
    NOT a meaningful order relation: the quotient
    `|Co₀|/196560 = 42305421312000` has no clean group interpretation.
    The genuine link between Co₀ and the 196560 vectors is the orbit
    ACTION proved in `LeechLatticeArithmetic`, not this quotient. -/
theorem kissing_divides_co0_order :
    co0Order % 196560 = 0
    ∧ co0Order / 196560 = 42305421312000 := by
  exact ⟨by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- MONSTER TIE-IN  (cited, not constructed)
-- ══════════════════════════════════════════════════════════
-- Co₁ is one of the twenty "Happy Family" sporadic simple groups —
-- those that are subquotients of the Monster M.  Concretely Co₁ appears
-- as a quotient of the centraliser of an involution in M.  The Monster's
-- smallest faithful irreducible representation has dimension 196883
-- (the moonshine floor under c(1)=196884; see `E8LeechMonsterTower`).
-- We make NO claim about |M| here and construct no representation; we
-- only cite the dimension and record the subquotient relationship in
-- the doc.  The single decidable fact below merely re-states the
-- moonshine floor link 196884 = 196883 + 1 to anchor the citation.

/-- Dimension of the Monster's smallest faithful irreducible
    representation — `196883`.  Cited (see `E8LeechMonsterTower` for the
    moonshine floor `196884 = 196883 + 1`).  Stated to anchor the
    Monster subquotient relationship documented above; no Monster order
    or representation is constructed here. -/
def monsterSmallestIrrep : Nat := 196883

/-- Anchor of the cited tie-in: the moonshine floor `196884` exceeds the
    Monster's smallest faithful irrep dimension `196883` by exactly the
    trivial representation, `196884 = 196883 + 1`.  (Co₁, a Happy-Family
    subquotient of the Monster, acts on the Leech lattice whose 196560
    kissing vectors sit just below this floor.) -/
theorem monster_floor_anchor :
    (196884 : Nat) = monsterSmallestIrrep + 1 := by decide

-- ══════════════════════════════════════════════════════════
-- SCOPE  (honesty over coverage)
-- ══════════════════════════════════════════════════════════
/--
  `deferred_scope` — honest scope marker.

  PROVED HERE (all kernel `decide`/`rfl`, Init-only, axiom-free):
    • |Co₀| = 8315553613086720000 = 2²²·3⁹·5⁴·7²·11·13·23   (co0_factorisation)
    • the literal prime powers 2²²,3⁹,5⁴,7²                  (co0_prime_powers)
    • 23 | |Co₀|                                             (co0_divisible_by_23)
    • |Co₀| = 2·|Co₁|,  Co₀ = 2.Co₁ index-2 extension        (co0_is_double_co1)
    • |Co₁| = |Co₀|/2 = 4157776806543360000                  (co1_is_half_co0)
    • |Co₁| = 2²¹·3⁹·5⁴·7²·11·13·23                          (co1_factorisation)
    • 196560 | |Co₀| (arithmetic accident, NOT order meaning) (kissing_divides_co0_order)
    • 196884 = 196883 + 1 Monster-floor anchor               (monster_floor_anchor)

  VERIFICATION NOTE.  `2²²·3⁹·5⁴·7²·11·13·23` was computed
  independently and equals `8315553613086720000` exactly; its half is
  `4157776806543360000` exactly.  No brief number needed correction.

  DEFERRED (NOT formalised here — needs far more than Init):
    • `Co₀ = Aut(Λ₂₄)` as the actual isometry group of the Leech
      lattice; the central extension `2.Co₁` with centre `{±I}`; the
      proof that `Co₁` is simple.  We prove only the ORDER arithmetic.
    • `Co₁` as a Happy-Family sporadic subquotient of the Monster
      (a quotient of an involution centraliser in M).  CITED only.
    • The Monster group `M`, its order, and its 196883-dimensional
      irreducible representation.  We CITE the dimension 196883 and
      construct nothing.
    • The Leech lattice's 196560 minimal vectors and the three Co₀
      orbits acting on them — proved as COUNTS in
      `LeechLatticeArithmetic`, not as a group action here.

  These order facts are TRUE and DECIDABLE; the group constructions
  they shadow are deferred honestly, exactly as `E8LeechMonsterTower`
  and `LeechLatticeArithmetic` defer the lattice, code, and Monster
  constructions.
-/
theorem deferred_scope : True := trivial

end ConwayLeechOrders
