/-
  LeechLatticeArithmetic
  ======================

  The next rung of Leech / Monster moonshine arithmetic, building on
  `E8LeechMonsterTower`.  This module pushes the FINITE, DECIDABLE
  arithmetic shadows deeper:

    • the 196560 Leech minimal-vector count, decomposed three ways
      (Conway's three shape-orbits, its prime factorisation, and the
      E_8 kissing-ladder multiple);
    • the kissing-number ladder  E_8 240  →  Leech 196560;
    • the next McKay–Thompson j-coefficient  c(3) = 864299970  as a
      sum of Monster irreducible-representation dimensions;
    • the Niemeier count (24 even unimodular rank-24 lattices) and its
      coincidence with the Leech dimension;
    • the Golay / Steiner combinatorics (759 octads) hiding inside one
      of the Leech orbits.

  INIT-ONLY (no Mathlib).  Every theorem closes by kernel `decide` /
  `rfl` — NEVER `native_decide`, NO `sorry`, NO `axiom`, NO `Classical`.
  Footprints are propext-only (the `Eq`/`And` plumbing `decide` emits).

  HONESTY (read before trusting any number).  Every arithmetic claim
  below was COMPUTED and checked before being proved.  Two claims
  floated in the design brief were FALSE and are NOT proved here; they
  are recorded in `corrected_claims` so the next agent does not retry
  them:

    1. The brief's `196560 = 2³·3³·5·7·13` is FALSE — that product is
       98280 = 196560/2.  The CORRECT factorisation has 2⁴, not 2³:
       `196560 = 2⁴·3³·5·7·13`.  We prove the correct one.
    2. The brief's `c(3) = 1 + 196883 + 21296876 + 842609326` is FALSE —
       that sum is 864103086, short of 864299970 by exactly 196884.
       The CORRECT McKay–Thompson decomposition doubles the two
       smallest pieces:
       `c(3) = 2·1 + 2·196883 + 21296876 + 842609326 = 864299970`.
       We prove the correct one.

  These are arithmetic / counting SHADOWS.  The full Leech lattice
  construction (its 196560 minimal vectors as actual lattice points,
  even unimodularity, rootlessness), the Golay code / Steiner system
  S(5,8,24), the Mathieu group M24, and the Monster group with its
  genuine 196883-dimensional irreducible module all remain DEFERRED
  (they need far more than `Init`).  We never write "X IS the Y": we
  say "equals", "decomposes as", "is the count of", "is the coefficient
  of".  See `deferred_scope` at the bottom.

  PRIOR ART (extended, not duplicated).  The bare `196884 = 196883 + 1`
  lives in `MoonshineMcKayBraid` / `TopologicalGriessAlgebra` /
  `ConformalFieldTheoryVOA`; the `c(2)` decomposition and the
  `196884 = 196560 + 324` Leech echo live in `E8LeechMonsterTower`.
  NEW here: the 196560 three-way decomposition (orbits / factorisation
  / kissing ladder), the `240 · 819` ladder, the `c(3)` Monster-irrep
  sum, the 759-octad combinatorics inside the orbits, and the Niemeier
  count fact.
-/

namespace LeechLatticeArithmetic

-- ══════════════════════════════════════════════════════════
-- THE LEECH KISSING NUMBER 196560 — THREE DECOMPOSITIONS
-- ══════════════════════════════════════════════════════════
-- The Leech lattice Λ₂₄ has 196560 minimal (norm-4) vectors; this is
-- its kissing number, the maximal known kissing number in dimension 24
-- (proved optimal by Cohn–Kumar–Miller–Radchenko–Viazovska 2017).

/-- Number of minimal (shortest nonzero) vectors of the Leech lattice —
    its kissing number — `196560`.  Cited constant, not constructed. -/
def leechKissingNumber : Nat := 196560

-- ── Decomposition 1: Conway's three shape-orbits ───────────
-- Under the automorphism group Co₀ = 2.Co₁, the 196560 minimal vectors
-- split into three orbits by coordinate shape (Conway & Sloane, SPLAG):
--
--   orbit A:  shape (∓4², 0²²)   — two ±4 entries           1104 vectors
--   orbit B:  shape (∓2⁸, 0¹⁶)   — supported on a Golay octad
--                                  with even sign change    97152 vectors
--   orbit C:  shape (∓3, ±1²³)   — one ±3 and 23 ±1         98304 vectors
--
-- (All coordinates ×2√2 normalisation aside; the COUNTS are what we
-- prove.)

/-- Orbit A count: vectors of shape `(∓4², 0²²)`.  Equals `4·C(24,2)`,
    the 276 coordinate pairs times 4 sign choices. -/
def orbitA : Nat := 1104

/-- Orbit B count: vectors supported on a Golay-code octad,
    `759 · 2⁷` — the 759 octads of `S(5,8,24)` times the `2⁷`
    even-sign-change patterns on 8 coordinates. -/
def orbitB : Nat := 97152

/-- Orbit C count: vectors of shape `(∓3, ±1²³)`, `2¹² · 24`. -/
def orbitC : Nat := 98304

/-- **Leech minimal-vector orbit decomposition (VERIFIED).**  The 196560
    minimal vectors split into Conway's three shape-orbits:
    `196560 = 1104 + 97152 + 98304`. -/
theorem leech_kissing_orbit_sum :
    leechKissingNumber = orbitA + orbitB + orbitC := by decide

/-- Orbit A equals `4 · C(24,2) = 4 · 276`: four sign choices on each of
    the 276 unordered coordinate pairs. -/
theorem orbitA_is_four_times_pairs : orbitA = 4 * 276 := by decide

/-- `276 = C(24,2)` written as the triangular number `24·23/2`. -/
theorem pairs_count : (276 : Nat) = 24 * 23 / 2 := by decide

/-- Orbit B equals `759 · 2⁷ = 759 · 128`: the 759 octads (blocks of the
    Steiner system `S(5,8,24)`) times the `2⁷` even sign patterns on the
    8 octad coordinates. -/
theorem orbitB_is_octads_times_signs : orbitB = 759 * 128 := by decide

/-- The octad count `759` equals the Steiner-system block count
    `C(24,5) / C(8,5) = 42504 / 56`.  (Each 5-subset of 24 points lies
    in a unique octad.)  Decidable Nat arithmetic. -/
theorem octads_eq_steiner_blocks : (759 : Nat) = 42504 / 56 := by decide

/-- The Steiner numerators: `C(24,5) = 42504` and `C(8,5) = 56`. -/
theorem steiner_binomials :
    (42504 : Nat) = 24*23*22*21*20 / (5*4*3*2*1)
    ∧ (56 : Nat) = 8*7*6 / (3*2*1) := by
  exact ⟨by decide, by decide⟩

/-- Orbit C equals `2¹² · 24 = 4096 · 24`. -/
theorem orbitC_is_pow_times_dim : orbitC = 4096 * 24 := by decide

-- ── Decomposition 2: prime factorisation ───────────────────
-- The CORRECT factorisation (the brief's 2³ version is wrong; see
-- `corrected_claims`).

/-- **Leech kissing-number factorisation (VERIFIED, corrected).**
    `196560 = 2⁴ · 3³ · 5 · 7 · 13`.  (The design brief's `2³·3³·5·7·13`
    is FALSE — it equals 98280 = 196560/2; the correct exponent of 2 is
    4.) -/
theorem leech_kissing_factorisation :
    leechKissingNumber = 2^4 * 3^3 * 5 * 7 * 13 := by decide

/-- For the record: the brief's claimed `2³·3³·5·7·13` equals 98280,
    i.e. exactly HALF the kissing number — not the kissing number.  A
    decidable witness that the dropped claim is false. -/
theorem brief_factorisation_is_half :
    2^3 * 3^3 * 5 * 7 * 13 = leechKissingNumber / 2
    ∧ 2^3 * 3^3 * 5 * 7 * 13 ≠ leechKissingNumber := by
  exact ⟨by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- THE KISSING-NUMBER LADDER  E_8 240  →  LEECH 196560
-- ══════════════════════════════════════════════════════════

/-- Kissing number of the `E_8` lattice in dimension 8 — its 240 roots.
    (`E8Lattice.e8_root_count = 240`.) -/
def e8KissingNumber : Nat := 240

/-- The ladder multiple `819 = 3² · 7 · 13`. -/
def ladderMultiple : Nat := 819

/-- **Kissing-number ladder (VERIFIED).**  The Leech kissing number is
    `819` times the `E_8` kissing number:  `196560 = 240 · 819`. -/
theorem kissing_ladder :
    leechKissingNumber = e8KissingNumber * ladderMultiple := by decide

/-- The ladder multiple factors as `819 = 3² · 7 · 13`. -/
theorem ladder_multiple_factor : ladderMultiple = 3^2 * 7 * 13 := by decide

/-- The quotient `196560 / 240` is exactly `819` (no remainder), so the
    `E_8` kissing number divides the Leech kissing number. -/
theorem leech_div_e8_kissing :
    leechKissingNumber / e8KissingNumber = ladderMultiple
    ∧ leechKissingNumber % e8KissingNumber = 0 := by
  exact ⟨by decide, by decide⟩

/-- The two kissing factorisations share the prime `13` and overlap on
    `3` (E_8: `240 = 2⁴·3·5`; ladder: `819 = 3²·7·13`); multiplied they
    rebuild the full `196560 = 2⁴·3³·5·7·13`.  Stated as the factor
    identity `(2⁴·3·5)·(3²·7·13) = 2⁴·3³·5·7·13`. -/
theorem kissing_factor_merge :
    (2^4 * 3 * 5) * (3^2 * 7 * 13) = 2^4 * 3^3 * 5 * 7 * 13 := by decide

/-- The `E_8` kissing number itself factors as `240 = 2⁴ · 3 · 5`. -/
theorem e8_kissing_factor : e8KissingNumber = 2^4 * 3 * 5 := by decide

/-- Leech kissing number also equals `24 · 8190` — its dimension times
    `8190 = 2·3²·5·7·13`.  A second divisor view of the ladder. -/
theorem leech_kissing_by_dimension :
    leechKissingNumber = 24 * 8190 ∧ (8190 : Nat) = 2 * 3^2 * 5 * 7 * 13 := by
  exact ⟨by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- THE NEXT j-COEFFICIENT  c(3) = 864299970  (McKay–Thompson)
-- ══════════════════════════════════════════════════════════
--   j(τ) = q⁻¹ + 744 + 196884 q + 21493760 q² + 864299970 q³ + ⋯
-- Monstrous moonshine: dim V♮ₙ = c(n) is a sum of dimensions of
-- irreducible representations of the Monster.  The first irrep
-- dimensions are 1, 196883, 21296876, 842609326, 18538750076, ⋯

/-- Coefficient `c(3)` of `q³` in the Klein j-invariant, `864299970`. -/
def jCoeff3 : Nat := 864299970

/-- Smallest faithful irreducible representation of the Monster, `196883`. -/
def monsterIrrep1 : Nat := 196883

/-- Third Monster irreducible-representation dimension, `21296876`. -/
def monsterIrrep2 : Nat := 21296876

/-- Fourth Monster irreducible-representation dimension, `842609326`. -/
def monsterIrrep3 : Nat := 842609326

/-- The trivial (1-dimensional) representation. -/
def trivialRep : Nat := 1

/-- **McKay–Thompson decomposition of c(3) (VERIFIED, corrected).**
    The `q³`-coefficient of `j` decomposes as a sum of Monster irrep
    dimensions:
      `c(3) = 2·1 + 2·196883 + 21296876 + 842609326 = 864299970`.
    (The design brief's `1 + 196883 + 21296876 + 842609326` is FALSE —
    it gives 864103086, short by exactly 196884; the two smallest
    pieces appear with multiplicity 2.) -/
theorem jcoeff3_mckay_thompson :
    jCoeff3 =
      2 * trivialRep + 2 * monsterIrrep1 + monsterIrrep2 + monsterIrrep3 := by
  decide

/-- For the record: the brief's single-multiplicity sum
    `1 + 196883 + 21296876 + 842609326` equals 864103086, which is
    `c(3) − 196884` — short by exactly the moonshine floor c(1).  A
    decidable witness that the dropped claim is false. -/
theorem brief_c3_is_short_by_c1 :
    trivialRep + monsterIrrep1 + monsterIrrep2 + monsterIrrep3
      = jCoeff3 - 196884
    ∧ trivialRep + monsterIrrep1 + monsterIrrep2 + monsterIrrep3
        ≠ jCoeff3 := by
  exact ⟨by decide, by decide⟩

/-- The shortfall of the brief's sum is exactly the moonshine floor
    `c(1) = 196884 = 196883 + 1`.  Stated as the difference. -/
theorem c3_shortfall_is_c1 :
    jCoeff3 - (trivialRep + monsterIrrep1 + monsterIrrep2 + monsterIrrep3)
      = 196883 + 1 := by decide

-- ══════════════════════════════════════════════════════════
-- THE NIEMEIER COUNT  (24 even unimodular rank-24 lattices)
-- ══════════════════════════════════════════════════════════
-- Niemeier (1973): there are exactly 24 even unimodular lattices in
-- dimension 24, classified by their root systems; 23 have roots and 1
-- (the Leech lattice) is rootless.

/-- The number of even unimodular lattices of rank 24 — the Niemeier
    lattices — `24`.  Cited classification constant. -/
def niemeierCount : Nat := 24

/-- Niemeier lattices with a nonempty root system, `23`. -/
def niemeierWithRoots : Nat := 23

/-- The unique rootless Niemeier lattice (the Leech lattice), counted as
    `1`. -/
def niemeierRootless : Nat := 1

/-- Dimension of the Leech lattice, `24`. -/
def leechDim : Nat := 24

/-- **Niemeier split (VERIFIED).**  The 24 Niemeier lattices split into
    the 23 with roots plus the 1 rootless (Leech):  `24 = 23 + 1`. -/
theorem niemeier_split :
    niemeierCount = niemeierWithRoots + niemeierRootless := by decide

/-- **Niemeier count = Leech dimension (VERIFIED coincidence).**  The
    Niemeier classification has exactly `24` members, equal to the
    rank/dimension `24` of the lattices it classifies.  A numerical
    coincidence of the rank-24 theory, stated as a cited count — NOT a
    structural identity. -/
theorem niemeier_count_eq_dim : niemeierCount = leechDim := by decide

/-- The Leech dimension is three times the `E_8` lattice dimension
    `24 = 3 · 8` — the `E8³` gluing count threaded through the tower
    (cross-checks `E8LeechMonsterTower.leech_dim_is_three_e8`). -/
theorem leech_dim_three_e8 : leechDim = 3 * 8 := by decide

-- ══════════════════════════════════════════════════════════
-- THE WHOLE LEECH ARITHMETIC LEDGER (one decidable conjunction)
-- ══════════════════════════════════════════════════════════

/-- The Leech / moonshine arithmetic ledger proved in this module, in
    one decidable conjunction:
      • orbit sum        196560 = 1104 + 97152 + 98304
      • factorisation    196560 = 2⁴·3³·5·7·13
      • kissing ladder   196560 = 240 · 819
      • c(3) moonshine   864299970 = 2·1 + 2·196883 + 21296876 + 842609326
      • Niemeier count   24 = 23 + 1 = dim Λ₂₄
    Each conjunct is a genuine, verified Nat equation. -/
theorem leech_arithmetic_ledger :
    leechKissingNumber = orbitA + orbitB + orbitC
    ∧ leechKissingNumber = 2^4 * 3^3 * 5 * 7 * 13
    ∧ leechKissingNumber = e8KissingNumber * ladderMultiple
    ∧ jCoeff3 = 2 * trivialRep + 2 * monsterIrrep1 + monsterIrrep2 + monsterIrrep3
    ∧ niemeierCount = niemeierWithRoots + niemeierRootless
    ∧ niemeierCount = leechDim := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- CORRECTED CLAIMS  (honest record of the two false brief items)
-- ══════════════════════════════════════════════════════════
/--
  `corrected_claims` — a marker theorem whose docstring records the two
  arithmetic claims from the design brief that were COMPUTED, found
  FALSE, and therefore replaced by their correct forms above (rather
  than proved as stated).

  DROPPED (false as written) → REPLACED BY (verified):

    1. `196560 = 2³·3³·5·7·13`            (FALSE: = 98280 = 196560/2)
       → `196560 = 2⁴·3³·5·7·13`          (`leech_kissing_factorisation`)
       witness of falsehood: `brief_factorisation_is_half`.

    2. `c(3) = 1 + 196883 + 21296876 + 842609326`
                                          (FALSE: = 864103086, short by 196884)
       → `c(3) = 2·1 + 2·196883 + 21296876 + 842609326`
                                          (`jcoeff3_mckay_thompson`)
       witness of falsehood: `brief_c3_is_short_by_c1`.

  VERIFIED-AND-PROVED (true as offered or as corrected):
    • 196560 = 1104 + 97152 + 98304        (orbit sum)            TRUE
    • 196560 = 240 · 819                   (kissing ladder)       TRUE
    • c(2) already in `E8LeechMonsterTower` (21296876+196883+1)   TRUE
    • 24 Niemeier lattices = dim 24                               TRUE
-/
theorem corrected_claims : True := trivial

-- ══════════════════════════════════════════════════════════
-- SCOPE  (honesty over coverage)
-- ══════════════════════════════════════════════════════════
/--
  `deferred_scope` — honest scope marker.

  PROVED HERE (all kernel `decide`/`rfl`, Init-only):
    • 196560 = 1104 + 97152 + 98304        Conway 3-orbit decomposition
    • 1104 = 4·C(24,2);  97152 = 759·128;  98304 = 2¹²·24  (orbit shapes)
    • 759 = C(24,5)/C(8,5)                 Steiner S(5,8,24) octad count
    • 196560 = 2⁴·3³·5·7·13                kissing-number factorisation
    • 196560 = 240·819,  819 = 3²·7·13     E_8 → Leech kissing ladder
    • 240 = 2⁴·3·5,  divides 196560        E_8 kissing factor
    • 864299970 = 2·1+2·196883+21296876+842609326   c(3) McKay–Thompson
    • 24 = 23 + 1                          Niemeier split (rooted + Leech)
    • 24 (Niemeier count) = 24 (dimension) = 3·8

  DEFERRED (NOT formalized here — needs far more than Init):
    • The Leech lattice itself: its 196560 minimal vectors as actual
      points of a rank-24 even unimodular rootless lattice, and the
      Co₀ = 2.Co₁ orbit action that produces the three shape-orbits.
      We prove only the COUNTS.
    • The binary Golay code, the Steiner system S(5,8,24), and the
      Mathieu group M24 (order 244823040).  We prove only that the
      octad count 759 = C(24,5)/C(8,5) as arithmetic.
    • The Niemeier classification theorem (that there are EXACTLY 24
      and no more).  We prove only the decidable count fact 24 = 23+1
      and its coincidence with the dimension.
    • The Monster group, its genuine irreducible representations of
      dimensions 196883, 21296876, 842609326, …, and the graded
      moonshine module V♮ with dim V♮ₙ = c(n).  We prove only the Nat
      coefficient arithmetic for c(3).
    • The j-invariant as a modular function over ℂ.

  These shadows are TRUE and DECIDABLE; the constructions they shadow
  are deferred honestly, exactly as `E8Lattice` / `E8LeechMonsterTower`
  defer the continuous and Mathlib pieces.
-/
theorem deferred_scope : True := trivial

end LeechLatticeArithmetic
