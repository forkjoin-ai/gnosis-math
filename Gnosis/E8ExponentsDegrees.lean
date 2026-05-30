/-
  E8ExponentsDegrees
  ==================

  The 8 exponents and 8 fundamental-invariant degrees of the Weyl
  group W(E_8), formalized as small-list arithmetic and tied to the
  single-source-of-truth tabulation in
  `Gnosis.DynkinCoxeterClassification` and `Gnosis.E8Lattice`.

  Background (Weyl-group invariant theory)
  ----------------------------------------
  For a finite Coxeter / Weyl group W of rank r acting on the
  reflection representation, the ring of W-invariant polynomials is
  a free polynomial algebra on r homogeneous generators (Chevalley–
  Shephard–Todd).  The degrees d_1 ≤ … ≤ d_r of those generators are
  the *fundamental-invariant degrees*; the numbers m_i = d_i − 1 are
  the *exponents*.  Three classical numerical facts follow:

      * Σ m_i = # positive roots               (= r·h / 2)
      * d_i = m_i + 1
      * Π d_i = |W|                             (Chevalley's theorem)
      * max d_i = h  (the Coxeter number), so  max m_i = h − 1
      * the exponents are symmetric:  m_i + m_{r+1−i} = h

  For E_8 (r = 8, h = 30):

      exponents  m = [ 1,  7, 11, 13, 17, 19, 23, 29]
      degrees    d = [ 2,  8, 12, 14, 18, 20, 24, 30]

  What is proved here vs. cited
  -----------------------------
  This module is small-list *arithmetic*.  It VERIFIES the numerical
  identities above for E_8 by kernel `decide` (no `native_decide`,
  no `Classical`, no `sorry`):

      Σ m_i = 120 = positiveRootCount .E8 8   (E8Lattice / Dynkin SSOT)
      d_i = m_i + 1
      Π d_i = 696729600 = weylOrder .E8 8     (Dynkin SSOT)
      max d_i = 30 = coxeterNumber .E8 8       (Dynkin SSOT)
      max m_i = 29 = h − 1
      m_i + m_{9−i} = 30 = h  for each pair

  The *theorems* behind these arithmetic facts — Chevalley–Shephard–
  Todd freeness, and the equality Π d_i = |W| in particular — are
  CITED, not formalized.  We assert only the arithmetic equalities,
  which are checked in the kernel against the SSOT numbers already
  proved in the cited modules.

  Sources of truth
  ----------------
  * `weylOrder .E8 8 = 696729600`        — DynkinCoxeterClassification
  * `coxeterNumber .E8 8 = 30`           — DynkinCoxeterClassification
  * `positiveRootCount .E8 8 = 120`      — DynkinCoxeterClassification
  * 240 roots / coset tower              — E8Lattice
-/

import Gnosis.DynkinCoxeterClassification

namespace E8ExponentsDegrees

open DynkinCoxeterClassification

-- ══════════════════════════════════════════════════════════
-- THE 8 EXPONENTS AND 8 DEGREES OF E_8
-- ══════════════════════════════════════════════════════════

/-- The 8 exponents m_i of W(E_8) (degrees of generators minus 1). -/
def exponents : List Nat := [1, 7, 11, 13, 17, 19, 23, 29]

/-- The 8 fundamental-invariant degrees d_i of W(E_8). -/
def degrees : List Nat := [2, 8, 12, 14, 18, 20, 24, 30]

/-- There are exactly 8 exponents (= rank of E_8). -/
theorem exponent_count : exponents.length = 8 := by decide

/-- There are exactly 8 degrees (= rank of E_8). -/
theorem degree_count : degrees.length = 8 := by decide

-- ══════════════════════════════════════════════════════════
-- SUM OF EXPONENTS = # POSITIVE ROOTS = 120
-- ══════════════════════════════════════════════════════════

/-- Sum of a Nat list. -/
def listSum (xs : List Nat) : Nat := xs.foldl (· + ·) 0

/-- Product of a Nat list. -/
def listProd (xs : List Nat) : Nat := xs.foldl (· * ·) 1

/-- The exponents sum to 120. -/
theorem exponents_sum : listSum exponents = 120 := by decide

/-- That sum equals the number of positive roots of E_8 (SSOT:
    `positiveRootCount .E8 8 = 120` in DynkinCoxeterClassification). -/
theorem exponents_sum_eq_positive_roots :
    listSum exponents = positiveRootCount .E8 8 := by decide

-- ══════════════════════════════════════════════════════════
-- DEGREES = EXPONENTS + 1  (elementwise)
-- ══════════════════════════════════════════════════════════

/-- Each degree is its exponent plus one (d_i = m_i + 1). -/
theorem degrees_eq_exponents_succ :
    degrees = exponents.map (· + 1) := by decide

-- ══════════════════════════════════════════════════════════
-- PRODUCT OF DEGREES = |W(E_8)| = 696729600   (Chevalley)
-- ══════════════════════════════════════════════════════════

/-- Verified product: 2·8·12·14·18·20·24·30 = 696729600. -/
theorem degrees_product : listProd degrees = 696729600 := by decide

/-- That product equals the order of the Weyl group of E_8 (SSOT:
    `weylOrder .E8 8 = 696729600`).  This is Chevalley's theorem
    |W| = Π d_i, here verified as an arithmetic equality against the
    tabulated Weyl order; the theorem itself is cited, not proved. -/
theorem degrees_product_eq_weyl_order :
    listProd degrees = weylOrder .E8 8 := by decide

-- ══════════════════════════════════════════════════════════
-- LARGEST DEGREE = h = 30 ;  LARGEST EXPONENT = h − 1 = 29
-- ══════════════════════════════════════════════════════════

/-- Max of a Nat list (0 on empty). -/
def listMax (xs : List Nat) : Nat := xs.foldl Nat.max 0

/-- The largest degree is 30. -/
theorem degrees_max : listMax degrees = 30 := by decide

/-- The largest degree equals the Coxeter number h of E_8 (SSOT:
    `coxeterNumber .E8 8 = 30`). -/
theorem degrees_max_eq_coxeter :
    listMax degrees = coxeterNumber .E8 8 := by decide

/-- The largest exponent is 29. -/
theorem exponents_max : listMax exponents = 29 := by decide

/-- The largest exponent equals h − 1. -/
theorem exponents_max_eq_coxeter_pred :
    listMax exponents = coxeterNumber .E8 8 - 1 := by decide

-- ══════════════════════════════════════════════════════════
-- EXPONENT SYMMETRY:  m_i + m_{9−i} = h = 30
-- ══════════════════════════════════════════════════════════
-- Pairing the i-th smallest with the i-th largest exponent gives a
-- constant sum equal to the Coxeter number.  With the list reversed,
-- this is the elementwise sum exponents[i] + reverse[i].

/-- The reversed exponent list (the i-th largest in position i). -/
def exponentsRev : List Nat := exponents.reverse

/-- Elementwise pair sums of the exponent list with its reverse:
    m_i + m_{9−i} for i = 1..8.  Each entry is the Coxeter number. -/
def pairSums : List Nat :=
  (exponents.zip exponentsRev).map (fun p => p.1 + p.2)

/-- Every symmetric pair sums to 30 = h. -/
theorem exponent_pairs_sum_to_coxeter :
    pairSums = [30, 30, 30, 30, 30, 30, 30, 30] := by decide

/-- Stated against the SSOT Coxeter number: every entry of the
    pair-sum list equals `coxeterNumber .E8 8`. -/
theorem exponent_pairs_all_coxeter :
    pairSums.all (fun s => s == coxeterNumber .E8 8) = true := by decide

end E8ExponentsDegrees
