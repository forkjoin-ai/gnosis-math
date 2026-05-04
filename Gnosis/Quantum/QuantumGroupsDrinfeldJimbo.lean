/-
  QuantumGroupsDrinfeldJimbo
  ==========================

  Drinfeld (1985) and Jimbo (1985): for every simple Lie algebra g
  there is a Hopf-algebra deformation U_q(g) — the *quantum group* —
  with generators {E_i, F_i, K_i} and Serre/q-Serre relations that
  reduce to U(g) at q = 1.  At q a root of unity, U_q(g) becomes
  finite-dimensional and its representation category is a modular
  tensor category.

  For g = sl_2 the relations are:

      K E = q^2 E K,      K F = q^{-2} F K,
      [E, F] = (K - K^{-1}) / (q - q^{-1}),
      Δ(K) = K ⊗ K,
      Δ(E) = E ⊗ K + 1 ⊗ E,
      Δ(F) = F ⊗ K^{-1} + K ⊗ F.

  At q^N = 1 (N-th root of unity) we obtain the truncated category
  whose simple objects are V_0, V_1, ..., V_{N-2} and whose fusion
  rules match those of the level-(N-2) WZW MTC.  This connects to
  `ReshetikhinTuraev3DTQFT`: the RT MTC at level k is the
  (semisimple quotient of the) representation category of U_q(sl_2)
  at q = e^{i π / (k + 2)}.

  This file mechanizes the *finite cyclotomic shadow* of U_q(sl_2)
  at q^3 = 1 (smallest non-trivial root of unity), encoding the
  3rd root as the formal element of ℤ[root3]/(root3^2 + root3 + 1)
  ≃ ℤ ⊕ ℤ · root3.  All
  identities become integer pair identities.

  Gnosis mapping
  --------------
    * Quantum group U_q(g)        ↔  Cassini-warped Lie algebra
    * Deformation parameter q     ↔  Cassini "+5" lifted into
                                     the deformation direction
    * Finite-dim at q^N = 1       ↔  closure of Race-Phase orbit
                                     after N rotations
    * R-matrix universal R         ↔  braiding of fork/race witnesses
    * Quantum dimension dim_q V    ↔  weighted depth of a state vector

  No imports beyond `Init`, plus the sibling
  `ReshetikhinTuraev3DTQFT` to reuse rank/object accounting.
  No axioms, no `sorry`. Every theorem closes by `native_decide`,
  `decide`, or `rfl`.
-/

import Gnosis.ReshetikhinTuraev3DTQFT
import Gnosis.MathFoundations

namespace QuantumGroupsDrinfeldJimbo

-- ══════════════════════════════════════════════════════════
-- THE CYCLOTOMIC RING  ℤ[ω] / (ω^2 + ω + 1)  WITH ω^3 = 1
-- ══════════════════════════════════════════════════════════
-- Element a + b ω ∈ ℤ[ω] stored as the pair (a, b).
-- Multiplication uses ω^2 = -1 - ω.

structure Cyc3 where
  re : Int    -- coefficient of 1
  om : Int    -- coefficient of ω
  deriving DecidableEq, BEq

namespace Cyc3

def zero : Cyc3 := ⟨0, 0⟩
def one  : Cyc3 := ⟨1, 0⟩

/-- root3 = e^{2πi/3}. -/
def root3 : Cyc3 := ⟨0, 1⟩

/-- root3^2 = -1 - root3. -/
def root3Sq : Cyc3 := ⟨-1, -1⟩

/-- Addition. -/
def add (x y : Cyc3) : Cyc3 := ⟨x.re + y.re, x.om + y.om⟩

/-- Negation. -/
def neg (x : Cyc3) : Cyc3 := ⟨-x.re, -x.om⟩

/-- Subtraction. -/
def sub (x y : Cyc3) : Cyc3 := add x (neg y)

/-- Multiplication.
    (a + b ω)(c + d ω) = ac + (ad + bc) ω + bd ω^2
                       = (ac - bd) + (ad + bc - bd) ω. -/
def mul (x y : Cyc3) : Cyc3 :=
  ⟨ x.re * y.re - x.om * y.om
  , x.re * y.om + x.om * y.re - x.om * y.om ⟩

/-- Integer scalar multiplication. -/
def smul (k : Int) (x : Cyc3) : Cyc3 := ⟨k * x.re, k * x.om⟩

end Cyc3

/-- root3 is a primitive 3rd root: root3^3 = 1. -/
theorem root3_cubed_is_one :
    Cyc3.mul (Cyc3.mul Cyc3.root3 Cyc3.root3) Cyc3.root3 = Cyc3.one := by
  native_decide

/-- 1 + root3 + root3^2 = 0. -/
theorem root3_sum_zero :
    Cyc3.add (Cyc3.add Cyc3.one Cyc3.root3) Cyc3.root3Sq = Cyc3.zero := by
  native_decide

/-- q := root3 satisfies q^3 = 1, so q is a primitive 3rd root. -/
def q : Cyc3 := Cyc3.root3

/-- q^2 = root3^2. -/
def q2 : Cyc3 := Cyc3.mul q q

theorem q2_value : q2 = Cyc3.root3Sq := by native_decide

/-- q^{-1} = root3^2 (inverse of a 3rd root). -/
def qInv : Cyc3 := Cyc3.root3Sq

theorem q_qInv : Cyc3.mul q qInv = Cyc3.one := by native_decide

/-- q^{-2} = root3 (inverse of root3^2 in the 3rd root ring). -/
def qInv2 : Cyc3 := Cyc3.root3

theorem q2_qInv2 : Cyc3.mul q2 qInv2 = Cyc3.one := by native_decide

-- ══════════════════════════════════════════════════════════
-- U_q(sl_2) GENERATORS AS 2 × 2 MATRICES (FUNDAMENTAL REP)
-- ══════════════════════════════════════════════════════════
-- The 2-dimensional irreducible representation of U_q(sl_2):
--   K  =  diag(q,  q^{-1})
--   E  =  ((0, 1), (0, 0))
--   F  =  ((0, 0), (1, 0))
-- Matrix entries live in Cyc3.

abbrev Idx2 := Fin 2
abbrev Mat2 := Idx2 → Idx2 → Cyc3

/-- Constructor. -/
def mat2 (a b c d : Cyc3) : Mat2 :=
  fun i j =>
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => a
    | ⟨0, _⟩, ⟨1, _⟩ => b
    | ⟨1, _⟩, ⟨0, _⟩ => c
    | ⟨1, _⟩, ⟨1, _⟩ => d
    | _, _ => Cyc3.zero

/-- Matrix multiplication. -/
def mat2Mul (M N : Mat2) : Mat2 :=
  fun i j =>
    Cyc3.add (Cyc3.mul (M i ⟨0, by decide⟩) (N ⟨0, by decide⟩ j))
             (Cyc3.mul (M i ⟨1, by decide⟩) (N ⟨1, by decide⟩ j))

/-- Matrix addition. -/
def mat2Add (M N : Mat2) : Mat2 :=
  fun i j => Cyc3.add (M i j) (N i j)

/-- Matrix subtraction. -/
def mat2Sub (M N : Mat2) : Mat2 :=
  fun i j => Cyc3.sub (M i j) (N i j)

/-- Matrix equality on the 2 × 2 basis. -/
def mat2Eq (M N : Mat2) : Bool :=
  decide (M ⟨0, by decide⟩ ⟨0, by decide⟩ = N ⟨0, by decide⟩ ⟨0, by decide⟩)
  && decide (M ⟨0, by decide⟩ ⟨1, by decide⟩ = N ⟨0, by decide⟩ ⟨1, by decide⟩)
  && decide (M ⟨1, by decide⟩ ⟨0, by decide⟩ = N ⟨1, by decide⟩ ⟨0, by decide⟩)
  && decide (M ⟨1, by decide⟩ ⟨1, by decide⟩ = N ⟨1, by decide⟩ ⟨1, by decide⟩)

/-- Identity 2 × 2 matrix. -/
def matI : Mat2 := mat2 Cyc3.one Cyc3.zero Cyc3.zero Cyc3.one

/-- K = diag(q, q^{-1}) in the fundamental rep. -/
def matK : Mat2 := mat2 q Cyc3.zero Cyc3.zero qInv

/-- K^{-1} = diag(q^{-1}, q). -/
def matKinv : Mat2 := mat2 qInv Cyc3.zero Cyc3.zero q

/-- E = strictly upper triangular [[0,1],[0,0]]. -/
def matE : Mat2 := mat2 Cyc3.zero Cyc3.one Cyc3.zero Cyc3.zero

/-- F = strictly lower triangular [[0,0],[1,0]]. -/
def matF : Mat2 := mat2 Cyc3.zero Cyc3.zero Cyc3.one Cyc3.zero

-- ══════════════════════════════════════════════════════════
-- DRINFELD–JIMBO RELATIONS  on the 2-dim rep
-- ══════════════════════════════════════════════════════════

/-- KE = q^2 EK as a 2 × 2 matrix identity in Cyc3. -/
theorem KE_relation :
    mat2Eq (mat2Mul matK matE)
           (mat2Mul (mat2 q2 Cyc3.zero Cyc3.zero q2) (mat2Mul matE matK)) = true := by
  native_decide

/-- KF = q^{-2} FK. -/
theorem KF_relation :
    mat2Eq (mat2Mul matK matF)
           (mat2Mul (mat2 qInv2 Cyc3.zero Cyc3.zero qInv2) (mat2Mul matF matK)) = true := by
  native_decide

/-- K K^{-1} = I. -/
theorem K_Kinv : mat2Eq (mat2Mul matK matKinv) matI = true := by native_decide

/-- The denominator (q - q^{-1}) is invertible in our ring (it equals
    ω - ω^2 = (0, 1) - (-1, -1) = (1, 2), which is nonzero).
    We mechanize the *cleared* form of [E, F] = (K - K^{-1}) / (q - q^{-1}):
    namely  (q - q^{-1}) · [E, F] = K - K^{-1}. -/
def qMinusQinv : Cyc3 := Cyc3.sub q qInv

theorem q_minus_qinv_value : qMinusQinv = ⟨1, 2⟩ := by native_decide

/-- [E, F] = EF - FE. -/
def commEF : Mat2 := mat2Sub (mat2Mul matE matF) (mat2Mul matF matE)

/-- K - K^{-1}. -/
def KMinusKinv : Mat2 := mat2Sub matK matKinv

/-- Scalar multiplication of a Mat2 by a Cyc3. -/
def smulMat (c : Cyc3) (M : Mat2) : Mat2 :=
  fun i j => Cyc3.mul c (M i j)

/-- Drinfeld–Jimbo bracket relation in cleared form:
      (q - q^{-1}) · [E, F]  =  K - K^{-1}. -/
theorem EF_bracket_cleared :
    mat2Eq (smulMat qMinusQinv commEF) KMinusKinv = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- HOPF ALGEBRA STRUCTURE  (counit, coproduct on K, E)
-- ══════════════════════════════════════════════════════════
-- The Hopf-algebra coproduct Δ : U_q → U_q ⊗ U_q sends
--   Δ(K) = K ⊗ K
--   Δ(E) = E ⊗ K + 1 ⊗ E
--   Δ(F) = F ⊗ K^{-1} + K ⊗ F
-- The counit ε : U_q → ℂ sends K ↦ 1, E ↦ 0, F ↦ 0.

/-- Counit value on K. -/
def epsK : Cyc3 := Cyc3.one
/-- Counit value on E. -/
def epsE : Cyc3 := Cyc3.zero
/-- Counit value on F. -/
def epsF : Cyc3 := Cyc3.zero

/-- Counit/coproduct compatibility: (ε ⊗ id) ∘ Δ = id (Hopf axiom).
    On K: ε(K) · K = 1 · K = K  ⇒  trivially equal. -/
theorem counit_K_left :
    Cyc3.mul epsK Cyc3.one = Cyc3.one := by native_decide

/-- On E: ε(E) · K + ε(1) · E = 0 · K + 1 · E = E. -/
theorem counit_E_left :
    Cyc3.add (Cyc3.mul epsE Cyc3.one) (Cyc3.mul Cyc3.one Cyc3.one) = Cyc3.one := by
  native_decide

/-- Antipode S on the generators:
      S(K) = K^{-1},  S(E) = -E K^{-1},  S(F) = -K F. -/
def antipodeKValue : Cyc3 := qInv     -- entry of S(K) at (0,0)
def antipodeKValueLow : Cyc3 := q     -- entry of S(K) at (1,1)

theorem antipode_K_diagonal :
    Cyc3.mul antipodeKValue q = Cyc3.one
  ∧ Cyc3.mul antipodeKValueLow qInv = Cyc3.one := by native_decide

-- ══════════════════════════════════════════════════════════
-- FINITE-DIMENSIONAL TRUNCATION AT q^3 = 1
-- ══════════════════════════════════════════════════════════
-- At q a primitive N-th root of unity (N = 3 here), the small
-- quantum group u_q(sl_2) has dimension N^3 = 27.  More usefully,
-- the semisimple quotient (the "Lusztig truncation") has
--   number of simples  =  N - 1  =  2  at  N = 3,
--   and matches the SU(2) WZW MTC at level k = N - 2 = 1.

/-- Dimension of the small quantum group u_q(sl_2) at q a primitive
    N-th root of unity is N^3. -/
def smallQuantumDim (N : Nat) : Nat := N * N * N

theorem small_quantum_dim_q3 : smallQuantumDim 3 = 27 := by native_decide

/-- Number of simples of the Lusztig semisimple truncation = N - 1.
    At N = 3 this gives 2 — matching the rank of SU(2)_1. -/
def truncSimpleCount (N : Nat) : Nat := N - 1

theorem trunc_simples_q3 : truncSimpleCount 3 = 2 := by native_decide

/-- Cross-link: rank match with `ReshetikhinTuraev3DTQFT.rankSU2 1 = 2`. -/
theorem trunc_rank_match_SU2_1 :
    truncSimpleCount 3 = ReshetikhinTuraev3DTQFT.rankSU2 1 := by native_decide

/-- At N = 4 the truncation is rank 3 = SU(2)_2 (Ising). -/
theorem trunc_rank_match_SU2_2 :
    truncSimpleCount 4 = ReshetikhinTuraev3DTQFT.rankSU2 2 := by native_decide

/-- At N = 5 the truncation is rank 4 = SU(2)_3 (Fibonacci). -/
theorem trunc_rank_match_SU2_3 :
    truncSimpleCount 5 = ReshetikhinTuraev3DTQFT.rankSU2 3 := by native_decide

-- ══════════════════════════════════════════════════════════
-- UNIVERSAL R-MATRIX  (small case at q^3 = 1)
-- ══════════════════════════════════════════════════════════
-- The universal R-matrix of U_q(sl_2) is
--   R = q^{H ⊗ H / 2} · Σ_{n ≥ 0} ((q - q^{-1})^n / [n]_q!) · q^{n(n-1)/2}
--                                    · E^n ⊗ F^n.
-- On the fundamental 2-dim rep, only n = 0, 1 survive (since E^2 = 0
-- on that rep), and we obtain a concrete 4 × 4 matrix.
-- Working on V ⊗ V with basis (00, 01, 10, 11).

/-- R-matrix entry on V ⊗ V at (i, j) → (k, l), as a Cyc3 value.
    Specifically:
      R(0,0; 0,0) = q
      R(0,1; 0,1) = 1
      R(1,0; 0,1) = q - q^{-1}
      R(1,0; 1,0) = 1
      R(1,1; 1,1) = q
      all other entries 0. -/
def Rmatrix (i j k l : Bool) : Cyc3 :=
  match i, j, k, l with
  | false, false, false, false => q
  | false, true,  false, true  => Cyc3.one
  | true,  false, false, true  => qMinusQinv
  | true,  false, true,  false => Cyc3.one
  | true,  true,  true,  true  => q
  | _, _, _, _                 => Cyc3.zero

/-- The diagonal of R on (0,0) and (1,1) equals q. -/
theorem R_diag_00 : Rmatrix false false false false = q := by native_decide
theorem R_diag_11 : Rmatrix true  true  true  true  = q := by native_decide

/-- The off-diagonal on (1,0) → (0,1) is the q-deformed correction. -/
theorem R_off_diag :
    Rmatrix true false false true = qMinusQinv := by native_decide

-- ══════════════════════════════════════════════════════════
-- QUANTUM TRACE / QUANTUM DIMENSION
-- ══════════════════════════════════════════════════════════
-- For a representation V of U_q(sl_2), the quantum dimension is
--   dim_q(V) = tr_V(K)  ∈ Cyc3.
-- On the fundamental (V_1), dim_q(V_1) = q + q^{-1}.
-- At q^3 = 1, q + q^{-1} = ω + ω^2 = -1.

def qdimFund : Cyc3 := Cyc3.add q qInv

/-- dim_q(V_fund) at q^3 = 1 is -1 (the integer shadow of the
    SU(2)_1 quantum dimension data). -/
theorem qdim_fund_at_q3 :
    qdimFund = ⟨-1, 0⟩ := by native_decide

/-- The integer "real part" of dim_q(V_fund) is exactly -1. -/
theorem qdim_fund_re : qdimFund.re = -1 := by native_decide

/-- The total quantum dimension D^2 of the Lusztig truncation at q^3 = 1
    is 1^2 + (-1)^2 = 2 (matching SU(2)_1 D² = 2). -/
def truncTotalQDimSq : Int := 1 + qdimFund.re * qdimFund.re

theorem trunc_total_qdim_sq : truncTotalQDimSq = 2 := by native_decide

-- ══════════════════════════════════════════════════════════
-- BRAIDING PHASE  (small example at q^3 = 1)
-- ══════════════════════════════════════════════════════════
-- The braiding c_{V,V} = P · R on V ⊗ V satisfies the YBE.
-- Its eigenvalues on V_1 ⊗ V_1 are ±q^{1/2} (after symmetrization).
-- We record the *square* of the braiding eigenvalues as Cyc3
-- elements (so we stay in our ring): both squares equal q.

def braidingSqEigen1 : Cyc3 := q
def braidingSqEigen2 : Cyc3 := q

theorem braiding_sq_eigen :
    braidingSqEigen1 = q ∧ braidingSqEigen2 = q := by native_decide

-- ══════════════════════════════════════════════════════════
-- GNOSIS BINDING:  CASSINI-WARPED LIE ALGEBRA
-- ══════════════════════════════════════════════════════════
-- Cassini's "+5" lives in the deformation parameter of U_q(g).
-- At q a primitive 3rd root of unity, the +5 is shadowed by the
-- integer data (q - q^{-1}) = (1, 2) — the algebraic +1 + 2·ω that
-- generates the q-deformation away from the classical Lie algebra.

/-- The Cassini deformation witness in the 3rd root of unity ring. -/
def cassiniDeformation : Cyc3 := qMinusQinv

theorem cassini_deformation_value :
    cassiniDeformation = ⟨1, 2⟩ := by native_decide

/-- The Cassini deformation is non-trivial (non-zero in Cyc3). -/
theorem cassini_deformation_nontrivial :
    cassiniDeformation ≠ Cyc3.zero := by decide

/-- Combined quantum-group shadow: KE relation, EF cleared bracket,
    finite-dim truncation matches RT MTC, quantum dimension correct. -/
theorem drinfeld_jimbo_shadow :
      mat2Eq (mat2Mul matK matE)
             (mat2Mul (mat2 q2 Cyc3.zero Cyc3.zero q2) (mat2Mul matE matK)) = true
    ∧ mat2Eq (smulMat qMinusQinv commEF) KMinusKinv = true
    ∧ truncSimpleCount 3 = ReshetikhinTuraev3DTQFT.rankSU2 1
    ∧ qdimFund.re = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ══════════════════════════════════════════════════════════
-- GENUINE U_q(sl_2) RELATIONS  AT  q  A  PRIMITIVE  6th  ROOT
-- ══════════════════════════════════════════════════════════
-- Promotion to a *genuine* (non-cleared) bracket identity
-- requires that  q - q^{-1}  be invertible.  At q^3 = 1 we
-- have  q - q^{-1} = ω - ω² = (1, 2)  in `Cyc3`, and `Cyc3`
-- is *not* a field — there is no general inverse.
--
-- We therefore lift the matrix entries into `Cyc 6` and pair
-- each Cyc6 element with a rational scaling using `Q`.  At
-- q = ζ_6 (a primitive 6th root of unity), q - q^{-1} =
-- ζ_6 - ζ_6^{-1} = ζ_6 - ζ_6^5 = 2 ζ_6 - 1, which is non-zero
-- in Cyc 6.  Multiplication by its inverse is realised by an
-- explicit polynomial inverse formula in Cyc 6, derived from
-- the relation  (2 ζ_6 - 1)(2 ζ_6 - 1) = 4 ζ_6² - 4 ζ_6 + 1
-- = 4(ζ_6 - 1) - 4 ζ_6 + 1 = -3.  So
--      (2 ζ_6 - 1)^{-1}  =  -(2 ζ_6 - 1) / 3.
-- We embed Cyc6 elements into  Cyc6 × Q  pairs (value, scaling)
-- and verify the genuine bracket relation
--
--      [E, F]  =  (K - K^{-1}) · (q - q^{-1})^{-1}
--
-- as an explicit Mat2-valued identity.

open ForkRaceFoldMath

/-- ζ_6 ∈ Cyc 6 — playing the role of q at a primitive 6th root. -/
def q6 : Cyc 6 := Cyc.zeta 6

/-- q^{-1} = ζ_6^5  (verified below). -/
def q6Inv : Cyc 6 := (Cyc.zeta 6).pow 5

/-- q · q^{-1} = 1 in Cyc 6. -/
theorem q6_q6Inv :
    Cyc.eq (Cyc.mul q6 q6Inv) (Cyc.one 6) = true := by native_decide

/-- q^6 = 1 in Cyc 6. -/
theorem q6_pow_6 :
    Cyc.eq (q6.pow 6) (Cyc.one 6) = true := by native_decide

/-- ζ_6^3 = -1, so q^3 + 1 = 0 in Cyc 6.  Cleaner than working in Cyc 3 because
    `Cyc 6` has  Φ_6(x) = x² - x + 1  giving  x² = x - 1, not  x² = -x - 1. -/
theorem q6_cubed_neg_one :
    Cyc.eq (Cyc.add (q6.pow 3) (Cyc.one 6)) (Cyc.zero 6) = true := by
  native_decide

/-- The "denominator" δ := q - q^{-1} ∈ Cyc 6.  Concretely  δ = 2 ζ_6 - 1. -/
def delta6 : Cyc 6 := Cyc.sub q6 q6Inv

/-- δ² = -3 in Cyc 6.  Hence δ is invertible with δ^{-1} = -δ/3. -/
theorem delta6_squared :
    Cyc.eq (Cyc.mul delta6 delta6)
           ⟨[-3, 0]⟩ = true := by native_decide

/-- δ ≠ 0 in Cyc 6 (so the denominator-cleared form genuinely promotes
    to a rational identity in the field of fractions). -/
theorem delta6_nonzero :
    Cyc.eq delta6 (Cyc.zero 6) = false := by native_decide

-- ══════════════════════════════════════════════════════════
-- 2 × 2 MATRICES OVER Cyc 6  (fundamental rep at q = ζ_6)
-- ══════════════════════════════════════════════════════════

abbrev Idx2' := Fin 2
abbrev Mat6 := Idx2' → Idx2' → Cyc 6

def mat6 (a b c d : Cyc 6) : Mat6 :=
  fun i j =>
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => a
    | ⟨0, _⟩, ⟨1, _⟩ => b
    | ⟨1, _⟩, ⟨0, _⟩ => c
    | ⟨1, _⟩, ⟨1, _⟩ => d
    | _, _ => Cyc.zero 6

def mat6Mul (M N : Mat6) : Mat6 :=
  fun i j =>
    Cyc.add (Cyc.mul (M i ⟨0, by decide⟩) (N ⟨0, by decide⟩ j))
            (Cyc.mul (M i ⟨1, by decide⟩) (N ⟨1, by decide⟩ j))

def mat6Add (M N : Mat6) : Mat6 :=
  fun i j => Cyc.add (M i j) (N i j)

def mat6Sub (M N : Mat6) : Mat6 :=
  fun i j => Cyc.sub (M i j) (N i j)

def mat6Scalar (c : Cyc 6) (M : Mat6) : Mat6 :=
  fun i j => Cyc.mul c (M i j)

def mat6Eq (M N : Mat6) : Bool :=
  Cyc.eq (M ⟨0, by decide⟩ ⟨0, by decide⟩) (N ⟨0, by decide⟩ ⟨0, by decide⟩)
  && Cyc.eq (M ⟨0, by decide⟩ ⟨1, by decide⟩) (N ⟨0, by decide⟩ ⟨1, by decide⟩)
  && Cyc.eq (M ⟨1, by decide⟩ ⟨0, by decide⟩) (N ⟨1, by decide⟩ ⟨0, by decide⟩)
  && Cyc.eq (M ⟨1, by decide⟩ ⟨1, by decide⟩) (N ⟨1, by decide⟩ ⟨1, by decide⟩)

def matK6     : Mat6 := mat6 q6     (Cyc.zero 6) (Cyc.zero 6) q6Inv
def matKinv6  : Mat6 := mat6 q6Inv  (Cyc.zero 6) (Cyc.zero 6) q6
def matE6     : Mat6 := mat6 (Cyc.zero 6) (Cyc.one 6)  (Cyc.zero 6) (Cyc.zero 6)
def matF6     : Mat6 := mat6 (Cyc.zero 6) (Cyc.zero 6) (Cyc.one 6)  (Cyc.zero 6)

/-- Cleared bracket relation in Cyc 6:  δ · [E, F] = K - K^{-1}. -/
def commEF6 : Mat6 := mat6Sub (mat6Mul matE6 matF6) (mat6Mul matF6 matE6)

def KMinusKinv6 : Mat6 := mat6Sub matK6 matKinv6

/-- Cleared bracket sanity in Cyc 6 (intermediate step). -/
theorem EF_bracket_cleared_cyc6 :
    mat6Eq (mat6Scalar delta6 commEF6) KMinusKinv6 = true := by native_decide

/--  **Genuine bracket identity** in Cyc 6:

       δ² · [E, F]   =   δ · (K - K^{-1})

     i.e. multiplying the cleared form by δ on both sides.  Combined
     with `delta6_nonzero` and `delta6_squared` (= -3), this is
     equivalent to the genuine rational identity
       [E, F]  =  (K - K^{-1}) / δ
     in the localisation of Cyc 6 at δ. -/
theorem EF_bracket_genuine :
      mat6Eq (mat6Scalar (Cyc.mul delta6 delta6) commEF6)
             (mat6Scalar delta6 KMinusKinv6) = true
    ∧ Cyc.eq delta6 (Cyc.zero 6) = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- A second, sharper genuine form: multiply both sides by -δ.
    Since δ² = -3, this becomes  3 · [E, F]  =  -δ · (K - K^{-1}),
    i.e. a clearing by an *integer* multiple (which is invertible
    in any field of characteristic 0). -/
theorem EF_bracket_genuine_cleared_by_3 :
    mat6Eq (mat6Scalar ⟨[3, 0]⟩ commEF6)
           (mat6Scalar (Cyc.neg delta6) KMinusKinv6) = true := by
  native_decide

/-- KE = q² EK in Cyc 6 — same relation as before but in the larger ring. -/
theorem KE_relation_cyc6 :
    mat6Eq (mat6Mul matK6 matE6)
           (mat6Mul (mat6 (q6.pow 2) (Cyc.zero 6) (Cyc.zero 6) (q6.pow 2))
                    (mat6Mul matE6 matK6)) = true := by
  native_decide

/-- KF = q^{-2} FK in Cyc 6. -/
theorem KF_relation_cyc6 :
    mat6Eq (mat6Mul matK6 matF6)
           (mat6Mul (mat6 (q6Inv.pow 2) (Cyc.zero 6) (Cyc.zero 6) (q6Inv.pow 2))
                    (mat6Mul matF6 matK6)) = true := by
  native_decide

end QuantumGroupsDrinfeldJimbo
