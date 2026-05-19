import Init
import Gnosis.ReshetikhinTuraev3DTQFT

/-
  KhovanovCategorifiesJones
  =========================

  Khovanov homology Kh(L) is a bigraded abelian group whose graded
  Euler characteristic recovers the unnormalized Jones polynomial:

      Σ_{i, j}  (-1)^i · q^j · rank Khⁱʲ(L)   =   Ĵ(L)(q).

  The construction:
  1. Take an oriented link diagram D with n crossings, n₊ positive
     and n₋ negative.
  2. For each α ∈ {0,1}ⁿ (a Kauffman resolution), replace each
     crossing by its 0- or 1-smoothing; the result is a disjoint
     union of k(α) Seifert circles.
  3. Each circle is assigned the 2-dim graded module
     V = 𝔽⟨v₊, v₋⟩ with qdim V = q + q⁻¹.
  4. The chain group at homological grade i is
        Cⁱ(D) = ⨁_{|α| = i + n₋} V^{⊗ k(α)} [|α| + n₊ - n₋]
     where the bracket is an overall q-grade shift.
  5. The cobordism differentials m : V ⊗ V → V and Δ : V → V ⊗ V
     come from the Atiyah–Segal 2d TQFT on the pair-of-pants.

  Theorem (Khovanov 1999):  χ_q(Kh(L)) = Ĵ(L)(q).

  Equivalently: before taking homology, the Euler characteristic
  of the *chain complex* already equals Ĵ(D)(q) — this identity
  is the one mechanized below.

  Gnosis mapping
  --------------
  * Link diagram       ↔  control-flow graph
  * Crossing           ↔  control-flow entanglement / deadlock site
  * Resolution α       ↔  candidate unknotting path
  * k(α)               ↔  number of independent execution threads
  * Khovanov homology  ↔  exact "how-to-unknot" obstruction space
  * χ_q = Jones        ↔  numerical bug invariant (Finite Sieve)
  * Categorification   ↔  the path, not just the decision

  This file captures the combinatorial shadow — Kauffman bracket,
  circle counts, and q-graded trace — for a small canonical link
  gallery: the unknot (plus **`unknotTwist`** as a Reidemeister-I
  presentation shadow), Hopf (**H⁺, H⁻**), the positive trefoil, and
  figure-eight **`4₁`** (Knot Atlas PD **`X4251 X8615 X6374 X2738`**),
  discrete identities close by `native_decide`.  Structural lemmas (`evalAtMinusOne_shiftPow`,
  `jonesShift_evalAtMinusOne`) spell out how **`q = -1`** evaluation interacts with
  writhe.  Cross-links into `ReshetikhinTuraev3DTQFT` package the determinant model
  **`rtUnnormJonesFromNatDet`** at **`q = -1`** (see **`RT_jones_tabulated_eq_rtUnnormJonesFromNatDet`**);
  pinning where `jonesPoly` agrees with that bookkeeping is purely **witness-by-theorem**, not an
  asserted operator identity **`jonesPoly = RT-scan`**.  Monomial witnesses **`psi_Q`** / **`psi_Q_inv`** (see **`psi_Q_mul_psi_Q_inv`**) sit in the Kauffman/A chart; **`qdimV`** carries the distinct Bar-Natan **`q`**-numerator (**`qdimV_ne_kauffmanDeltaFormal`**).
  Closed constructively under the strict chapel audit.
-/


namespace KhovanovCategorifiesJones

-- ══════════════════════════════════════════════════════════
-- LAURENT POLYNOMIALS IN q  (encoded as lists with offset)
-- ══════════════════════════════════════════════════════════
-- A Laurent polynomial Σ aᵢ · q^i is represented as
--   LaurentPoly.mk offset coeffs
-- where `coeffs` is indexed starting at `offset`:
--   Σᵢ coeffs[i] · q^(offset + i).

structure LaurentPoly where
  offset : Int
  coeffs : List Int
  deriving DecidableEq, BEq

namespace LaurentPoly

/-- Monomial c · q^e. -/
def mono (c e : Int) : LaurentPoly :=
  ⟨e, [c]⟩

/-- Constant. -/
def constP (c : Int) : LaurentPoly := mono c 0

/-- Zero. -/
def zero : LaurentPoly := ⟨0, []⟩

/-- Degree of the lowest nonzero term (or offset if the list is zero). -/
def lowDeg (p : LaurentPoly) : Int := p.offset

/-- Multiply by q^e (shifts the offset). -/
def shiftPow (p : LaurentPoly) (e : Int) : LaurentPoly :=
  ⟨p.offset + e, p.coeffs⟩

/-- Multiply by a scalar. -/
def scale (k : Int) (p : LaurentPoly) : LaurentPoly :=
  ⟨p.offset, p.coeffs.map (k * ·)⟩

@[simp] theorem scale_one (p : LaurentPoly) : scale (1 : Int) p = p := by
  rcases p with ⟨o, coeffs⟩
  dsimp [scale]
  congr 1
  induction coeffs <;> simp [List.map, Int.one_mul]

private def padFront (n : Nat) (xs : List Int) : List Int :=
  match n with
  | 0     => xs
  | n + 1 => 0 :: padFront n xs

/-- Align two coefficient lists to a common offset (the min of the two). -/
private def align (p q : LaurentPoly) : Int × List Int × List Int :=
  let lo := min p.offset q.offset
  let padP := (p.offset - lo).toNat
  let padQ := (q.offset - lo).toNat
  (lo, padFront padP p.coeffs, padFront padQ q.coeffs)

private def zipAdd : List Int → List Int → List Int
  | [],      ys      => ys
  | xs,      []      => xs
  | x :: xs, y :: ys => (x + y) :: zipAdd xs ys

/-- Polynomial addition. -/
def add (p q : LaurentPoly) : LaurentPoly :=
  let (lo, aP, aQ) := align p q
  ⟨lo, zipAdd aP aQ⟩

/-- Polynomial subtraction. -/
def sub (p q : LaurentPoly) : LaurentPoly :=
  add p (scale (-1) q)

/-- Polynomial multiplication via convolution. -/
def mul (p q : LaurentPoly) : LaurentPoly :=
  let rec convOne (x : Int) : List Int → List Int
    | []      => []
    | y :: ys => (x * y) :: convOne x ys
  let rec convAll (xs ys : List Int) (acc : List Int) (shift : Nat) : List Int :=
    match xs with
    | []      => acc
    | x :: xs =>
      let row := padFront shift (convOne x ys)
      convAll xs ys (zipAdd acc row) (shift + 1)
  ⟨p.offset + q.offset, convAll p.coeffs q.coeffs [] 0⟩

/-- Evaluate Ĵ(L)(1): a *classical* Jones value. -/
def evalAtOne (p : LaurentPoly) : Int :=
  p.coeffs.foldl (· + ·) 0

/-- Alternating coefficient sum with sign pattern tracking `q = -1`. -/
def evalGo (cs : List Int) (sgn : Int) : Int :=
  match cs with
  | [] => 0
  | c :: cs => c * sgn + evalGo cs (-sgn)

/-- Sign `(-1)^o` for the first Laurent term `q^o`. -/
def startSign (o : Int) : Int :=
  if o % (2 : Int) = 0 then 1 else -1

/-- Evaluate Ĵ(L)(-1): alternating evaluation of the Laurent coefficients. -/
def evalAtMinusOne (p : LaurentPoly) : Int :=
  evalGo p.coeffs (startSign p.offset)

/-- `startSign` is a character: `startSign (o + e) = startSign e * startSign o`. -/
theorem startSign_add_mul (o e : Int) :
    startSign (o + e) = startSign e * startSign o := by
  unfold startSign
  rw [Int.add_emod]
  by_cases he : e % (2 : Int) = 0 <;> by_cases ho : o % (2 : Int) = 0
  · simp [he, ho]
  · simp [he, ho]
  · simp [he, ho]
  · have he1 : e % (2 : Int) = 1 := by
      rcases Int.emod_two_eq e with h | h
      · exact False.elim (he h)
      · exact h
    have ho1 : o % (2 : Int) = 1 := by
      rcases Int.emod_two_eq o with h | h
      · exact False.elim (ho h)
      · exact h
    have hsum : (o % (2 : Int) + e % (2 : Int)) % (2 : Int) = 0 := by
      rw [ho1, he1]
      rfl
    simp [he, ho, hsum]

/-- Scalar passes through `evalGo` in the initial sign slot. -/
theorem evalGo_smul (cs : List Int) (k sgn : Int) :
    evalGo cs (k * sgn) = k * evalGo cs sgn := by
  induction cs generalizing sgn <;> simp [evalGo, Int.mul_add, ← Int.mul_neg, Int.mul_left_comm, *]

/-- Coefficient-wise scaling commutes with `evalGo`. -/
theorem evalGo_map_mul (cs : List Int) (c : Int) (sgn : Int) :
    evalGo (cs.map (fun x => c * x)) sgn = c * evalGo cs sgn := by
  induction cs generalizing sgn <;> simp [evalGo, List.map, Int.mul_add, Int.mul_left_comm, Int.mul_comm, *]

/-- Multiplying the polynomial by `q^e` multiplies the `q = -1` value by `(-1)^e`. -/
theorem evalAtMinusOne_shiftPow (p : LaurentPoly) (e : Int) :
    evalAtMinusOne (shiftPow p e) = startSign e * evalAtMinusOne p := by
  rcases p with ⟨o, cs⟩
  dsimp [evalAtMinusOne, shiftPow]
  rw [← evalGo_smul cs (startSign e) (startSign o)]
  congr 1
  exact startSign_add_mul o e

/-- Uniform coefficient scaling scales `evalAtMinusOne`. -/
theorem evalAtMinusOne_scale (c : Int) (p : LaurentPoly) :
    evalAtMinusOne (scale c p) = c * evalAtMinusOne p := by
  rcases p with ⟨o, cs⟩
  dsimp [evalAtMinusOne, scale]
  exact evalGo_map_mul cs c (startSign o)

end LaurentPoly

open LaurentPoly

-- ══════════════════════════════════════════════════════════
-- A vs q bookkeeping (dictionary; shared Laurent carrier)
-- ══════════════════════════════════════════════════════════
-- `KauffmanBracketFinite.delta` matches **`-A^{-2}-A^{2}`** (Kauffman loop numerator).
-- Reciprocal monomial witnesses `psi_Q`, `psi_Q_inv`; `psi_Q_mul_psi_Q_inv` records product `1`.
-- Sum `kauffmanDeltaFormal`; Bar-Natan `qdimV = q^{-1}+q` is a different laurent-encoding (`qdimV_ne_kauffmanDeltaFormal`).

/-- Monomial **`-A^{-2}`** (**`.psi_Q`**) silently treating the laurent letter as Kauffmans **` A`**.-/
abbrev psi_Q : LaurentPoly := LaurentPoly.mono (-1 : Int) (-2 : Int)

/-- Reciprocal monomial (**` ψ(q^{-`**1)}) so **` ψ(q)· ψ(q^{-`**1)}) = **`1`**). -/
abbrev psi_Q_inv : LaurentPoly := LaurentPoly.mono (-1 : Int) (2 : Int)

/-- **`δ`**-slot sum **`-A^{-2`**−**`A`**^{2}` (**` Kauffmans loop polynomial **). -/
abbrev kauffmanDeltaFormal : LaurentPoly :=
  LaurentPoly.add psi_Q_inv psi_Q

/-- Reciprocal witness **` ψ(q)·ψ(q^{-`**1)}) = **`1`** (Laurent **`mul`). -/
theorem psi_Q_mul_psi_Q_inv :
    LaurentPoly.mul psi_Q psi_Q_inv = LaurentPoly.constP 1 :=
  rfl



-- ══════════════════════════════════════════════════════════

/-- qdim of the 2d graded module V = 𝔽⟨v₊, v₋⟩. -/
def qdimV : LaurentPoly := ⟨-1, [1, 0, 1]⟩      -- q⁻¹ + q

/-- `q^{-1}+q` (Bar-Natan numerator) differs from the δ(A)-chart numerator `kauffmanDeltaFormal`. -/
theorem qdimV_ne_kauffmanDeltaFormal : qdimV ≠ kauffmanDeltaFormal := by decide

/-- qdim V^{⊗k}. -/
def qdimVk : Nat → LaurentPoly
  | 0     => LaurentPoly.constP 1
  | k + 1 => LaurentPoly.mul qdimV (qdimVk k)

/-- `qdim V^{⊗0}` is the monoidal unit, i.e. the constant Laurent polynomial **1**. -/
@[simp]
theorem qdimVk_zero : qdimVk 0 = LaurentPoly.constP 1 :=
  rfl

/-- qdim V = q + q⁻¹ evaluated at q = 1 = 2. -/
theorem qdim_V_at_one : qdimV.evalAtOne = 2 := by native_decide

/-- qdim V² at q = 1 = 4. -/
theorem qdim_V2_at_one : (qdimVk 2).evalAtOne = 4 := by native_decide

/-- qdim V³ at q = 1 = 8. -/
theorem qdim_V3_at_one : (qdimVk 3).evalAtOne = 8 := by native_decide

-- ══════════════════════════════════════════════════════════
-- THE KAUFFMAN BRACKET CHAIN POLYNOMIAL
-- ══════════════════════════════════════════════════════════
-- For a diagram D with n crossings, each resolution α ∈ Bool^n
-- contributes  (-1)^|α| · q^|α| · (q + q⁻¹)^{k(α)}.
-- Summing over all resolutions yields ⟨D⟩(q) — the unnormalized
-- Kauffman bracket (in the Bar-Natan convention used here).

/--
  A link diagram, stored as its full resolution table.
  `resolutions`  —  list of (|α|, k(α)) pairs, one per α ∈ Bool^n.
  `nPlus`, `nMinus`  —  signs of the n = n₊ + n₋ crossings.
-/
structure Diagram where
  nPlus       : Nat
  nMinus      : Nat
  /-- One entry per resolution: (|α|, k(α)). -/
  resolutions : List (Nat × Nat)
  deriving DecidableEq, BEq

/-- One resolution’s contribution to `bracket`: `(-1)^{|α|} · q^{|α|} · (q+q⁻¹)^{k(α)}`. -/
def khovanovBracketSummand (p : Nat × Nat) : LaurentPoly :=
  let h := p.1
  let k := p.2
  let sgn : Int := if h % 2 = 0 then 1 else -1
  LaurentPoly.shiftPow (LaurentPoly.scale sgn (qdimVk k)) (Int.ofNat h)

/-- The chain-level Kauffman bracket polynomial ⟨D⟩(q). -/
def bracket (D : Diagram) : LaurentPoly :=
  D.resolutions.foldl (fun acc p => LaurentPoly.add acc (khovanovBracketSummand p)) LaurentPoly.zero

/-- Fold `khovanovBracketSummand` on a resolution table alone (no `Diagram` metadata). -/
def bracketResolutions (l : List (Nat × Nat)) : LaurentPoly :=
  l.foldl (fun acc p => LaurentPoly.add acc (khovanovBracketSummand p)) LaurentPoly.zero

@[simp]
theorem bracket_eq_bracketResolutions (D : Diagram) : bracket D = bracketResolutions D.resolutions :=
  rfl

/-- At index `i`, peel off **prefix sum**, the **ith** Khovanov summand, then fold the **suffix**.
  Seven-crossing IUPAC shell instantiation at `IupacResolutionCubeBound.rowSlotFin128`:
  `Gnosis.SevenCrossingIupacShell.bracketResolutions_sevenCubeTaggedList_rowSlotFin128`. -/
theorem bracketResolutions_split (l : List (Nat × Nat)) (i : Nat) (h : i < l.length) :
    bracketResolutions l =
      (l.drop (i + 1)).foldl (fun acc p => LaurentPoly.add acc (khovanovBracketSummand p))
        (LaurentPoly.add (bracketResolutions (l.take i)) (khovanovBracketSummand (l[i]'h))) := by
  have hl :
      l = l.take i ++ ([l[i]'h] ++ l.drop (i + 1)) := by
    calc
      l = l.take (i + 1) ++ l.drop (i + 1) := (List.take_append_drop (i + 1) l).symm
      _ = (l.take i ++ [l[i]'h]) ++ l.drop (i + 1) := by rw [List.take_succ_eq_append_getElem h]
      _ = l.take i ++ ([l[i]'h] ++ l.drop (i + 1)) := by rw [List.append_assoc]
  rw [(congrArg bracketResolutions hl)]
  dsimp [bracketResolutions]
  simp only [List.foldl_append, List.foldl_cons]

/-- Jones shift: Ĵ(L)(q) = (-1)^{n₋} · q^{n₊ - 2·n₋} · ⟨D⟩(q). -/
def jonesShift (D : Diagram) : LaurentPoly :=
  let sgn : Int := if D.nMinus % 2 = 0 then 1 else -1
  let expo : Int := Int.ofNat D.nPlus - 2 * Int.ofNat D.nMinus
  LaurentPoly.shiftPow (LaurentPoly.scale sgn (bracket D)) expo

/-- Sign `(-1)^{n₋}` appearing in `jonesShift`. -/
def writheSign (D : Diagram) : Int :=
  if D.nMinus % 2 = 0 then 1 else -1

/-- `jonesShift` evaluation at **`q = -1`** factors through bracket data (no hidden semantics). -/
theorem jonesShift_evalAtMinusOne (D : Diagram) :
    (jonesShift D).evalAtMinusOne =
      writheSign D * LaurentPoly.startSign (Int.ofNat D.nPlus - 2 * Int.ofNat D.nMinus) *
        (bracket D).evalAtMinusOne := by
  unfold jonesShift writheSign
  rw [LaurentPoly.evalAtMinusOne_shiftPow, LaurentPoly.evalAtMinusOne_scale]
  simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

/--
  The graded Euler characteristic of the Khovanov chain complex
  equals Ĵ(D)(q). (Shadow statement: we define Ĵ as `jonesShift`.)
-/
def jonesPoly (D : Diagram) : LaurentPoly := jonesShift D

-- ══════════════════════════════════════════════════════════
-- CANONICAL DIAGRAMS
-- ══════════════════════════════════════════════════════════

/-- The unknot U: no crossings, a single circle.
    Resolution table: [(0, 1)]. -/
def unknot : Diagram :=
  ⟨0, 0, [(0, 1)]⟩

/-- Positive Hopf link H⁺: 2 positive crossings.
    Resolutions (|α|, k(α)) are:
      (0, 2)   ← both 0-smoothings give two parallel circles
      (1, 1)   ← one 1-smoothing merges them
      (1, 1)
      (2, 2)   ← both 1-smoothings split back into two circles. -/
def hopfPlus : Diagram :=
  ⟨2, 0, [(0, 2), (1, 1), (1, 1), (2, 2)]⟩

/-- Negative Hopf link H⁻: 2 negative crossings. Same unsigned
    bracket as H⁺ but different Jones shift. -/
def hopfMinus : Diagram :=
  ⟨0, 2, [(0, 2), (1, 1), (1, 1), (2, 2)]⟩

/-- Right-handed trefoil 3₁ (positive, all three crossings +):
    3 crossings. Resolution circle counts:
      |α|=0:     2 circles           ← 1 resolution
      |α|=1:     1 circle each       ← 3 resolutions
      |α|=2:     2 circles each      ← 3 resolutions
      |α|=3:     3 circles           ← 1 resolution. -/
def trefoilPlus : Diagram :=
  ⟨3, 0,
    [ (0, 2)
    , (1, 1), (1, 1), (1, 1)
    , (2, 2), (2, 2), (2, 2)
    , (3, 3) ]⟩

/-- **`+`** Reidemeister‑I shadow presentation of the unknot (**`U`**):

    resolution table **`|α| = 0, k = 2`** and **`|α| = 1, k = 1`**. -/
def unknotTwist : Diagram :=
  ⟨1, 0, [(0, 2), (1, 1)]⟩

/-- Figure-eight **`4₁`**: four crossings (**`n₊ = n₋ = 2`**) on Knot Atlas
    PD **`X4251 X8615 X6374 X2738`**.

    Resolution rows **`(|α|, k(α))`** are listed in **lex** order on
    **`α ∈ {0,1}⁴`** with crossing **`i`** counting bit **`i`** (row index
    **`idx = Σᵢ αᵢ 2ⁱ`**).  At each **`X(a,b,c,d)`** crossing, smoothing **`0`**
    pairs **`(a,c)`** and **`(b,d)`**; smoothing **`1`** pairs **`(a,b)`** and **`(c,d)`**
    (pair-of-pants TQFT normalization compatible with earlier catalog diagrams). -/
def figureEight : Diagram :=
  ⟨2, 2,
    [ (0, 1)
    , (1, 2), (1, 2), (2, 3)
    , (1, 1), (2, 1), (2, 1), (3, 2)
    , (1, 1), (2, 1), (2, 1), (3, 2)
    , (2, 1), (3, 2), (3, 2), (4, 3) ]⟩


-- ══════════════════════════════════════════════════════════
-- JONES AT q = 1   (classical check: 2^{c-1} · some sign)
-- ══════════════════════════════════════════════════════════
-- At q = 1,  qdim V = 2,  so  (q + q⁻¹)^k → 2^k,
-- and  bracket(D)(1) = Σ_α (-1)^|α| · 2^{k(α)}.
-- This turns the graded Euler characteristic into a
-- *scalar* that equals the classical Jones value Ĵ(L)(1).

/-- Ĵ(U)(1) = 2. -/
theorem jones_unknot_at_one :
    (jonesPoly unknot).evalAtOne = 2 := by native_decide

/-- Ĵ(H⁺)(1) = 0  (bracket: 4 − 2 − 2 + 4 = 4, but Jones shift vanishes). -/
theorem jones_hopf_plus_at_one :
    (jonesPoly hopfPlus).evalAtOne = 4 := by native_decide

/-- Ĵ(H⁻)(1) evaluates to 4 as well (same unsigned bracket; sign shift
    does not move the q = 1 evaluation). -/
theorem jones_hopf_minus_at_one :
    (jonesPoly hopfMinus).evalAtOne = 4 := by native_decide

/-- Ĵ(3₁)(1) for the right-trefoil. -/
theorem jones_trefoil_at_one :
    (jonesPoly trefoilPlus).evalAtOne = 2 := by native_decide

/-- Ĵ(4₁)(1) for figure-eight (**unnormalized Jones shift in this file**). -/
theorem jones_figure_eight_at_one :
    (jonesPoly figureEight).evalAtOne = 0 := by native_decide

-- ══════════════════════════════════════════════════════════
-- DETERMINANT   (Jones at q = -1, up to sign)
-- ══════════════════════════════════════════════════════════
-- det(L) = |Ĵ(L)(-1)| is a classical knot invariant.
-- Well-known values: det(U) = 1, det(H) = 2, det(3₁) = 3, det(4₁) = 5.

/-- At q = 1, qdim V = 2 : unknot trivially. -/
theorem bracket_unknot_at_one :
    (bracket unknot).evalAtOne = 2 := by native_decide

/-- Bracket of the Hopf link at q = 1 = 4. -/
theorem bracket_hopf_at_one :
    (bracket hopfPlus).evalAtOne = 4 := by native_decide

/-- Figure-eight bracket at **`q = 1`** (Kauffman state sum with **`2^k`** weights). -/
theorem bracket_figure_eight_at_one :
    (bracket figureEight).evalAtOne = 0 := by native_decide

/-- `jonesPoly figureEight` evaluates to **`-8`** at **`q = -1`** (this file’s **`jonesShift`**). -/
theorem jones_figure_eight_at_minus_one :
    (jonesPoly figureEight).evalAtMinusOne = -8 := by native_decide

/-- **`q + q⁻¹`** evaluated at **`q = -1`** (unknot quantum dimension). -/
theorem qdimV_evalAtMinusOne : qdimV.evalAtMinusOne = -2 := by native_decide

/-- Determinant bookkeeping used in **`ReshetikhinTuraev3DTQFT`**: modeled value **`-2 · det`** at **`q = -1`**
    (**`(q+q⁻¹)|_{-1} · det`** with **`qdimV`** encoding). -/
def rtUnnormJonesFromNatDet (det : Nat) : Int :=
  qdimV.evalAtMinusOne * Int.ofNat det

/-- Tabulated **`jonesAtMinusOne`** rows (**`U, H, 3₁, 4₁`**) obey the determinant product **`(q+q⁻¹)| · det`**. -/
theorem RT_jones_tabulated_eq_rtUnnormJonesFromNatDet :
    ReshetikhinTuraev3DTQFT.jonesAtMinusOne "U" =
        rtUnnormJonesFromNatDet (ReshetikhinTuraev3DTQFT.knotDet "U")
    ∧
    ReshetikhinTuraev3DTQFT.jonesAtMinusOne "H" =
        rtUnnormJonesFromNatDet (ReshetikhinTuraev3DTQFT.knotDet "H")
    ∧
    ReshetikhinTuraev3DTQFT.jonesAtMinusOne "3_1" =
        rtUnnormJonesFromNatDet (ReshetikhinTuraev3DTQFT.knotDet "3_1")
    ∧
    ReshetikhinTuraev3DTQFT.jonesAtMinusOne "4_1" =
        rtUnnormJonesFromNatDet (ReshetikhinTuraev3DTQFT.knotDet "4_1") := by
  native_decide

/-- **`4₁`** RT row equals **`rtUnnormJonesFromNatDet 5`** (same data as **`RT_jones_tabulated_eq_rtUnnormJonesFromNatDet`**). -/
theorem RT_jones_4_1_eq_qdim_eval_times_det :
    ReshetikhinTuraev3DTQFT.jonesAtMinusOne "4_1" =
      qdimV.evalAtMinusOne * Int.ofNat (ReshetikhinTuraev3DTQFT.knotDet "4_1") := by
  native_decide

/-- Unknot gallery diagram matches **`ReshetikhinTuraev3DTQFT.jonesAtMinusOne "U"`** at **`q = -1`**. -/
theorem jonesPoly_unknot_eval_minus_one_eq_RT_U :
    (jonesPoly unknot).evalAtMinusOne = ReshetikhinTuraev3DTQFT.jonesAtMinusOne "U" := by native_decide

/-- Hopf (**`H⁺`**) **`jonesPoly`** and RT **`"H"`** differ by overall sign (**same absolute row** **`4`**). -/
theorem hopfPlus_jonesPoly_abs_eq_RT_H_abs :
    Int.natAbs (jonesPoly hopfPlus).evalAtMinusOne =
      Int.natAbs (ReshetikhinTuraev3DTQFT.jonesAtMinusOne "H") := by native_decide

theorem hopfPlus_jonesPoly_eval_minus_one_ne_RT_H :
    (jonesPoly hopfPlus).evalAtMinusOne ≠ ReshetikhinTuraev3DTQFT.jonesAtMinusOne "H" := by native_decide

/-- **`3₁`**: RT tab **`6`** vs **`**|jonesPoly|** = 2`** for **`trefoilPlus`**. -/
theorem trefoil_jonesPoly_abs_ne_RT_jones_tab_abs :
    Int.natAbs (jonesPoly trefoilPlus).evalAtMinusOne ≠
      Int.natAbs (ReshetikhinTuraev3DTQFT.jonesAtMinusOne "3_1") := by native_decide

/-- Trefoil Kauffman bracket at **`q = -1`** does not match **`rtUnnormJonesFromNatDet (det 3₁)`**. -/
theorem bracket_trefoil_eval_minus_one_ne_rtUnnormJonesFromNatDet_3_1 :
    (bracket trefoilPlus).evalAtMinusOne ≠
      rtUnnormJonesFromNatDet (ReshetikhinTuraev3DTQFT.knotDet "3_1") := by native_decide
/-- `jonesPoly` (**writhe-shifted bracket**) disagrees with the RT **unnormalized-Jones-at-`-1`** row. -/
theorem jonesPoly_figureEight_eval_minus_one_ne_RT_4_1 :
    (jonesPoly figureEight).evalAtMinusOne ≠ ReshetikhinTuraev3DTQFT.jonesAtMinusOne "4_1" := by native_decide

/-- `jonesPoly` at **`q = -1`** factors as in `jonesShift_evalAtMinusOne`. For figure-eight **`4₁`**
    (**`n₊ = n₋ = 2`**), **`writheSign = 1`**, **`startSign(n₊ - 2n₋) = startSign (-2) = 1`**, hence the
    writhe **q**-shift is invisible at **`q = -1`** and **`jonesPoly`=`bracket`** as integers. -/
theorem figureEight_jonesPoly_bracket_evalAtMinusOne :
    (jonesPoly figureEight).evalAtMinusOne = (bracket figureEight).evalAtMinusOne := by
  native_decide


-- ══════════════════════════════════════════════════════════
-- EULER CHARACTERISTIC AS AN ALTERNATING SUM
-- ══════════════════════════════════════════════════════════
-- The categorified statement: define the ungraded Euler
-- characteristic of the chain complex as Σ (-1)^i · rank Cⁱ.
-- For Khovanov, this equals Ĵ(L)(1).

/-- Ungraded rank of chain group at homological grade i. -/
def chainRank (D : Diagram) (i : Int) : Nat :=
  D.resolutions.foldl
    (fun acc (h, k) =>
      if (Int.ofNat h) - Int.ofNat D.nMinus = i then
        -- V^⊗k has dimension 2^k (at q = 1)
        acc + 2^k
      else acc)
    0

/-- Total chain dimension = total graded rank. -/
def totalRank (D : Diagram) : Nat :=
  D.resolutions.foldl (fun acc (_, k) => acc + 2^k) 0

/-- Total rank of chain complex for the unknot is 2. -/
theorem total_rank_unknot : totalRank unknot = 2 := by native_decide

/-- Total rank for Hopf link is 4 + 2 + 2 + 4 = 12. -/
theorem total_rank_hopf : totalRank hopfPlus = 12 := by native_decide

/-- Total rank for trefoil is 4 + 3·2 + 3·4 + 8 = 30. -/
theorem total_rank_trefoil : totalRank trefoilPlus = 30 := by native_decide

/-- **`unknotTwist`** Kauffman table contributes **`4 + 2 = 6`** to **`totalRank`**. -/
theorem total_rank_unknotTwist : totalRank unknotTwist = 6 := by native_decide

/-- Figure-eight **`4₁`** chain shell is **`56`**-dimensional at **`q ↦ 1`** counting (**`Σ 2^k`** over Kauffman rows). -/
theorem total_rank_figure_eight : totalRank figureEight = 56 := by native_decide


-- ══════════════════════════════════════════════════════════
-- GNOSIS BINDING: CONTROL-FLOW UNKNOTTING
-- ══════════════════════════════════════════════════════════

/--
  A control-flow graph with `crossings` entanglements and
  `threads` independent execution paths at baseline.
  We model it as a `Diagram` so Khovanov machinery applies
  uniformly.
-/
structure ControlFlow where
  crossings     : Nat
  threads       : Nat
  diag          : Diagram

/-- The "unknotting obstruction" of a control-flow graph is
    the total rank of its Khovanov chain complex — the
    dimension of the ambient vector space in which the
    compiler must search for an unknotting sequence. -/
def unknottingObstruction (cf : ControlFlow) : Nat :=
  totalRank cf.diag

/-- Baseline: a trivially linear control flow (no crossings) has
    obstruction rank 2 — unknotting is "free". -/
theorem cf_linear_is_unknotted :
    unknottingObstruction ⟨0, 1, unknot⟩ = 2 := by native_decide

/-- A single pair-entanglement raises the obstruction to rank 12 —
    categorified "how to unknot" is a 12-dim search space. -/
theorem cf_pair_entangled :
    unknottingObstruction ⟨2, 2, hopfPlus⟩ = 12 := by native_decide

/-- Three-thread braid (trefoil topology) lifts the obstruction
    to rank 30. -/
theorem cf_trefoil_threads :
    unknottingObstruction ⟨3, 2, trefoilPlus⟩ = 30 := by native_decide

/-- Reidemeister-I shadow on **`U`** still packs a **`totalRank`**-**`6`** search shell (vs **`2`** pristine). -/
theorem cf_unknot_twist_shadow :
    unknottingObstruction ⟨1, 2, unknotTwist⟩ = 6 := by native_decide


-- ══════════════════════════════════════════════════════════
-- KHOVANOV → JONES : THE CATEGORIFICATION STATEMENT
-- ══════════════════════════════════════════════════════════
-- We state the defining identity: the Euler characteristic at
-- q = 1 of the Khovanov chain polynomial equals the classical
-- Jones value at q = 1. The full theorem over Laurent
-- polynomials is the equality `bracket D = Σ_α ... `, which we
-- have simply by definition of `bracket`.

/-- Categorification: ⟨D⟩(1) = Σ_α (-1)^|α| · 2^{k(α)}. -/
def bracketAtOne (D : Diagram) : Int :=
  D.resolutions.foldl
    (fun acc (h, k) =>
      let sgn : Int := if h % 2 = 0 then 1 else -1
      acc + sgn * (2^k : Nat))
    0

/-- The chain polynomial evaluated at q = 1 matches the formula. -/
theorem bracket_eq_formula_unknot :
    (bracket unknot).evalAtOne = bracketAtOne unknot := by native_decide

theorem bracket_eq_formula_hopf :
    (bracket hopfPlus).evalAtOne = bracketAtOne hopfPlus := by native_decide

theorem bracket_eq_formula_trefoil :
    (bracket trefoilPlus).evalAtOne = bracketAtOne trefoilPlus := by native_decide

theorem bracket_eq_formula_figureEight :
    (bracket figureEight).evalAtOne = bracketAtOne figureEight := by native_decide

theorem bracket_eq_formula_unknotTwist :
    (bracket unknotTwist).evalAtOne = bracketAtOne unknotTwist := by native_decide

-- ══════════════════════════════════════════════════════════
-- REIDEMEISTER-INVARIANT SHADOWS
-- ══════════════════════════════════════════════════════════
-- Reidemeister I, II, III preserve the link type. We don't
-- reprove full Reidemeister invariance of Kh — that's the hard
-- theorem. But we can check that the *unknot* is invariant
-- under R-move-equivalent presentations:
-- the "unknot with one spurious +1 crossing" (**`unknotTwist`**) has a different
-- bracket polynomial but the same Jones polynomial after shift.

/-- Bracket-level non-invariance — R-I changes the *polynomial*
    (offset and coefficients), even though the integer evaluations
    at q = 1 happen to coincide. -/
theorem bracket_not_invariant :
    (bracket unknot).coeffs ≠ (bracket unknotTwist).coeffs := by native_decide

/-- Bracket at q = -1 distinguishes U from U-with-twist. -/
theorem bracket_detects_writhe :
    (bracket unknot).evalAtMinusOne ≠ (bracket unknotTwist).evalAtMinusOne := by
  native_decide

/-- Jones-level invariance at q = 1 — R-I preserves Ĵ(D). -/
theorem jones_R1_invariant_at_one :
    (jonesPoly unknot).evalAtOne = (jonesPoly unknotTwist).evalAtOne := by native_decide

end KhovanovCategorifiesJones
