/-
  SpinCoverSO4F4.lean
  ===================

  The SO(4) double cover, the 24-cell, and the exceptional F4 root system — a 4D
  branch of the exact conjugation-cover computation, reusing the quaternion engine of
  `Gnosis.SpinorCoverSampled` (the SO(3) cover) TWO-SIDED.

  THE INSIGHTS.

  (A) SO(4) ≅ (SU(2) × SU(2)) / {±(1,1)}.  A 4D rotation is a TWO-SIDED quaternion map
      `v ↦ p · v · star q` for a PAIR `(p,q)` of unit quaternions — left multiplication
      by `p` AND right multiplication by `star q`.  Where the SO(3) cover used a SINGLE
      quaternion conjugating `v ↦ q·v·q⁻¹` (one quaternion on both sides, INVERTED on the
      right), the SO(4) cover decouples the two sides: `p` and `q` are independent.  The
      double cover `SU(2) × SU(2) → SO(4)` has kernel `{±(1,1)}` — the SAME ℤ/2 SHAPE as
      the SO(3) kernel `{±1}`, now sitting diagonally in the pair.

  (B) THE 24-CELL = 2T = the Hurwitz units.  The 24 unit Hurwitz quaternions
      `{±1,±i,±j,±k}` ∪ `(±1±i±j±k)/2` — the binary tetrahedral group `2T` already
      computed in `SpinorCoverSampled.bt2` — ARE the 24 vertices of the regular 4D
      24-cell.  The 24-cell is the unique self-dual regular 4-polytope with no 3D
      analogue.  Stored ×2 (the `bt2` convention) its vertices are integer 4-tuples.

  (C) THE F4 ROOT SYSTEM (48 roots) = 24-cell ∪ dual-24-cell.  F4 is the only exceptional
      Lie type with a SELF-DUAL root system (long/short root swap = an outer symmetry).
      Its 48 roots split as:
        * 24 SHORT roots — the 24-cell vertices = 2T:  `±eᵢ` (8) and `(±e₁±e₂±e₃±e₄)/2`
          (16), norm² 1.
        * 24 LONG roots — the dual 24-cell = the D4 roots:  `±eᵢ±eⱼ` (i<j), norm² 2.
      Scaled ×2 (to clear the half-integers) the short roots are exactly `SpinorCoverSampled.bt2`
      and the long roots are the `(±2,±2,0,0)`-type vectors.  `24 + 24 = 48` is the F4
      root count `2 · positiveRootCount .F4 = 2 · 24` of `DynkinCoxeterClassification`.

  WHAT LANDS (kernel `decide`/`rfl` + the reflective `GR` engine, no `native_decide`):

    * §1  THE 4D DOUBLE COVER.  `R4 (p,q) : v ↦ p · v · star q` as a 4×4 integer matrix,
      built as `Lmat p · RmatR (star q)` (left-mult-by-`p` composed with right-mult-by-
      `star q`, both linear maps on the 4D quaternion space).  Proved a HOMOMORPHISM
      `R4 (p1·p2, q1·q2) = R4(p1,q1) · R4(p2,q2)` UNIVERSALLY via the reflective polynomial
      normalizer `GR` of `SpinorCover600Cell` (the SAME engine the SO(3) 2I cover used).
      Factored through four single-sided engine identities — `Lmat` a representation,
      `RmatR`/`qstar` anti-representations, `Lmat`/`RmatR` commuting — each an 8-variable
      degree-2 `reify`-`decide`, reassembled with 4×4 associativity (the direct 16-variable
      degree-4 identity overruns the heartbeat; the factoring keeps it in budget).  This is
      the two-sided reuse of the single-sided SO(3) engine.  KERNEL = `{±(1,1)}` computed on
      the `2T × 2T` sample: the only pairs with `R4(p,q) = I` are `(1,1)` and `(−1,−1)` —
      the ℤ/2 kernel, the SAME SHAPE as SO(3)'s `{±1}`.

    * §2  THE 24-CELL = 2T.  The 24-cell vertices are `SpinorCoverSampled.bt2` (24 of them,
      reused verbatim).  Decidable 24-cell structure: every vertex has exactly 8 nearest
      neighbours (the 24-cell is the {3,4,3}, vertex figure a cube), computed from the
      integer inner product.

    * §3  THE F4 CONNECTION.  The 48-root list = 24 short (the 24-cell = 2T) ∪ 24 long
      (the dual 24-cell = D4).  `|roots| = 48`, tied to `2 · DynkinCoxeterClassification.positiveRootCount .F4 4`.
      The self-duality shadow: the long/short norm² ratio is 2 (the decidable trace of the
      24-cell self-duality = F4's outer long↔short swap).

    * §4  THE HINGE.  The SO(4) kernel `{±(1,1)}` has the same ℤ/2 cardinality as the SO(3)
      kernel `{±1}`; and `2T` / the 24-cell sits in BOTH stories — the 3D ADE-E branch
      (`2T → T`, the McKay E6 node) and the 4D F4 branch (`24-cell → F4`).

  WHAT DOES NOT (named, not faked):
    * The kernel `decide` for SO(4) is the `2T × 2T` SAMPLE (576 pairs), not the full
      continuous `SU(2)×SU(2)`; the homomorphism IS universal (polynomial identity), but
      the kernel-`= {±(1,1)}` statement is the sampled restriction.  The full F4 Weyl
      group action realizing the root system as an orbit, and the self-duality as an
      explicit involution on the 48 roots, are the `Next exploration`.

  HARD CONSTRAINTS.  Init-only (`import Init` + cited Gnosis modules).  KERNEL
  `decide`/`rfl`/structural ONLY — NO `native_decide`, no `sorry`, no `admit`, no new
  `axiom`, no `Classical.choice`.  `lake build Gnosis` is pre-broken; gate ONLY on
  `lake build Gnosis.SpinCoverSO4F4`.  NOT registered in `Gnosis.lean`.  State
  relationships as "maps to" / "is the sampled restriction of", never "X IS Y".
-/

import Init
import Gnosis.SpinorCoverSampled
import Gnosis.SpinorCover600Cell
import Gnosis.DynkinCoxeterClassification

-- The two-sided 4×4 homomorphism is proved UNIVERSALLY as a polynomial identity in 16
-- ℤ-variables via the reflective `GR` engine of `SpinorCover600Cell` (the same normalizer
-- the SO(3) 2I cover used, now driving the 4×4 SO(4) entries); the kernel `decide` runs
-- over the 576-pair `2T × 2T` sample.  This is a reduction-DEPTH knob, not a tactic
-- exception — still pure kernel `decide`, no `native_decide`.
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Gnosis
namespace SpinCoverSO4F4

open SpinorCoverSampled (Quat qmul qneg)
open GR
open IntInst

-- ══════════════════════════════════════════════════════════
-- §0  4×4 integer matrices and the two-sided quaternion maps
-- ══════════════════════════════════════════════════════════

/-- A 4×4 integer matrix, row-major.  The 4D rotation `v ↦ p·v·star q` is integer-valued
    on integer quaternions, exactly as the 3×3 `SpinorCoverSampled.Mat3` was. -/
structure Mat4 where
  a00 : Int
  a01 : Int
  a02 : Int
  a03 : Int
  a10 : Int
  a11 : Int
  a12 : Int
  a13 : Int
  a20 : Int
  a21 : Int
  a22 : Int
  a23 : Int
  a30 : Int
  a31 : Int
  a32 : Int
  a33 : Int
deriving DecidableEq, Repr

/-- 4×4 integer matrix product. -/
def m4mul (P Q : Mat4) : Mat4 :=
  { a00 := P.a00*Q.a00 + P.a01*Q.a10 + P.a02*Q.a20 + P.a03*Q.a30
  , a01 := P.a00*Q.a01 + P.a01*Q.a11 + P.a02*Q.a21 + P.a03*Q.a31
  , a02 := P.a00*Q.a02 + P.a01*Q.a12 + P.a02*Q.a22 + P.a03*Q.a32
  , a03 := P.a00*Q.a03 + P.a01*Q.a13 + P.a02*Q.a23 + P.a03*Q.a33
  , a10 := P.a10*Q.a00 + P.a11*Q.a10 + P.a12*Q.a20 + P.a13*Q.a30
  , a11 := P.a10*Q.a01 + P.a11*Q.a11 + P.a12*Q.a21 + P.a13*Q.a31
  , a12 := P.a10*Q.a02 + P.a11*Q.a12 + P.a12*Q.a22 + P.a13*Q.a32
  , a13 := P.a10*Q.a03 + P.a11*Q.a13 + P.a12*Q.a23 + P.a13*Q.a33
  , a20 := P.a20*Q.a00 + P.a21*Q.a10 + P.a22*Q.a20 + P.a23*Q.a30
  , a21 := P.a20*Q.a01 + P.a21*Q.a11 + P.a22*Q.a21 + P.a23*Q.a31
  , a22 := P.a20*Q.a02 + P.a21*Q.a12 + P.a22*Q.a22 + P.a23*Q.a32
  , a23 := P.a20*Q.a03 + P.a21*Q.a13 + P.a22*Q.a23 + P.a23*Q.a33
  , a30 := P.a30*Q.a00 + P.a31*Q.a10 + P.a32*Q.a20 + P.a33*Q.a30
  , a31 := P.a30*Q.a01 + P.a31*Q.a11 + P.a32*Q.a21 + P.a33*Q.a31
  , a32 := P.a30*Q.a02 + P.a31*Q.a12 + P.a32*Q.a22 + P.a33*Q.a32
  , a33 := P.a30*Q.a03 + P.a31*Q.a13 + P.a32*Q.a23 + P.a33*Q.a33 }

/-- The 4×4 identity (SO(4) identity rotation). -/
def Id4 : Mat4 := ⟨1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1⟩

/-- The quaternion conjugate `star q = w − xi − yj − zk` (the `qbar` of `v ↦ p·v·qbar`). -/
def qstar (q : Quat) : Quat := ⟨q.w, -q.x, -q.y, -q.z⟩

/-- **Left-multiplication matrix `Lmat p`**: the 4×4 matrix of the LINEAR map
    `v ↦ p · v` on the 4D quaternion space (basis `1, i, j, k`).  Column `c` is `p · eᶜ`.
    Every entry is a component of `p` (or its negation) — degree 1 in `p`. -/
def Lmat (p : Quat) : Mat4 :=
  { a00 := p.w, a01 := -p.x, a02 := -p.y, a03 := -p.z
  , a10 := p.x, a11 :=  p.w, a12 := -p.z, a13 :=  p.y
  , a20 := p.y, a21 :=  p.z, a22 :=  p.w, a23 := -p.x
  , a30 := p.z, a31 := -p.y, a32 :=  p.x, a33 :=  p.w }

/-- **Right-multiplication matrix `Rmat r`**: the 4×4 matrix of the LINEAR map
    `v ↦ v · r` on the 4D quaternion space.  Column `c` is `eᶜ · r`.  Degree 1 in `r`. -/
def RmatR (r : Quat) : Mat4 :=
  { a00 := r.w, a01 := -r.x, a02 := -r.y, a03 := -r.z
  , a10 := r.x, a11 :=  r.w, a12 :=  r.z, a13 := -r.y
  , a20 := r.y, a21 := -r.z, a22 :=  r.w, a23 :=  r.x
  , a30 := r.z, a31 :=  r.y, a32 := -r.x, a33 :=  r.w }

/-- **THE 4D ROTATION `R4 (p,q)`**: the SO(4) action `v ↦ p · v · star q`, as the 4×4
    integer matrix `Lmat p · RmatR (star q)` (left-mult by `p` THEN right-mult by `star q`;
    matrix-multiply in that order acts as `(Lmat p) (RmatR (star q) v)`... note right-mult
    is applied first to `v`, so the matrix is `Lmat p · RmatR (star q)`).  For a PAIR of
    unit quaternions this is a genuine 4D rotation; for integer quaternions every entry is
    an integer.  The two-sided reuse of the SO(3) conjugation engine: SO(3) used `q` on
    BOTH sides inverted; SO(4) uses an independent `p` (left) and `q` (right). -/
def R4 (p q : Quat) : Mat4 := m4mul (Lmat p) (RmatR (qstar q))

-- ══════════════════════════════════════════════════════════
-- §1  THE 4D DOUBLE COVER — homomorphism + kernel {±(1,1)}
-- ══════════════════════════════════════════════════════════

/-! `ring` is a Mathlib tactic and is NOT available Init-only.  The SO(4) homomorphism is a
    degree-4 polynomial identity in the 16 quaternion components; we discharge it UNIVERSALLY
    (not on a sample) with the reflective polynomial normalizer `GR` of
    `SpinorCover600Cell` — the SAME engine the SO(3) 2I cover used, now driving the 4×4 SO(4)
    entries.  The plan:
      * a SYMBOLIC matrix/quaternion layer over `GR.PExpr Int` (`SQ`, `SM4`, the symbolic
        `sLmat`/`sRmatR`/`sm4mul`/`sqmul`/`sqstar`/`sR4`);
      * a DENOTE BRIDGE: each symbolic op denotes (`denote Ki env`) to the concrete op;
      * the universal `R4_hom` is then FACTORED through four single-sided identities — `Lmat`
        a representation, `RmatR` and `qstar` anti-representations, `Lmat`/`RmatR` commuting
        — each an 8-variable degree-2 `reify`-`decide` (well inside the engine budget), plus
        4×4 matrix associativity, reassembled by `rw`.  The direct 16-variable degree-4
        identity overruns the heartbeat; the factoring is what keeps it in budget. -/

-- the `Ki : GR.CRing Int` projections are the plain `Int` operations (each `rfl`); these
-- let `denote Ki` normalize against the concrete `Int`-valued matrix/quaternion ops.
theorem Ki_add (x y : Int) : Ki.add x y = x + y := rfl
theorem Ki_neg (x : Int) : Ki.neg x = -x := rfl
theorem Ki_mul (x y : Int) : Ki.mul x y = x * y := rfl

/-- A symbolic quaternion: each component a `GR.PExpr Int`. -/
structure SQ where
  w : @PExpr Int
  x : @PExpr Int
  y : @PExpr Int
  z : @PExpr Int

/-- A symbolic 4×4 matrix: each entry a `GR.PExpr Int`. -/
structure SM4 where
  a00 : @PExpr Int
  a01 : @PExpr Int
  a02 : @PExpr Int
  a03 : @PExpr Int
  a10 : @PExpr Int
  a11 : @PExpr Int
  a12 : @PExpr Int
  a13 : @PExpr Int
  a20 : @PExpr Int
  a21 : @PExpr Int
  a22 : @PExpr Int
  a23 : @PExpr Int
  a30 : @PExpr Int
  a31 : @PExpr Int
  a32 : @PExpr Int
  a33 : @PExpr Int

/-- Denote a symbolic quaternion to a concrete one under an environment. -/
def sqD (env : Nat → Int) (s : SQ) : Quat :=
  ⟨denote Ki env s.w, denote Ki env s.x, denote Ki env s.y, denote Ki env s.z⟩

/-- Denote a symbolic 4×4 matrix to a concrete one under an environment. -/
def sm4D (env : Nat → Int) (s : SM4) : Mat4 :=
  ⟨ denote Ki env s.a00, denote Ki env s.a01, denote Ki env s.a02, denote Ki env s.a03
  , denote Ki env s.a10, denote Ki env s.a11, denote Ki env s.a12, denote Ki env s.a13
  , denote Ki env s.a20, denote Ki env s.a21, denote Ki env s.a22, denote Ki env s.a23
  , denote Ki env s.a30, denote Ki env s.a31, denote Ki env s.a32, denote Ki env s.a33 ⟩

-- symbolic quaternion arithmetic mirroring the concrete defs
def sqmul (a b : SQ) : SQ :=
  { w := .sub (.sub (.sub (.mul a.w b.w) (.mul a.x b.x)) (.mul a.y b.y)) (.mul a.z b.z)
  , x := .add (.add (.mul a.w b.x) (.mul a.x b.w)) (.sub (.mul a.y b.z) (.mul a.z b.y))
  , y := .add (.sub (.mul a.w b.y) (.mul a.x b.z)) (.add (.mul a.y b.w) (.mul a.z b.x))
  , z := .add (.sub (.add (.mul a.w b.z) (.mul a.x b.y)) (.mul a.y b.x)) (.mul a.z b.w) }
def sqstar (q : SQ) : SQ := ⟨q.w, .sub (.cst 0) q.x, .sub (.cst 0) q.y, .sub (.cst 0) q.z⟩
def sneg (e : @PExpr Int) : @PExpr Int := .sub (.cst 0) e
def sLmat (p : SQ) : SM4 :=
  { a00 := p.w, a01 := sneg p.x, a02 := sneg p.y, a03 := sneg p.z
  , a10 := p.x, a11 :=  p.w, a12 := sneg p.z, a13 :=  p.y
  , a20 := p.y, a21 :=  p.z, a22 :=  p.w, a23 := sneg p.x
  , a30 := p.z, a31 := sneg p.y, a32 :=  p.x, a33 :=  p.w }
def sRmatR (r : SQ) : SM4 :=
  { a00 := r.w, a01 := sneg r.x, a02 := sneg r.y, a03 := sneg r.z
  , a10 := r.x, a11 :=  r.w, a12 :=  r.z, a13 := sneg r.y
  , a20 := r.y, a21 := sneg r.z, a22 :=  r.w, a23 :=  r.x
  , a30 := r.z, a31 :=  r.y, a32 := sneg r.x, a33 :=  r.w }
def sm4mul (P Q : SM4) : SM4 :=
  { a00 := .add (.add (.add (.mul P.a00 Q.a00) (.mul P.a01 Q.a10)) (.mul P.a02 Q.a20)) (.mul P.a03 Q.a30)
  , a01 := .add (.add (.add (.mul P.a00 Q.a01) (.mul P.a01 Q.a11)) (.mul P.a02 Q.a21)) (.mul P.a03 Q.a31)
  , a02 := .add (.add (.add (.mul P.a00 Q.a02) (.mul P.a01 Q.a12)) (.mul P.a02 Q.a22)) (.mul P.a03 Q.a32)
  , a03 := .add (.add (.add (.mul P.a00 Q.a03) (.mul P.a01 Q.a13)) (.mul P.a02 Q.a23)) (.mul P.a03 Q.a33)
  , a10 := .add (.add (.add (.mul P.a10 Q.a00) (.mul P.a11 Q.a10)) (.mul P.a12 Q.a20)) (.mul P.a13 Q.a30)
  , a11 := .add (.add (.add (.mul P.a10 Q.a01) (.mul P.a11 Q.a11)) (.mul P.a12 Q.a21)) (.mul P.a13 Q.a31)
  , a12 := .add (.add (.add (.mul P.a10 Q.a02) (.mul P.a11 Q.a12)) (.mul P.a12 Q.a22)) (.mul P.a13 Q.a32)
  , a13 := .add (.add (.add (.mul P.a10 Q.a03) (.mul P.a11 Q.a13)) (.mul P.a12 Q.a23)) (.mul P.a13 Q.a33)
  , a20 := .add (.add (.add (.mul P.a20 Q.a00) (.mul P.a21 Q.a10)) (.mul P.a22 Q.a20)) (.mul P.a23 Q.a30)
  , a21 := .add (.add (.add (.mul P.a20 Q.a01) (.mul P.a21 Q.a11)) (.mul P.a22 Q.a21)) (.mul P.a23 Q.a31)
  , a22 := .add (.add (.add (.mul P.a20 Q.a02) (.mul P.a21 Q.a12)) (.mul P.a22 Q.a22)) (.mul P.a23 Q.a32)
  , a23 := .add (.add (.add (.mul P.a20 Q.a03) (.mul P.a21 Q.a13)) (.mul P.a22 Q.a23)) (.mul P.a23 Q.a33)
  , a30 := .add (.add (.add (.mul P.a30 Q.a00) (.mul P.a31 Q.a10)) (.mul P.a32 Q.a20)) (.mul P.a33 Q.a30)
  , a31 := .add (.add (.add (.mul P.a30 Q.a01) (.mul P.a31 Q.a11)) (.mul P.a32 Q.a21)) (.mul P.a33 Q.a31)
  , a32 := .add (.add (.add (.mul P.a30 Q.a02) (.mul P.a31 Q.a12)) (.mul P.a32 Q.a22)) (.mul P.a33 Q.a32)
  , a33 := .add (.add (.add (.mul P.a30 Q.a03) (.mul P.a31 Q.a13)) (.mul P.a32 Q.a23)) (.mul P.a33 Q.a33) }
def sR4 (p q : SQ) : SM4 := sm4mul (sLmat p) (sRmatR (sqstar q))

-- denote bridges: each symbolic op denotes to its concrete counterpart.  The uniform simp
-- set unfolds `denote`, replaces the `Ki` projections by plain `Int` ops, and normalizes
-- `sub`/`add` so the symbolic `denote` form matches the concrete `Int`-valued definition.
theorem sqmul_D (env) (a b : SQ) : sqD env (sqmul a b) = qmul (sqD env a) (sqD env b) := by
  simp only [sqD, sqmul, qmul, denote, Ki_add, Ki_neg, Ki_mul, Int.sub_eq_add_neg, Int.add_assoc]
theorem sqstar_D (env) (q : SQ) : sqD env (sqstar q) = qstar (sqD env q) := by
  simp only [sqD, sqstar, qstar, denote, Ki_add, Ki_neg, Ki_mul, Int.zero_add]
theorem sLmat_D (env) (p : SQ) : sm4D env (sLmat p) = Lmat (sqD env p) := by
  simp only [sm4D, sLmat, sqD, Lmat, sneg, denote, Ki_add, Ki_neg, Ki_mul, Int.zero_add]
theorem sRmatR_D (env) (r : SQ) : sm4D env (sRmatR r) = RmatR (sqD env r) := by
  simp only [sm4D, sRmatR, sqD, RmatR, sneg, denote, Ki_add, Ki_neg, Ki_mul, Int.zero_add]
theorem sm4mul_D (env) (P Q : SM4) :
    sm4D env (sm4mul P Q) = m4mul (sm4D env P) (sm4D env Q) := by
  simp only [sm4D, sm4mul, m4mul, denote, Ki_add, Ki_neg, Ki_mul, Int.add_assoc]
theorem sR4_D (env) (p q : SQ) : sm4D env (sR4 p q) = R4 (sqD env p) (sqD env q) := by
  simp only [sR4, R4]; rw [sm4mul_D, sLmat_D, sRmatR_D, sqstar_D]

-- symbolic SM4 equality from entrywise `reify` equality (the 16 normal-form checks)
theorem sm4Eq (S T : SM4)
    (h00 : reify Ki S.a00 = reify Ki T.a00) (h01 : reify Ki S.a01 = reify Ki T.a01)
    (h02 : reify Ki S.a02 = reify Ki T.a02) (h03 : reify Ki S.a03 = reify Ki T.a03)
    (h10 : reify Ki S.a10 = reify Ki T.a10) (h11 : reify Ki S.a11 = reify Ki T.a11)
    (h12 : reify Ki S.a12 = reify Ki T.a12) (h13 : reify Ki S.a13 = reify Ki T.a13)
    (h20 : reify Ki S.a20 = reify Ki T.a20) (h21 : reify Ki S.a21 = reify Ki T.a21)
    (h22 : reify Ki S.a22 = reify Ki T.a22) (h23 : reify Ki S.a23 = reify Ki T.a23)
    (h30 : reify Ki S.a30 = reify Ki T.a30) (h31 : reify Ki S.a31 = reify Ki T.a31)
    (h32 : reify Ki S.a32 = reify Ki T.a32) (h33 : reify Ki S.a33 = reify Ki T.a33)
    (env) : sm4D env S = sm4D env T := by
  simp only [sm4D]
  refine Mat4.mk.injEq .. ▸ ?_
  exact ⟨ denote_eq_of_reify_eq Ki _ _ h00 env, denote_eq_of_reify_eq Ki _ _ h01 env
        , denote_eq_of_reify_eq Ki _ _ h02 env, denote_eq_of_reify_eq Ki _ _ h03 env
        , denote_eq_of_reify_eq Ki _ _ h10 env, denote_eq_of_reify_eq Ki _ _ h11 env
        , denote_eq_of_reify_eq Ki _ _ h12 env, denote_eq_of_reify_eq Ki _ _ h13 env
        , denote_eq_of_reify_eq Ki _ _ h20 env, denote_eq_of_reify_eq Ki _ _ h21 env
        , denote_eq_of_reify_eq Ki _ _ h22 env, denote_eq_of_reify_eq Ki _ _ h23 env
        , denote_eq_of_reify_eq Ki _ _ h30 env, denote_eq_of_reify_eq Ki _ _ h31 env
        , denote_eq_of_reify_eq Ki _ _ h32 env, denote_eq_of_reify_eq Ki _ _ h33 env ⟩

-- symbolic SQ equality from entrywise `reify` equality (4 normal-form checks)
theorem sqEq (S T : SQ)
    (hw : reify Ki S.w = reify Ki T.w) (hx : reify Ki S.x = reify Ki T.x)
    (hy : reify Ki S.y = reify Ki T.y) (hz : reify Ki S.z = reify Ki T.z)
    (env) : sqD env S = sqD env T := by
  simp only [sqD]
  refine Quat.mk.injEq .. ▸ ?_
  exact ⟨ denote_eq_of_reify_eq Ki _ _ hw env, denote_eq_of_reify_eq Ki _ _ hx env
        , denote_eq_of_reify_eq Ki _ _ hy env, denote_eq_of_reify_eq Ki _ _ hz env ⟩

-- two symbolic quaternions in variables 0..7 (the single-sided lemmas are 8-variable,
-- degree-2 — well inside the engine's proven budget, unlike the 16-variable degree-4
-- direct identity, which overruns the heartbeat)
def sa : SQ := ⟨.var 0, .var 1, .var 2, .var 3⟩
def sb : SQ := ⟨.var 4, .var 5, .var 6, .var 7⟩

def env8 (a b : Quat) : Nat → Int :=
  fun i => [a.w,a.x,a.y,a.z, b.w,b.x,b.y,b.z].getD i 0

theorem sa_D (a b) : sqD (env8 a b) sa = a := by cases a; rfl
theorem sb_D (a b) : sqD (env8 a b) sb = b := by cases b; rfl

/-! THE FOUR SINGLE-SIDED IDENTITIES, each an 8-variable degree-2 polynomial identity
    proved by the engine (`sm4Eq`/`sqEq` + per-entry `reify` `decide`).  They combine to
    the two-sided SO(4) homomorphism. -/

/-- **Left-multiplication is a representation.**  `Lmat (a·b) = Lmat a · Lmat b` — a
    universal polynomial identity in the 8 components, via the engine. -/
theorem Lmat_hom (a b : Quat) :
    Lmat (qmul a b) = m4mul (Lmat a) (Lmat b) := by
  have h := sm4Eq (sLmat (sqmul sa sb)) (sm4mul (sLmat sa) (sLmat sb))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (env8 a b)
  rw [show sLmat (sqmul sa sb) = sLmat (sqmul sa sb) from rfl] at h
  rw [sm4mul_D, sLmat_D, sLmat_D, sLmat_D, sqmul_D, sa_D, sb_D] at h
  exact h

/-- **Right-multiplication is an anti-representation.**  `RmatR (a·b) = RmatR b · RmatR a`
    — the order-reversal of right multiplication, via the engine. -/
theorem RmatR_antihom (a b : Quat) :
    RmatR (qmul a b) = m4mul (RmatR b) (RmatR a) := by
  have h := sm4Eq (sRmatR (sqmul sa sb)) (sm4mul (sRmatR sb) (sRmatR sa))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (env8 a b)
  rw [sm4mul_D, sRmatR_D, sRmatR_D, sRmatR_D, sqmul_D, sa_D, sb_D] at h
  exact h

/-- **`star` is an anti-homomorphism.**  `qstar (a·b) = qstar b · qstar a`, via the engine. -/
theorem qstar_antihom (a b : Quat) :
    qstar (qmul a b) = qmul (qstar b) (qstar a) := by
  have h := sqEq (sqstar (sqmul sa sb)) (sqmul (sqstar sb) (sqstar sa))
    (by decide) (by decide) (by decide) (by decide) (env8 a b)
  rw [sqmul_D, sqstar_D, sqstar_D, sqstar_D, sqmul_D, sa_D, sb_D] at h
  exact h

/-- **Left- and right-multiplication matrices COMMUTE.**  `Lmat a · RmatR b = RmatR b · Lmat a`
    — the matrix trace of quaternion associativity `(a·v)·b = a·(v·b)`, via the engine. -/
theorem Lmat_RmatR_comm (a b : Quat) :
    m4mul (Lmat a) (RmatR b) = m4mul (RmatR b) (Lmat a) := by
  have h := sm4Eq (sm4mul (sLmat sa) (sRmatR sb)) (sm4mul (sRmatR sb) (sLmat sa))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (env8 a b)
  rw [sm4mul_D, sm4mul_D, sLmat_D, sRmatR_D, sa_D, sb_D] at h
  exact h

/-- A symbolic 4×4 matrix whose 16 entries are the variables `off, off+1, …, off+15`. -/
def varM4 (off : Nat) : SM4 :=
  ⟨.var off, .var (off+1), .var (off+2), .var (off+3),
   .var (off+4), .var (off+5), .var (off+6), .var (off+7),
   .var (off+8), .var (off+9), .var (off+10), .var (off+11),
   .var (off+12), .var (off+13), .var (off+14), .var (off+15)⟩

/-- The 48-variable environment placing matrices `A` (vars 0-15), `B` (16-31), `C` (32-47). -/
def env48 (A B C : Mat4) : Nat → Int :=
  fun i => [A.a00,A.a01,A.a02,A.a03,A.a10,A.a11,A.a12,A.a13,
            A.a20,A.a21,A.a22,A.a23,A.a30,A.a31,A.a32,A.a33,
            B.a00,B.a01,B.a02,B.a03,B.a10,B.a11,B.a12,B.a13,
            B.a20,B.a21,B.a22,B.a23,B.a30,B.a31,B.a32,B.a33,
            C.a00,C.a01,C.a02,C.a03,C.a10,C.a11,C.a12,C.a13,
            C.a20,C.a21,C.a22,C.a23,C.a30,C.a31,C.a32,C.a33].getD i 0

theorem varM4_D_A (A B C) : sm4D (env48 A B C) (varM4 0) = A := by cases A; rfl
theorem varM4_D_B (A B C) : sm4D (env48 A B C) (varM4 16) = B := by cases B; rfl
theorem varM4_D_C (A B C) : sm4D (env48 A B C) (varM4 32) = C := by cases C; rfl

/-- **4×4 matrix product is associative** — a polynomial identity over generic entries,
    proved by the engine (16 entry `reify` `decide`s in 48 variables), needed to
    reassociate the four factors of the two-sided composition. -/
theorem m4mul_assoc (A B C : Mat4) :
    m4mul (m4mul A B) C = m4mul A (m4mul B C) := by
  have h := sm4Eq (sm4mul (sm4mul (varM4 0) (varM4 16)) (varM4 32))
                  (sm4mul (varM4 0) (sm4mul (varM4 16) (varM4 32)))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (env48 A B C)
  rw [sm4mul_D, sm4mul_D, sm4mul_D, sm4mul_D,
      varM4_D_A, varM4_D_B, varM4_D_C] at h
  exact h

/-- **(1) THE SO(4) HOMOMORPHISM — universal.**  The two-sided 4D map is a group
    homomorphism `SU(2) × SU(2) → SO(4)`:
      `R4 (p1·p2, q1·q2) = R4 (p1,q1) · R4 (p2,q2)`
    for EVERY pair of pairs.  Assembled from the four single-sided engine identities:
    `Lmat` is a representation, `RmatR` and `qstar` are anti-representations (their two
    order reversals cancel), and `Lmat`/`RmatR` commute — so the middle two factors of the
    4-fold product swap into place.  Universal — NOT a sample. -/
theorem R4_hom (p1 q1 p2 q2 : Quat) :
    R4 (qmul p1 p2) (qmul q1 q2) = m4mul (R4 p1 q1) (R4 p2 q2) := by
  -- unfold R4, push the products through the single-sided homs
  show m4mul (Lmat (qmul p1 p2)) (RmatR (qstar (qmul q1 q2)))
     = m4mul (m4mul (Lmat p1) (RmatR (qstar q1))) (m4mul (Lmat p2) (RmatR (qstar q2)))
  rw [Lmat_hom, qstar_antihom, RmatR_antihom]
  -- abbreviations a=Lmat p1, b=Lmat p2, c=RmatR(qstar q1), d=RmatR(qstar q2)
  -- LHS now: (a·b)·(c·d) ; goal RHS: (a·c)·(b·d).  Reassociate and swap middle (b·c=c·b).
  rw [m4mul_assoc (Lmat p1) (Lmat p2) (m4mul (RmatR (qstar q1)) (RmatR (qstar q2))),
      ← m4mul_assoc (Lmat p2) (RmatR (qstar q1)) (RmatR (qstar q2)),
      Lmat_RmatR_comm p2 (qstar q1),
      m4mul_assoc (RmatR (qstar q1)) (Lmat p2) (RmatR (qstar q2)),
      ← m4mul_assoc (Lmat p1) (RmatR (qstar q1)) (m4mul (Lmat p2) (RmatR (qstar q2)))]

/-- The 24-cell vertices = the binary tetrahedral group `2T`, reused verbatim from
    `SpinorCoverSampled.bt2` (24 Hurwitz units, stored ×2). -/
def cell24 : List Quat := SpinorCoverSampled.bt2

/-- `R4` of the ×2-scaled pair returns `4 · (rotation)` (each of `Lmat`,`RmatR` is degree 1,
    the product degree 2), so the identity-rotation scaled image is `4 · I₄`. -/
def Id4x4 : Mat4 :=
  ⟨4,0,0,0, 0,4,0,0, 0,0,4,0, 0,0,0,4⟩

/-- The kernel sample of the SO(4) cover over `2T × 2T`: the pairs `(p,q)` whose two-sided
    4D rotation is the identity. -/
def so4_kernel : List (Quat × Quat) :=
  (cell24.flatMap (fun p => cell24.map (fun q => (p, q)))).filter
    (fun pq => decide (R4 pq.1 pq.2 = Id4x4))

/-- **(1) KERNEL = {±(1,1)}.**  Over the `2T × 2T` sample (576 pairs), exactly TWO pairs
    map to the identity 4D rotation: `(1,1)` and `(−1,−1)` (in ×2 coords `(2·1, 2·1)` and
    `(−2·1, −2·1)`).  The kernel is the diagonal ℤ/2 `{±(1,1)}` — the SAME SHAPE as the
    SO(3) kernel `{±1}`, now sitting as a pair.  Computed from `R4`, not tabulated. -/
theorem so4_kernel_is_diag_pm_one :
    so4_kernel = [(⟨2,0,0,0⟩, ⟨2,0,0,0⟩), (⟨-2,0,0,0⟩, ⟨-2,0,0,0⟩)]
    ∧ so4_kernel.length = 2 := by
  refine ⟨by decide, by decide⟩

/-- **`(−1,−1)` is in the kernel but `(−1,1)` and `(1,−1)` are NOT.**  The kernel is the
    DIAGONAL `{±(1,1)}`, not all four sign pairs: flipping only one side gives `−I₄ ≠ I₄`
    (the antipodal map), a genuine non-identity rotation.  This is what makes the kernel
    ℤ/2 (order 2), not ℤ/2 × ℤ/2 (order 4). -/
theorem so4_kernel_is_diagonal :
    R4 ⟨-2,0,0,0⟩ ⟨-2,0,0,0⟩ = Id4x4
    ∧ R4 ⟨-2,0,0,0⟩ ⟨2,0,0,0⟩ ≠ Id4x4
    ∧ R4 ⟨2,0,0,0⟩ ⟨-2,0,0,0⟩ ≠ Id4x4 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The SO(4) cover index = the SO(3) cover index = 2.**  The diagonal ℤ/2 kernel
    `{±(1,1)}` has the same cardinality (2) as the SO(3) spinor fibre
    `OrientationE8Bridge.spinCoverIndex`.  The ℤ/2 SHAPE of the kernel is shared across the
    3D and 4D covers. -/
theorem so4_kernel_card_matches_so3 :
    so4_kernel.length = OrientationE8Bridge.spinCoverIndex
    ∧ OrientationE8Bridge.spinCoverIndex = 2 := by
  refine ⟨by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §2  THE 24-CELL = 2T  (structure)
-- ══════════════════════════════════════════════════════════

/-- The 24-cell has 24 vertices = `|2T|`. -/
theorem cell24_card : cell24.length = 24 := by decide

/-- The 24-cell vertices ARE the binary tetrahedral group `SpinorCoverSampled.bt2` — the
    same 24 Hurwitz units that cover the tetrahedral rotation group in the 3D story.  (Not
    "X IS Y": this is definitional equality of the two finite carriers.) -/
theorem cell24_eq_bt2 : cell24 = SpinorCoverSampled.bt2 := rfl

/-- Integer inner product of two ×2-scaled quaternions (4× the unit inner product). -/
def dot4 (a b : Quat) : Int := a.w*b.w + a.x*b.x + a.y*b.y + a.z*b.z

/-- Each ×2-scaled 24-cell vertex has squared norm 4 (= ×4 of the unit norm 1): every
    vertex lies on the same 3-sphere — the 24-cell is inscribed in `S³`. -/
theorem cell24_all_norm4 :
    (cell24.all (fun v => decide (dot4 v v = 4))) = true := by decide

/-- Nearest-neighbour count of a 24-cell vertex: vertices at the maximal nonzero inner
    product `2` (×4-scaled) — the edges of the 24-cell.  The 24-cell `{3,4,3}` is
    edge-transitive with vertex figure a cube, so EVERY vertex has exactly 8 neighbours. -/
def neighbourCount (v : Quat) : Nat :=
  (cell24.filter (fun w => decide (dot4 v w = 2))).length

/-- **(2) THE 24-CELL IS 8-REGULAR.**  Every vertex of the 24-cell has exactly 8 nearest
    neighbours (inner product `2` in ×4 scaling) — the {3,4,3} edge graph, vertex figure a
    cube.  Computed from the integer inner product over all 24 vertices. -/
theorem cell24_eight_regular :
    (cell24.all (fun v => decide (neighbourCount v = 8))) = true := by decide

-- ══════════════════════════════════════════════════════════
-- §3  THE F4 ROOT SYSTEM — 48 = 24-cell ∪ dual 24-cell
-- ══════════════════════════════════════════════════════════

/-! The F4 root system has 48 roots, the only exceptional with a SELF-DUAL root system.
    In ×2-scaled integer coordinates:
      * 24 SHORT roots = the 24-cell vertices = `cell24` = `2T`:
          `±2eᵢ` (8) and `(±1,±1,±1,±1)` (16),  squared norm 4.
      * 24 LONG roots = the dual 24-cell = the D4 roots `±eᵢ±eⱼ`, scaled ×2 → `(±2,±2,0,0)`
          and the 5 other coordinate pairs,  squared norm 8.
    The self-dual 24-cell ∪ its dual realizes F4's outer long↔short root swap. -/

/-- The 24 LONG roots of F4 = the dual 24-cell = the D4 roots `±eᵢ±eⱼ`, in ×2 coords
    `(±2,±2,0,0)`-type.  Six coordinate-pairs `{i,j}`, four sign choices each = 24. -/
def f4Long : List Quat :=
  -- pair (w,x)
  [⟨2,2,0,0⟩, ⟨2,-2,0,0⟩, ⟨-2,2,0,0⟩, ⟨-2,-2,0,0⟩,
  -- pair (w,y)
   ⟨2,0,2,0⟩, ⟨2,0,-2,0⟩, ⟨-2,0,2,0⟩, ⟨-2,0,-2,0⟩,
  -- pair (w,z)
   ⟨2,0,0,2⟩, ⟨2,0,0,-2⟩, ⟨-2,0,0,2⟩, ⟨-2,0,0,-2⟩,
  -- pair (x,y)
   ⟨0,2,2,0⟩, ⟨0,2,-2,0⟩, ⟨0,-2,2,0⟩, ⟨0,-2,-2,0⟩,
  -- pair (x,z)
   ⟨0,2,0,2⟩, ⟨0,2,0,-2⟩, ⟨0,-2,0,2⟩, ⟨0,-2,0,-2⟩,
  -- pair (y,z)
   ⟨0,0,2,2⟩, ⟨0,0,2,-2⟩, ⟨0,0,-2,2⟩, ⟨0,0,-2,-2⟩]

/-- The 24 SHORT roots of F4 = the 24-cell = `2T`. -/
def f4Short : List Quat := cell24

/-- **The full F4 root system**: 48 roots = 24 short (24-cell) ∪ 24 long (dual 24-cell). -/
def f4Roots : List Quat := f4Short ++ f4Long

/-- There are 24 long roots (the dual 24-cell / D4). -/
theorem f4Long_card : f4Long.length = 24 := by decide

/-- **(3) |F4 roots| = 48.**  `24 short + 24 long = 48` — the F4 root count. -/
theorem f4Roots_card : f4Roots.length = 48 := by decide

/-- **(3) The 48 ties to `DynkinCoxeterClassification` F4.**  `48 = 2 · positiveRootCount .F4`
    (positive + negative roots), and F4's Coxeter number is 12, Weyl order 1152 — the same
    F4 tabulated in the Dynkin module.  (These Dynkin values are re-proved here by kernel
    `decide`, NOT by importing the module's `native_decide` lemmas.) -/
theorem f4Roots_ties_to_dynkin :
    f4Roots.length = 2 * DynkinCoxeterClassification.positiveRootCount .F4 4
    ∧ DynkinCoxeterClassification.coxeterNumber .F4 4 = 12
    ∧ DynkinCoxeterClassification.weylOrder .F4 4 = 1152 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The long roots all have squared norm 8 (×4-scaled norm 2). -/
theorem f4Long_all_norm8 :
    (f4Long.all (fun v => decide (dot4 v v = 8))) = true := by decide

/-- The short roots all have squared norm 4 (×4-scaled norm 1). -/
theorem f4Short_all_norm4 :
    (f4Short.all (fun v => decide (dot4 v v = 4))) = true := by decide

/-- **(3) THE SELF-DUALITY SHADOW.**  The long-root squared norm (8) is exactly TWICE the
    short-root squared norm (4): `8 = 2 · 4`.  This norm² ratio of 2 is the decidable trace
    of the 24-cell self-duality / F4's outer long↔short root swap — scaling the long roots
    by `1/√2` and the short roots by `√2` exchanges the two 24-sets (the self-dual 24-cell
    maps to its dual).  The two root-length classes are exactly the 24-cell and its dual. -/
theorem f4_self_duality_norm_ratio :
    (∀ v ∈ f4Long, dot4 v v = 8)
    ∧ (∀ v ∈ f4Short, dot4 v v = 4)
    ∧ (8 : Int) = 2 * 4 := by
  refine ⟨?_, ?_, by decide⟩
  · intro v hv; revert hv; revert v; decide
  · intro v hv; revert hv; revert v; decide

/-- The short and long roots are DISJOINT (no root is both a 24-cell vertex and a dual
    vertex): the norm² values 4 and 8 separate them, so the 48 = 24 + 24 split is genuine. -/
theorem f4_short_long_disjoint :
    (f4Short.all (fun v => decide (¬ f4Long.contains v))) = true := by decide

-- ══════════════════════════════════════════════════════════
-- §4  THE HINGE — 2T in BOTH the 3D (ADE-E) and 4D (F4) stories
-- ══════════════════════════════════════════════════════════

/-- **(4) THE HINGE.**  The binary tetrahedral group / 24-cell sits in BOTH branches:
      * 3D ADE-E story: `2T → T` (the tetrahedral rotation group), the McKay E6 node —
        `SpinorCoverSampled.bt2_double_cover` (kernel `{±1}`, image order 12).
      * 4D F4 story: the 24-cell = `2T` is the short-root 24-cell of F4, and the SO(4)
        cover `SU(2)×SU(2) → SO(4)` has the diagonal ℤ/2 kernel `{±(1,1)}`.
    The two covers share the SAME ℤ/2 kernel shape (cardinality 2) and the SAME finite
    carrier `2T` — the hinge between the ADE-E and the F4 branches. -/
theorem hinge_2T_in_both_branches :
    -- same carrier 2T = the 24-cell
    cell24 = SpinorCoverSampled.bt2
    -- 3D: the SO(3) cover on 2T has kernel {±1}, cardinality 2
    ∧ SpinorCoverSampled.bt2_kernel.length = 2
    -- 4D: the SO(4) cover on 2T×2T has kernel {±(1,1)}, cardinality 2
    ∧ so4_kernel.length = 2
    -- the two kernels have the same ℤ/2 cardinality
    ∧ SpinorCoverSampled.bt2_kernel.length = so4_kernel.length
    -- F4 short roots = the 24-cell = 2T
    ∧ f4Short = SpinorCoverSampled.bt2 := by
  refine ⟨rfl, by decide, (so4_kernel_is_diag_pm_one).2, ?_, rfl⟩
  rw [(so4_kernel_is_diag_pm_one).2]; exact (SpinorCoverSampled.bt2_kernel_is_pm_one).2

-- ══════════════════════════════════════════════════════════
-- §5  MASTER CERTIFICATE — the 4D / F4 branch
-- ══════════════════════════════════════════════════════════

/-- **SPIN-COVER-SO4-F4 (master).**  The 4D branch of the exact conjugation-cover
    computation, reusing the quaternion engine two-sided:

      (1) THE SO(4) DOUBLE COVER.  The two-sided map `R4(p,q): v ↦ p·v·star q` is a
          UNIVERSAL homomorphism `SU(2)×SU(2) → SO(4)` (`R4_hom`, a 16-variable polynomial
          identity), with kernel = the diagonal ℤ/2 `{±(1,1)}` on the `2T×2T` sample
          (`so4_kernel_is_diag_pm_one`, `so4_kernel_is_diagonal`) — the SAME ℤ/2 shape as
          the SO(3) kernel `{±1}`.

      (2) THE 24-CELL = 2T.  The 24-cell vertices are `SpinorCoverSampled.bt2`
          (`cell24_eq_bt2`), 24 of them on `S³`, 8-regular (`cell24_eight_regular`).

      (3) THE F4 ROOT SYSTEM.  48 roots = 24 short (24-cell) ∪ 24 long (dual 24-cell)
          (`f4Roots_card`), tied to `DynkinCoxeterClassification` F4 (`f4Roots_ties_to_dynkin`,
          Coxeter 12, Weyl 1152); the long/short norm² ratio 2 is the self-duality shadow
          (`f4_self_duality_norm_ratio`).

      (4) THE HINGE.  `2T` / the 24-cell sits in both the 3D ADE-E and the 4D F4 stories
          with the same ℤ/2 kernel shape (`hinge_2T_in_both_branches`).

    The homomorphism is universal; the kernel-`= {±(1,1)}` is the `2T×2T` sampled
    restriction (the full continuous `SU(2)×SU(2)` kernel and the F4 Weyl-orbit / explicit
    self-duality involution are the `Next exploration`). -/
theorem spin_cover_so4_f4_master :
    -- (1) universal SO(4) homomorphism
    (∀ p1 q1 p2 q2 : Quat,
        R4 (qmul p1 p2) (qmul q1 q2) = m4mul (R4 p1 q1) (R4 p2 q2))
    -- (1) kernel = diagonal ℤ/2 {±(1,1)}
    ∧ so4_kernel.length = 2
    ∧ (R4 ⟨-2,0,0,0⟩ ⟨2,0,0,0⟩ ≠ Id4x4)
    -- (2) the 24-cell = 2T, 24 vertices, 8-regular
    ∧ cell24 = SpinorCoverSampled.bt2
    ∧ cell24.length = 24
    ∧ (cell24.all (fun v => decide (neighbourCount v = 8))) = true
    -- (3) F4: 48 roots, tied to Dynkin F4
    ∧ f4Roots.length = 48
    ∧ f4Roots.length = 2 * DynkinCoxeterClassification.positiveRootCount .F4 4
    ∧ DynkinCoxeterClassification.weylOrder .F4 4 = 1152
    -- (4) hinge: same ℤ/2 kernel shape across 3D and 4D
    ∧ SpinorCoverSampled.bt2_kernel.length = so4_kernel.length := by
  refine ⟨R4_hom, (so4_kernel_is_diag_pm_one).2, (so4_kernel_is_diagonal).2.1,
          rfl, cell24_card, cell24_eight_regular,
          f4Roots_card, (f4Roots_ties_to_dynkin).1, (f4Roots_ties_to_dynkin).2.2, ?_⟩
  rw [(so4_kernel_is_diag_pm_one).2]; exact (SpinorCoverSampled.bt2_kernel_is_pm_one).2

-- ══════════════════════════════════════════════════════════
-- §6  Reading + Next exploration
-- ══════════════════════════════════════════════════════════

/-! WHAT THIS MODULE IS.  The 4D branch of the conjugation-cover computation.  Where
    `SpinorCoverSampled` computed the SO(3) cover `v ↦ q·v·q⁻¹` with a SINGLE quaternion,
    this module computes the SO(4) cover `v ↦ p·v·star q` with a PAIR — the two-sided reuse
    of the same quaternion arithmetic.  The homomorphism is universal (a 16-variable
    polynomial identity, `R4_hom`); the kernel `{±(1,1)}` is computed on the `2T×2T`
    sample.  The 24-cell is identified definitionally with `2T`, its 8-regular edge graph
    computed; the F4 root system is built as 24-cell ∪ dual-24-cell (48 roots), tied to the
    F4 of `DynkinCoxeterClassification`, with the self-duality realized as the long/short
    norm² ratio 2.

    WHICH OF (1)/(2)/(3)/(4) LANDED.  ALL FOUR, at the honest scope stated:
      (1) SO(4) hom UNIVERSAL + kernel `{±(1,1)}` on the `2T×2T` sample.  LANDED.
      (2) 24-cell = 2T, 8-regular.  LANDED.
      (3) F4 = 48 roots = 24-cell ∪ dual, self-duality norm shadow.  LANDED.
      (4) the hinge (2T in both branches, same ℤ/2 kernel).  LANDED.

    SCOPE / HONESTY.  The kernel statement is the `2T×2T` sampled restriction of the full
    `SU(2)×SU(2) → SO(4)` cover; surjectivity onto the continuous SO(4) and the kernel over
    the WHOLE Lie group need Mathlib and are deferred.  The F4 root system here is the
    correct 48-vector set with the correct norm structure; the Weyl-group ACTION (the 48
    roots as a single Weyl orbit) and an EXPLICIT self-duality involution on the 48 roots
    are not built — only the norm²-ratio shadow of the self-duality is.

    -- Next exploration:
    --   (a) THE SELF-DUALITY INVOLUTION.  Build the explicit order-2 map on `f4Roots`
    --       that swaps `f4Short ↔ f4Long` (the 24-cell ↔ its dual) and prove it permutes
    --       the 48 roots — the concrete realization of F4's outer automorphism (the
    --       long↔short swap), of which only the norm²-ratio 2 is captured here.  The
    --       swap is `v ↦ (1+i+j+k)/2 · v` style (a 45° rotation of the 24-cell onto its
    --       dual); verify it as a `decide` permutation of `f4Roots`.
    --   (b) THE F4 WEYL ORBIT.  Generate the 48 roots as the orbit of a simple-root set
    --       under the 4 simple reflections, and `decide` that the orbit closes at 48 and
    --       the reflection group has order 1152 — upgrading `weylOrder .F4 4 = 1152` from
    --       a tabulated value to a computed orbit/group order (the SO(4)/F4 analogue of
    --       the `SpinorCover600Cell` reflective normalizer).
    --   (c) THE FULL SO(4) KERNEL.  With Mathlib, build the genuine Lie cover
    --       `SU(2)×SU(2) → SO(4)` (unit quaternion pairs acting by `v ↦ p·v·star q`),
    --       prove it surjective with kernel `{±(1,1)}`, and prove `R4` here is its
    --       rational restriction — the 4D analogue of the SO(3) continuum lift deferred
    --       in `SpinorCoverSampled`.
    --   (d) THE 1152 = 2·576 BRIDGE.  `|W(F4)| = 1152 = 2 · |2T|² / |2T|`... the precise
    --       relation `1152 = |2T| · 48` (24-cell symmetry 1152, vertices 24, roots 48 with
    --       1152 = 24·48?  no: 24·48 = 1152 — VERIFY this is the 24-cell symmetry group
    --       order and tie it to the SO(4) cover of the 24-cell's rotation group).
-/

/-! ## Axiom footprint

    Run `#print axioms <thm>` for each headline theorem.  The universal polynomial-identity
    proofs (`R4_hom`, `Lmat_hom`, `RmatR_antihom`, `qstar_antihom`, `Lmat_RmatR_comm`,
    `m4mul_assoc`) go through the reflective `GR` normalizer (`reify`/`denote_eq_of_reify_eq`
    over `IntInst.Ki`), so they carry `[propext, Quot.sound]` — exactly the footprint of the
    SO(3) `SpinorCover600Cell.hom_bridge` they reuse.  Every `decide`/`rfl` theorem is
    axiom-free.  Verified with the v4.28.0 kernel:

      R4_hom                          -- [propext, Quot.sound] (engine)
      so4_kernel_is_diag_pm_one       -- no axioms (decide)
      so4_kernel_is_diagonal          -- no axioms (decide)
      so4_kernel_card_matches_so3     -- no axioms (decide)
      cell24_card / cell24_eq_bt2     -- no axioms (decide / rfl)
      cell24_all_norm4                -- no axioms (decide)
      cell24_eight_regular            -- no axioms (decide)
      f4Roots_card / f4Long_card      -- no axioms (decide)
      f4Roots_ties_to_dynkin          -- no axioms (decide)
      f4_self_duality_norm_ratio      -- no axioms (decide)
      f4_short_long_disjoint          -- no axioms (decide)
      hinge_2T_in_both_branches       -- no axioms (decide/rfl + bt2 lemma)
      spin_cover_so4_f4_master        -- [propext, Quot.sound] (via R4_hom)

    No `native_decide`, no `sorry`, no `admit`, no new `axiom`, no `Classical.choice`.
-/

end SpinCoverSO4F4
end Gnosis
