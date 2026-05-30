/-
  SpinorCoverSampled.lean
  =======================

  The SU(2) -> SO(3) double cover, SAMPLED on the finite subgroups of SU(2) where
  the conjugation rotation q·v·q⁻¹ is EXACT integer arithmetic — the Rustic Church
  technique applied to a Lie-group cover.

  THE INSIGHT. The finite subgroups of SU(2) (the binary polyhedral groups, and the
  Lipschitz units / quaternion group Q8 inside them) have EXACT algebraic coordinates.
  For a unit quaternion `q = (w,x,y,z)` the conjugation map on ℝ³ is the rotation

    R(q) = [[w²+x²−y²−z², 2(xy−wz),     2(xz+wy)    ],
            [2(xy+wz),     w²−x²+y²−z², 2(yz−wx)    ],
            [2(xz−wy),     2(yz+wx),     w²−x²−y²+z²]]

  (this is the conjugation already scaled by the norm |q|², so for |q|² = 1 it IS the
  rotation, and for integer coords every entry is an INTEGER). Restricted to a finite
  subgroup the whole cover — homomorphism, {±1} kernel, 2:1 fibre count — becomes a
  KERNEL `decide` over a closed finite sample. This is a genuine witness of the cover
  realized by ACTUAL conjugation, not an approximation, not an order tabulation.

  This module is the COMPUTATIONAL LIFT of the order-level shadow in
  `Gnosis.OrientationE8Bridge` and `Gnosis.OrientationSpinorBridge`: there the index 2
  and the orders 2T/2O/2I were tabulated (`subgroupOrder`, `spinCoverIndex`); here the
  index 2 is COMPUTED from `R(q) = R(−q)` and `|image| = |group|/2` by running the
  conjugation formula on every group element.

  WHAT LANDS (kernel `decide`, no `native_decide`):

    * TIER 1 — Q8 = {±1,±i,±j,±k}, integer coords in {0,±1}.
        homomorphism R(p·q) = R(p)·R(q) over all 64 pairs;
        R(q) = R(−q) (so −1 is in the kernel);
        kernel = {±1} (exactly the two units mapping to I);
        |image| = 4 = |Q8|/2 (the Klein-four rotation group V4); cover index 2,
        tied to `OrientationSpinorBridge.preimageOfOne.length` / `spinCoverIndex`.
    * TIER 2 — 2T (binary tetrahedral, 24 units = 8 Lipschitz + 16 half-integer
        (±1±i±j±k)/2). Quaternions stored ×2 as integer 4-tuples so the /2 is exact;
        conjugation stays exact in ℤ (scaled by 4). Φ : 2T -> T is a 2:1 homomorphism
        over all 576 pairs, kernel {±1}, image = tetrahedral rotation group (order 12),
        24/12 = 2. The cover EXACT on the binary tetrahedral subgroup.
    * PERIODICITY — the belt trick on a sample. With axis = i and the half-turn
        generator g = (0, i) (a 2π rotation, q(2π) = −1 ... actually q at angle π in
        spinor space): the spinor loop q(2π) = −1 maps to I (R(−1) = I) while q(4π) = +1.
        The discrete witness that the rotation has period 2π but the spinor has period 4π
        — the computational lift of `OrientationSpinorBridge.order_halves_under_quotient`.

  WHAT DOES NOT (and exactly why):

    * TIER 3 — 2O (48) needs ℤ[√2] coordinates (the extra 24 units are (±eᵢ±eⱼ)/√2);
      2I (120) needs ℤ[φ], the golden ratio. Both are still EXACT (quadratic integers,
      no reals), and the algebra `decide`s on small samples, but the FULL closure /
      homomorphism over 48²=2304 (resp. 120²=14400) pairs in quadratic-integer arithmetic
      exceeds the kernel `decide` budget (whnf heartbeat blow-up on the larger carrier).
      They are left as the documented `Next exploration` with the ℤ[√2] / ℤ[φ] setup
      sketched — NOT faked, NOT `native_decide`'d.

  CONTINUUM-PROMOTION RECORD: see `coverPromotionTrail` (§5) — the discrete theorem
  proved, the continuum refinement it is the finite restriction of, and what would
  falsify the bridge. State relationships as "is the finite restriction of" / "is the
  sampled shadow of", never "X IS Y".

  HARD CONSTRAINTS. Init-only (`import Init` + cited Gnosis modules). KERNEL
  `decide`/`rfl`/structural ONLY — NO `native_decide`, no `sorry`, no `admit`, no new
  `axiom`, no `Classical.choice`. Target propext-at-most. `lake build Gnosis` is
  pre-broken; gate ONLY on `lake build Gnosis.SpinorCoverSampled`. `#print axioms` for
  every headline theorem at the bottom of this file (commented).
-/

import Init
import Gnosis.OrientationSpinorBridge
import Gnosis.OrientationE8Bridge

-- Kernel `decide` over the 24-element 2T sample (576-pair homomorphism/closure, image
-- de-duplication) drives the definitional unfolder deep; raise the reduction limit.
-- This is a reduction DEPTH knob, not a tactic exception — still pure kernel `decide`,
-- no `native_decide`.
set_option maxRecDepth 4000

namespace Gnosis
namespace SpinorCoverSampled

-- ══════════════════════════════════════════════════════════
-- §0  Quaternions and 3×3 rotation matrices over ℤ (exact)
-- ══════════════════════════════════════════════════════════

/-- An integer quaternion `w + x·i + y·j + z·k`. For Q8 the coords are in `{0,±1}`;
    for the binary tetrahedral group we store the quaternion SCALED BY 2 so the
    half-integer `(±1±i±j±k)/2` units become integer 4-tuples in `{0,±1,±2}`. -/
structure Quat where
  w : Int
  x : Int
  y : Int
  z : Int
deriving DecidableEq, Repr

/-- The Hamilton product of two integer quaternions (exact in ℤ). -/
def qmul (a b : Quat) : Quat :=
  { w := a.w*b.w - a.x*b.x - a.y*b.y - a.z*b.z
  , x := a.w*b.x + a.x*b.w + a.y*b.z - a.z*b.y
  , y := a.w*b.y - a.x*b.z + a.y*b.w + a.z*b.x
  , z := a.w*b.z + a.x*b.y - a.y*b.x + a.z*b.w }

/-- Quaternion negation `−q`. -/
def qneg (a : Quat) : Quat := ⟨-a.w, -a.x, -a.y, -a.z⟩

/-- A 3×3 integer matrix, row-major. -/
structure Mat3 where
  a00 : Int
  a01 : Int
  a02 : Int
  a10 : Int
  a11 : Int
  a12 : Int
  a20 : Int
  a21 : Int
  a22 : Int
deriving DecidableEq, Repr

/-- 3×3 integer matrix product. -/
def mmul (P Q : Mat3) : Mat3 :=
  { a00 := P.a00*Q.a00 + P.a01*Q.a10 + P.a02*Q.a20
  , a01 := P.a00*Q.a01 + P.a01*Q.a11 + P.a02*Q.a21
  , a02 := P.a00*Q.a02 + P.a01*Q.a12 + P.a02*Q.a22
  , a10 := P.a10*Q.a00 + P.a11*Q.a10 + P.a12*Q.a20
  , a11 := P.a10*Q.a01 + P.a11*Q.a11 + P.a12*Q.a21
  , a12 := P.a10*Q.a02 + P.a11*Q.a12 + P.a12*Q.a22
  , a20 := P.a20*Q.a00 + P.a21*Q.a10 + P.a22*Q.a20
  , a21 := P.a20*Q.a01 + P.a21*Q.a11 + P.a22*Q.a21
  , a22 := P.a20*Q.a02 + P.a21*Q.a12 + P.a22*Q.a22 }

/-- Scale every entry of a matrix by an integer. -/
def mscale (k : Int) (P : Mat3) : Mat3 :=
  ⟨k*P.a00, k*P.a01, k*P.a02, k*P.a10, k*P.a11, k*P.a12, k*P.a20, k*P.a21, k*P.a22⟩

/-- Integer-divide every entry by `k` (exact only when every entry is divisible). -/
def mdiv (k : Int) (P : Mat3) : Mat3 :=
  ⟨P.a00/k, P.a01/k, P.a02/k, P.a10/k, P.a11/k, P.a12/k, P.a20/k, P.a21/k, P.a22/k⟩

/-- **The conjugation rotation `R(q)`**, the SO(3) action of `q` on ℝ³ by
    `v ↦ q·v·q⁻¹`, written in matrix form scaled by `|q|²`. For `|q|² = 1` this is the
    rotation exactly; for an integer quaternion every entry is an integer. Applied to a
    quaternion stored ×2 it returns `4·R` of the underlying unit quaternion (the formula
    is quadratic). -/
def Rmat (q : Quat) : Mat3 :=
  let w := q.w; let x := q.x; let y := q.y; let z := q.z
  { a00 := w*w + x*x - y*y - z*z
  , a01 := 2*(x*y - w*z)
  , a02 := 2*(x*z + w*y)
  , a10 := 2*(x*y + w*z)
  , a11 := w*w - x*x + y*y - z*z
  , a12 := 2*(y*z - w*x)
  , a20 := 2*(x*z - w*y)
  , a21 := 2*(y*z + w*x)
  , a22 := w*w - x*x - y*y + z*z }

/-- The 3×3 identity (SO(3) identity rotation). -/
def Id3 : Mat3 := ⟨1,0,0, 0,1,0, 0,0,1⟩

/-- Distinct-elements fold (kernel-`decide`-friendly de-duplication). -/
def nub (l : List Mat3) : List Mat3 :=
  l.foldl (fun acc m => if acc.contains m then acc else acc ++ [m]) []

-- ══════════════════════════════════════════════════════════
-- §1  TIER 1 — the quaternion group Q8 = {±1, ±i, ±j, ±k}
-- ══════════════════════════════════════════════════════════

/-- The Lipschitz unit quaternions / quaternion group `Q8 = {±1, ±i, ±j, ±k}`, integer
    coords in `{0,±1}`. The minimal perfect cover demonstrator. -/
def q8 : List Quat :=
  [⟨1,0,0,0⟩, ⟨-1,0,0,0⟩,
   ⟨0,1,0,0⟩, ⟨0,-1,0,0⟩,
   ⟨0,0,1,0⟩, ⟨0,0,-1,0⟩,
   ⟨0,0,0,1⟩, ⟨0,0,0,-1⟩]

/-- The sample has eight elements. -/
theorem q8_card : q8.length = 8 := by decide

/-- Q8 is closed under the Hamilton product — it is a genuine subgroup, the carrier the
    cover is sampled on. -/
theorem q8_closed :
    (q8.all (fun a => q8.all (fun b => q8.contains (qmul a b)))) = true := by decide

/-- **(i) HOMOMORPHISM.** The conjugation rotation is a group homomorphism on Q8:
    `R(p·q) = R(p)·R(q)` for ALL 64 ordered pairs. Exhaustive kernel `decide` —
    the cover is an actual homomorphism of the sampled conjugation action. -/
theorem q8_hom :
    (q8.all (fun a => q8.all (fun b =>
      decide (Rmat (qmul a b) = mmul (Rmat a) (Rmat b))))) = true := by decide

/-- **(ii) R(q) = R(−q).** Negating the quaternion leaves the rotation unchanged for
    every element of Q8 — so `−1` lies in the kernel and the cover is (at least) 2:1.
    `±q` cover the same rotation, computed by the conjugation formula itself. -/
theorem q8_neg_invariant :
    (q8.all (fun q => decide (Rmat q = Rmat (qneg q)))) = true := by decide

/-- The kernel sample: the Q8 elements whose conjugation rotation is the identity. -/
def q8_kernel : List Quat := q8.filter (fun q => decide (Rmat q = Id3))

/-- **(iii) KERNEL = {±1}.** Exactly the two central units `+1` and `−1` map to the
    identity rotation; the kernel sample is precisely `[1, −1]`, length 2. This is the
    `{±1}` kernel of the double cover, COMPUTED from the conjugation `R`. -/
theorem q8_kernel_is_pm_one :
    q8_kernel = [⟨1,0,0,0⟩, ⟨-1,0,0,0⟩] ∧ q8_kernel.length = 2 := by
  refine ⟨by decide, by decide⟩

/-- The image of Q8 under `R`: the distinct rotation matrices. -/
def q8_image : List Mat3 := nub (q8.map Rmat)

/-- **(iv) THE 2:1 COUNT.** The image is the Klein-four rotation group `V4`, order 4,
    and `|Q8| / |image| = 8 / 4 = 2`. The cover is exactly 2:1 — half as many rotations
    as quaternions — computed by counting distinct conjugation matrices. -/
theorem q8_image_card_is_four :
    q8_image.length = 4 ∧ q8.length / q8_image.length = 2 := by
  refine ⟨by decide, by decide⟩

/-- **The sampled cover index equals the abstract spinor fibre `{−1,+1}`.** The 2:1
    count computed here from the conjugation rotation (`|Q8| / |image| = 2`) is the SAME
    integer 2 as `OrientationE8Bridge.spinCoverIndex` (=
    `OrientationSpinorBridge.preimageOfOne.length`, the `{−1,+1}` spinor fibre) — but now
    realized by an ACTUAL conjugation computation rather than tabulated. -/
theorem q8_cover_index_ties_to_spinor_fibre :
    q8.length / q8_image.length = OrientationE8Bridge.spinCoverIndex
    ∧ OrientationE8Bridge.spinCoverIndex = OrientationSpinorBridge.preimageOfOne.length
    ∧ q8.length / q8_image.length = 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`q8_double_cover` — TIER 1 master.** The conjugation rotation `R` realizes the
    SU(2)->SO(3) double cover EXACTLY on Q8:
      (i)   homomorphism over all 64 pairs (`q8_hom`);
      (ii)  `R(q) = R(−q)`, so `−1` is in the kernel (`q8_neg_invariant`);
      (iii) kernel = `{±1}` (`q8_kernel_is_pm_one`);
      (iv)  `|image| = 4 = |Q8|/2`, cover index 2 = spinor fibre (`q8_image_card_is_four`,
            `q8_cover_index_ties_to_spinor_fibre`). -/
theorem q8_double_cover :
    (q8.all (fun a => q8.all (fun b =>
      decide (Rmat (qmul a b) = mmul (Rmat a) (Rmat b))))) = true
    ∧ (q8.all (fun q => decide (Rmat q = Rmat (qneg q)))) = true
    ∧ (q8_kernel = [⟨1,0,0,0⟩, ⟨-1,0,0,0⟩] ∧ q8_kernel.length = 2)
    ∧ (q8_image.length = 4 ∧ q8.length / q8_image.length = 2)
    ∧ q8.length / q8_image.length = OrientationE8Bridge.spinCoverIndex := by
  refine ⟨q8_hom, q8_neg_invariant, q8_kernel_is_pm_one, q8_image_card_is_four, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §2  TIER 2 — the binary tetrahedral group 2T (24 units)
-- ══════════════════════════════════════════════════════════

/-! The binary tetrahedral group `2T` has 24 unit quaternions: the 8 Lipschitz units
    `{±1,±i,±j,±k}` and the 16 half-integer units `(±1±i±j±k)/2`. The half-integers
    are not integer-valued, so we store every quaternion SCALED BY 2: `2·q` has integer
    coords in `{0,±1,±2}`. Multiplication of scaled quats: if `A = 2a` and `B = 2b`
    then the raw Hamilton product `A·B = 4·(a·b) = 2·(2ab)`, so the scaled product
    `2·(a·b)` is `(A·B)/2`, which is EXACT because every `2T` scaled product is even
    (closure, proved below). The conjugation `Rmat` applied to the SCALED quat returns
    `4·R(q)` (the formula is quadratic), so the scaled homomorphism is
    `Rmat(scaled ab) = (Rmat(A)·Rmat(B)) / 4`. -/

/-- Halve every coordinate of a quaternion (exact only when all even). -/
def qhalf (a : Quat) : Quat := ⟨a.w/2, a.x/2, a.y/2, a.z/2⟩

/-- Scaled product of quaternions stored ×2: `(2a)(2b) = 4ab`; the ×2-scaled answer
    `2ab` is the raw product halved. Exact on `2T` (closure proves divisibility). -/
def qmulScaled (a b : Quat) : Quat := qhalf (qmul a b)

/-- The 8 Lipschitz units, scaled ×2: `(±2,0,0,0)` etc. -/
def lip2 : List Quat :=
  [⟨2,0,0,0⟩, ⟨-2,0,0,0⟩,
   ⟨0,2,0,0⟩, ⟨0,-2,0,0⟩,
   ⟨0,0,2,0⟩, ⟨0,0,-2,0⟩,
   ⟨0,0,0,2⟩, ⟨0,0,0,-2⟩]

/-- The 16 half-integer units `(±1±i±j±k)/2`, scaled ×2: coords all `±1`. -/
def halfUnits2 : List Quat :=
  [⟨1,1,1,1⟩,   ⟨1,1,1,-1⟩,   ⟨1,1,-1,1⟩,   ⟨1,1,-1,-1⟩,
   ⟨1,-1,1,1⟩,  ⟨1,-1,1,-1⟩,  ⟨1,-1,-1,1⟩,  ⟨1,-1,-1,-1⟩,
   ⟨-1,1,1,1⟩,  ⟨-1,1,1,-1⟩,  ⟨-1,1,-1,1⟩,  ⟨-1,1,-1,-1⟩,
   ⟨-1,-1,1,1⟩, ⟨-1,-1,1,-1⟩, ⟨-1,-1,-1,1⟩, ⟨-1,-1,-1,-1⟩]

/-- The binary tetrahedral group `2T`, 24 units, stored ×2. -/
def bt2 : List Quat := lip2 ++ halfUnits2

/-- `2T` has 24 elements. -/
theorem bt2_card : bt2.length = 24 := by decide

/-- `2T` is closed under the scaled product — a genuine 24-element subgroup, and the
    `/2` in `qmulScaled` is exact on it (every scaled product lands back in the integer
    sample). Exhaustive over all 576 pairs. -/
theorem bt2_closed :
    (bt2.all (fun a => bt2.all (fun b => bt2.contains (qmulScaled a b)))) = true := by
  decide

/-- The scaled identity `4·I` (`= Rmat` of the ×2-scaled unit `2·1`). The image of a
    `2T` element under `Rmat` is `4·R(q)`; the scaled-identity rotation is `4·I₃`. -/
def Id3x4 : Mat3 := mscale 4 Id3

/-- **(i) HOMOMORPHISM on 2T.** `R(a·b) = R(a)·R(b)` for ALL 576 ordered pairs, in the
    scaled form `Rmat(qmulScaled a b) = (Rmat a · Rmat b)/4`. Exhaustive kernel `decide`
    — the cover is an actual homomorphism on the binary tetrahedral subgroup. -/
theorem bt2_hom :
    (bt2.all (fun a => bt2.all (fun b =>
      decide (Rmat (qmulScaled a b) = mdiv 4 (mmul (Rmat a) (Rmat b)))))) = true := by
  decide

/-- **(ii) R(q) = R(−q) on 2T.** Negation is invisible to the conjugation rotation for
    every `2T` element, so `−1` is in the kernel and the cover is 2:1. -/
theorem bt2_neg_invariant :
    (bt2.all (fun q => decide (Rmat q = Rmat (qneg q)))) = true := by decide

/-- The kernel sample of `2T`: elements whose conjugation rotation is `4·I` (the scaled
    identity). -/
def bt2_kernel : List Quat := bt2.filter (fun q => decide (Rmat q = Id3x4))

/-- **(iii) KERNEL = {±1}.** Exactly the two central units `±(2,0,0,0)` (= ×2-scaled
    `±1`) map to the identity rotation; the kernel sample has length 2. The `{±1}`
    kernel of the double cover, COMPUTED on 2T. -/
theorem bt2_kernel_is_pm_one :
    bt2_kernel = [⟨2,0,0,0⟩, ⟨-2,0,0,0⟩] ∧ bt2_kernel.length = 2 := by
  refine ⟨by decide, by decide⟩

/-- The image of `2T` under `R`: the distinct (scaled) rotation matrices. -/
def bt2_image : List Mat3 := nub (bt2.map Rmat)

/-- **(iv) THE 2:1 COUNT.** The image is the tetrahedral rotation group `T = A4`, order
    12, and `|2T| / |image| = 24 / 12 = 2`. The cover is exactly 2:1 on the binary
    tetrahedral subgroup — computed by counting distinct conjugation matrices. -/
theorem bt2_image_card_is_twelve :
    bt2_image.length = 12 ∧ bt2.length / bt2_image.length = 2 := by
  refine ⟨by decide, by decide⟩

/-- **The 2T cover index ties to the order-level shadow.** The 2:1 count computed here
    from conjugation (`24/12 = 2`) is the SAME 2 as `OrientationE8Bridge.spinCoverIndex`
    and equals the tabulated `subgroupOrder .BinaryTetra / rotationOrder .Tetra` — the
    computational lift of `OrientationE8Bridge.binary_is_2to1_spin_cover` for the
    tetrahedral case. -/
theorem bt2_cover_index_ties_to_shadow :
    bt2.length / bt2_image.length = OrientationE8Bridge.spinCoverIndex
    ∧ bt2.length / bt2_image.length
        = ADEMcKayCorrespondence.subgroupOrder .BinaryTetra 0
            / OrientationE8Bridge.rotationOrder .Tetra := by
  refine ⟨by decide, by decide⟩

/-- **`bt2_double_cover` — TIER 2 master.** The conjugation rotation `R` realizes the
    SU(2)->SO(3) double cover EXACTLY on the binary tetrahedral group `2T`:
      (i)   homomorphism over all 576 pairs (`bt2_hom`);
      (ii)  `R(q) = R(−q)` (`bt2_neg_invariant`);
      (iii) kernel = `{±1}` (`bt2_kernel_is_pm_one`);
      (iv)  `|image| = 12 = |2T|/2`, the tetrahedral rotation group, cover index 2
            (`bt2_image_card_is_twelve`). -/
theorem bt2_double_cover :
    (bt2.all (fun a => bt2.all (fun b =>
      decide (Rmat (qmulScaled a b) = mdiv 4 (mmul (Rmat a) (Rmat b)))))) = true
    ∧ (bt2.all (fun q => decide (Rmat q = Rmat (qneg q)))) = true
    ∧ (bt2_kernel = [⟨2,0,0,0⟩, ⟨-2,0,0,0⟩] ∧ bt2_kernel.length = 2)
    ∧ (bt2_image.length = 12 ∧ bt2.length / bt2_image.length = 2)
    ∧ bt2.length / bt2_image.length = OrientationE8Bridge.spinCoverIndex := by
  refine ⟨bt2_hom, bt2_neg_invariant, bt2_kernel_is_pm_one,
          bt2_image_card_is_twelve, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §3  PERIODICITY — the belt trick on a quaternion sample
-- ══════════════════════════════════════════════════════════

/-! Sample the spinor rotation loop about the `i` axis at the angles where `cos`/`sin`
    are exact (multiples of `π/2` in the quaternion's half-angle `θ/2`):

      q(θ) = cos(θ/2) + sin(θ/2)·i

    At `θ = 0`     : `q = (1,0,0,0) = +1`        (start).
    At `θ = π`     : `q = (0,1,0,0) = i`         (quarter of the spinor loop).
    At `θ = 2π`    : `q = (−1,0,0,0) = −1`       (the spinor has flipped sign).
    At `θ = 3π`    : `q = (0,−1,0,0) = −i`.
    At `θ = 4π`    : `q = (1,0,0,0) = +1`        (the spinor is back).

    All five samples are Q8 elements (integer coords), so the conjugation rotation is
    exact. The DISCRETE WITNESS: `R(q(2π)) = R(−1) = I` — the ROTATION has period 2π —
    while `q(2π) = −1 ≠ +1 = q(4π)` — the SPINOR has period 4π. This is the computational
    lift of `OrientationSpinorBridge.order_halves_under_quotient`. -/

/-- The spinor at `θ = 2π`: a full physical turn flips the spinor sign to `−1`. -/
def qAt2pi : Quat := ⟨-1, 0, 0, 0⟩
/-- The spinor at `θ = 4π`: two physical turns return the spinor to `+1`. -/
def qAt4pi : Quat := ⟨1, 0, 0, 0⟩
/-- The spinor at `θ = 0` (and the quaternion identity `+1`). -/
def qAt0 : Quat := ⟨1, 0, 0, 0⟩

/-- **The spinor has period 4π, not 2π.** At `θ = 2π` the spinor is `−1`, genuinely
    different from its start `+1`; only at `θ = 4π` does it return. The two are Q8
    elements with distinct integer coords. -/
theorem spinor_period_four_pi :
    qAt2pi ≠ qAt0 ∧ qAt4pi = qAt0 := by
  refine ⟨by decide, by decide⟩

/-- **The rotation has period 2π.** The conjugation rotation of the `θ = 2π` spinor is
    the identity `I₃` — exactly equal to `R` of the start spinor `+1`. A full physical
    turn returns the rotation, even though the spinor flipped sign. `R` cannot see the
    sign: `R(−1) = R(+1) = I`. -/
theorem rotation_period_two_pi :
    Rmat qAt2pi = Id3 ∧ Rmat qAt2pi = Rmat qAt0 := by
  refine ⟨by decide, by decide⟩

/-- **`belt_trick_sample` — the period mismatch, computed.** The rotation returns at 2π
    (`R(q(2π)) = R(−1) = I = R(q(0))`) while the spinor only returns at 4π
    (`q(2π) = −1 ≠ +1 = q(4π) = q(0)`). The 2:1 cover read off one axis: the spinor must
    go around TWICE for the rotation to go around ONCE. This is the conjugation-computed
    lift of `OrientationSpinorBridge.order_halves_under_quotient` (order 4 upstairs,
    order 2 downstairs). -/
theorem belt_trick_sample :
    -- rotation period 2π: R returns after one physical turn
    (Rmat qAt2pi = Id3 ∧ Rmat qAt2pi = Rmat qAt0)
    -- spinor period 4π: the spinor does NOT return at 2π, only at 4π
    ∧ (qAt2pi ≠ qAt0 ∧ qAt4pi = qAt0)
    -- −1 (= q(2π)) is in the kernel: it conjugates to the identity
    ∧ Rmat (qneg qAt0) = Id3 := by
  refine ⟨rotation_period_two_pi, spinor_period_four_pi, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §4  TIER 3 setup — 2O over ℤ[√2] and 2I over ℤ[φ] (deferred)
-- ══════════════════════════════════════════════════════════

/-! Tier 3 is NOT proved as a full cover here; the kernel `decide` budget does not reach
    the 48²=2304 / 120²=14400 closure checks in quadratic-integer arithmetic. We provide
    the EXACT (real-free) quadratic-integer setup so the deferral is honest and the
    `Next exploration` is concrete, and we land a small `decide`-cheap sanity slice
    (the quadratic-integer ring laws compute) to prove the representation is sound. -/

/-- `ℤ[√2]`: the element `a + b·√2`, exact, no reals. The 2O extra units
    `(±eᵢ±eⱼ)/√2` scale (×2) to coordinates `±√2 = (0,±1)`. -/
structure Zsqrt2 where
  a : Int
  b : Int
deriving DecidableEq, Repr

/-- `ℤ[√2]` multiplication: `(a+b√2)(c+d√2) = (ac+2bd) + (ad+bc)√2`. -/
def zs2mul (p q : Zsqrt2) : Zsqrt2 := ⟨p.a*q.a + 2*p.b*q.b, p.a*q.b + p.b*q.a⟩

/-- `ℤ[√2]` sanity: `√2 · √2 = 2`, exact integer arithmetic, no reals. -/
theorem zsqrt2_sq : zs2mul ⟨0,1⟩ ⟨0,1⟩ = ⟨2,0⟩ := by decide

/-- `ℤ[φ]`: the element `a + b·φ` with `φ² = φ + 1` (the golden ratio), exact, no reals.
    The icosian units of 2I live in `ℤ[φ]`, the group `OrientationE8Bridge` ties to E8. -/
structure Zphi where
  a : Int
  b : Int
deriving DecidableEq, Repr

/-- `ℤ[φ]` multiplication using `φ² = φ + 1`:
    `(a+bφ)(c+dφ) = ac + (ad+bc)φ + bd·φ² = (ac+bd) + (ad+bc+bd)φ`. -/
def zphimul (p q : Zphi) : Zphi := ⟨p.a*q.a + p.b*q.b, p.a*q.b + p.b*q.a + p.b*q.b⟩

/-- `ℤ[φ]` sanity: `φ · φ = φ + 1`, i.e. `(0+1·φ)² = 1 + 1·φ`. Exact, no reals. -/
theorem zphi_sq : zphimul ⟨0,1⟩ ⟨0,1⟩ = ⟨1,1⟩ := by decide

-- ══════════════════════════════════════════════════════════
-- §5  CONTINUUM-PROMOTION RECORD (Rustic Church §3)
-- ══════════════════════════════════════════════════════════

/-- The Rustic Church §3 documentation record for this module: which discrete theorem is
    proved, which continuum refinement it is the finite restriction of, and what would
    falsify the bridge. Strings are audit narration, not numerical axioms. -/
structure CoverContinuumTrail where
  discreteTheoremAnchor : String
  continuumRefinementAnchor : String
  falsifierSketch : String

/-- **`coverPromotionTrail`.**

    (a) DISCRETE THEOREM PROVED. The conjugation rotation `R(q) = q·v·q⁻¹` (scaled by
        `|q|²`) restricted to the finite SU(2) subgroups Q8 (`q8_double_cover`) and the
        binary tetrahedral group 2T (`bt2_double_cover`) is a 2:1 group homomorphism onto
        the corresponding rotation group, with kernel `{±1}` and image of half the
        carrier's size (V4 of order 4 for Q8; the tetrahedral group T=A4 of order 12 for
        2T). Plus a one-axis belt-trick sample (`belt_trick_sample`): the rotation `R`
        returns at 2π while the spinor returns only at 4π.

    (b) CONTINUUM REFINEMENT IT IS THE FINITE RESTRICTION OF. The Lie-group double cover
        `SU(2) → SO(3)`, a surjective 2:1 group homomorphism with kernel `{±I}`, whose
        one-parameter rotation subgroup satisfies `exp(2π) = −I` in SU(2) but `= I` in
        SO(3) and `exp(4π) = I` in both. The discrete result here IS THE FINITE
        RESTRICTION OF that cover to the sampled subgroups; it does NOT establish
        surjectivity onto the full continuous SO(3). See (cited, NOT imported)
        `docs/OrientationSpinorContinuous_SKELETON.md` and the deferred Mathlib lift named
        in `OrientationSpinorBridge`'s Next exploration.

    (c) WHAT WOULD FALSIFY THE BRIDGE. Any sampled ordered pair `(p,q)` violating
        `R(p·q) = R(p)·R(q)` (homomorphism failure); OR any kernel element outside `{±1}`
        (i.e. a non-central `q` with `R(q) = I`); OR a computed cover index ≠ 2 (an image
        whose size is not exactly half the carrier). Each is a closed `decide` that, were
        it to flip, would refute the finite restriction — and is exactly what `q8_hom`,
        `q8_kernel_is_pm_one`, `bt2_hom`, `bt2_kernel_is_pm_one`, and the image-count
        theorems certify does NOT happen on the sample. -/
def coverPromotionTrail : CoverContinuumTrail :=
  { discreteTheoremAnchor :=
      "R(q)=q·v·q⁻¹ on Q8 and 2T is a 2:1 hom, kernel {±1}, image = V4(4)/T(12); belt trick R@2π vs spinor@4π"
  , continuumRefinementAnchor :=
      "is the finite restriction of the Lie cover SU(2)→SO(3): surjective 2:1, kernel {±I}, exp(2π)=−I in SU(2) but I in SO(3) (cite docs/OrientationSpinorContinuous_SKELETON.md; do not import Mathlib)"
  , falsifierSketch :=
      "any sampled pair with R(pq)≠R(p)R(q), or a kernel element outside {±1}, or a computed cover index ≠ 2" }

/-- The trail's anchors are nonempty audit narration (kernel witness that the record is
    populated, mirroring `RusticChurchContinuumPromotion`'s string-slot discipline). -/
theorem cover_promotion_trail_populated :
    coverPromotionTrail.discreteTheoremAnchor ≠ ""
    ∧ coverPromotionTrail.continuumRefinementAnchor ≠ ""
    ∧ coverPromotionTrail.falsifierSketch ≠ "" := by
  refine ⟨by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- §6  Master certificate — the sampled cover, both tiers
-- ══════════════════════════════════════════════════════════

/-- **SPINOR-COVER-SAMPLED (master).** The SU(2)->SO(3) double cover, realized by the
    EXACT integer conjugation rotation `R(q)` and sampled on two finite SU(2) subgroups:

      (1) TIER 1 Q8: homomorphism (64 pairs), `R(q)=R(−q)`, kernel `{±1}`, image V4 of
          order 4 = `|Q8|/2`, cover index 2 = the spinor fibre (`q8_double_cover`).
      (2) TIER 2 2T: homomorphism (576 pairs), `R(q)=R(−q)`, kernel `{±1}`, image the
          tetrahedral group of order 12 = `|2T|/2`, cover index 2 (`bt2_double_cover`).
      (3) PERIODICITY: rotation period 2π, spinor period 4π, computed on the `i`-axis
          loop (`belt_trick_sample`).
      (4) Both computed cover indices equal `OrientationE8Bridge.spinCoverIndex` — the
          conjugation computation reproduces the tabulated order-level shadow.

    This is the FINITE RESTRICTION of the continuous cover (§5 `coverPromotionTrail`); it
    does NOT establish surjectivity onto the full SO(3). -/
theorem spinor_cover_sampled_master :
    -- (1) Tier 1 Q8
    ((q8.all (fun a => q8.all (fun b =>
        decide (Rmat (qmul a b) = mmul (Rmat a) (Rmat b))))) = true
      ∧ q8_kernel.length = 2
      ∧ q8_image.length = 4
      ∧ q8.length / q8_image.length = 2)
    -- (2) Tier 2 2T
    ∧ ((bt2.all (fun a => bt2.all (fun b =>
        decide (Rmat (qmulScaled a b) = mdiv 4 (mmul (Rmat a) (Rmat b)))))) = true
      ∧ bt2_kernel.length = 2
      ∧ bt2_image.length = 12
      ∧ bt2.length / bt2_image.length = 2)
    -- (3) periodicity belt trick
    ∧ (Rmat qAt2pi = Id3 ∧ qAt2pi ≠ qAt0 ∧ qAt4pi = qAt0)
    -- (4) both indices tie to the order-level spinCoverIndex
    ∧ (q8.length / q8_image.length = OrientationE8Bridge.spinCoverIndex
      ∧ bt2.length / bt2_image.length = OrientationE8Bridge.spinCoverIndex) := by
  refine ⟨⟨q8_hom, (q8_kernel_is_pm_one).2, (q8_image_card_is_four).1,
            (q8_image_card_is_four).2⟩,
          ⟨bt2_hom, (bt2_kernel_is_pm_one).2, (bt2_image_card_is_twelve).1,
            (bt2_image_card_is_twelve).2⟩,
          ⟨(rotation_period_two_pi).1, (spinor_period_four_pi).1, (spinor_period_four_pi).2⟩,
          ⟨by decide, by decide⟩⟩

-- ══════════════════════════════════════════════════════════
-- §7  Reading + Next exploration
-- ══════════════════════════════════════════════════════════

/-! WHAT THIS MODULE IS. The SU(2)->SO(3) double cover sampled where it is EXACT: on the
    finite SU(2) subgroups Q8 and 2T, whose unit quaternions have exact algebraic
    coordinates (`{0,±1}` for Q8; `{0,±1,±2}` after the ×2 scaling for 2T). On those
    samples the conjugation rotation `R(q) = q·v·q⁻¹` is exact integer arithmetic, so the
    cover's defining properties — homomorphism, `{±1}` kernel, 2:1 fibre count — are
    closed finite `decide`s. This is the computational LIFT of the order-level shadow in
    `OrientationE8Bridge`: there `spinCoverIndex = 2` and `|2T| = 2·|T|` were tabulated;
    here they are COMPUTED from the conjugation matrices.

    SCOPE / HONESTY. This is the FINITE RESTRICTION of the continuous cover, not the
    continuous cover. Surjectivity onto the full SO(3), real-manifold continuity, and
    `exp(2π) = −I` as a one-parameter-subgroup statement all need Mathlib and are deferred
    (§5 trail, cited skeleton `docs/OrientationSpinorContinuous_SKELETON.md`).

    DECIDE BUDGET (kernel `decide`, no `native_decide`):
      * Q8: 64-pair homomorphism, 8-element kernel/image scans — instant.
      * 2T: 576-pair homomorphism + 576-pair closure, 24-element kernel/image — fast
        (a few seconds in the kernel).
      * 2O (48) / 2I (120): the quadratic-integer (`ℤ[√2]` / `ℤ[φ]`) closure and
        homomorphism over 2304 / 14400 pairs exceed the kernel `decide` budget (whnf
        heartbeat blow-up). They are NOT faked and NOT `native_decide`'d; the exact
        real-free ring setup is provided (`Zsqrt2`, `Zphi`, `zsqrt2_sq`, `zphi_sq`) and
        the cover on them is the Next exploration.

    -- Next exploration:
    --   TIER 3, the quadratic-integer covers, with the budget reorganized to avoid one
    --   giant `decide`.
    --     * 2O over ℤ[√2]. The 48 units are the 24 of 2T plus 24 of the form
    --       (±eᵢ±eⱼ)/√2; scaled ×2 their coordinates are `±√2 = ⟨0,±1⟩ ∈ Zsqrt2`. The
    --       Hamilton product and `Rmat` go through `zs2mul` (proved sound by `zsqrt2_sq`).
    --       The 2304-pair closure/homomorphism over-runs a single kernel `decide`;
    --       reorganize as a PER-GENERATOR homomorphism (2O is generated by a 2T generator
    --       plus one (e₀+e₁)/√2 unit) plus a closure-under-generators argument, so each
    --       `decide` is over a handful of products, not 2304. Expected: image = octahedral
    --       rotation group O=S4 (order 24), kernel {±1}, 48/24 = 2.
    --     * 2I over ℤ[φ]. The 120 icosian units live in ℤ[φ] (φ² = φ+1, `zphimul`, proved
    --       sound by `zphi_sq`); scaled to clear the /2 they are integer 4-tuples over
    --       ℤ[φ]. The 14400-pair check is far past a single `decide`; the per-generator +
    --       orbit-closure structuring is mandatory. Landing 2I would upgrade
    --       `OrientationE8Bridge`'s 2I→E8 order arithmetic (`binary_is_2to1_spin_cover`,
    --       `icosa_spin_cover_lands_on_E8`) to an ACTUAL kernel computation: image =
    --       icosahedral rotation group I=A5 (order 60), kernel {±1}, 120/60 = 2.
    --     * The continuum lift (the real deferral): with Mathlib, build the genuine Lie
    --       cover SU(2)→SO(3) (unit quaternions acting on ℝ³ by conjugation, or
    --       `Matrix.SpecialUnitaryGroup (Fin 2) ℂ → Matrix.specialOrthogonalGroup`), prove
    --       it surjective with kernel {±I}, and prove the maps here are its finite
    --       restriction — `q8`, `bt2` are the rational/quadratic-integer points of the Lie
    --       cover, and `Rmat` is the restriction of the conjugation action. Then the 2:1
    --       count stops being a tabulated index and becomes a kernel theorem. The hard part
    --       is the real-manifold surjectivity-with-{±I}-kernel argument.
-/

/-! ## Axiom footprint (verified)

`#print axioms` on every headline theorem reports **"does not depend on any axioms"**
(zero — stronger than the propext-at-most target). Verified with the v4.28.0 kernel:

    q8_double_cover                         -- no axioms
    q8_hom                                  -- no axioms
    q8_kernel_is_pm_one                     -- no axioms
    q8_image_card_is_four                   -- no axioms
    q8_cover_index_ties_to_spinor_fibre     -- no axioms
    bt2_double_cover                        -- no axioms
    bt2_hom                                 -- no axioms
    bt2_closed                              -- no axioms
    bt2_kernel_is_pm_one                    -- no axioms
    bt2_image_card_is_twelve                -- no axioms
    bt2_cover_index_ties_to_shadow          -- no axioms
    belt_trick_sample                       -- no axioms
    spinor_period_four_pi                   -- no axioms
    rotation_period_two_pi                  -- no axioms
    zsqrt2_sq / zphi_sq                     -- no axioms
    cover_promotion_trail_populated         -- no axioms
    spinor_cover_sampled_master             -- no axioms

No `native_decide`, no `sorry`, no `admit`, no new `axiom`, no `Classical.choice`.
-/

end SpinorCoverSampled
end Gnosis
