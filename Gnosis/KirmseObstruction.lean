/-
  KirmseObstruction
  ==================

  The KIRMSE MISTAKE and the COXETER FIX, certified.

  History
  -------
  Kirmse (1925) wrote the 240 minimal vectors of the E8 lattice as octonions
  in the natural `e0..e7` basis and claimed the resulting set of unit octonions
  (the "Kirmse integers") is closed under octonion multiplication — hence a
  maximal arithmetic order. Coxeter (1946) pointed out the error: the Kirmse
  set is NOT closed under the product. Coxeter further showed the fix: swap the
  real coordinate `a0` with any one imaginary coordinate `aj` (j = 1..7), and
  the resulting set IS closed. The seven choices of `j` give the seven maximal
  orders (the octavian / Cayley integers), all cyclically equivalent.

  What this module certifies (no `sorry`, no new axiom)
  ----------------------------------------------------
  We work in the integer-scaled model: each unit octonion of norm 1 is written
  as an integer vector of squared-norm 4 (scale ×2). The 240 Kirmse units are

      * `±2 eᵢ`                                    (16 vectors)
      * `±1 ± eᵢ ± eⱼ ± eₖ` with `{i,j,k}` a Fano line   (112 vectors)
      * `± eₚ ± e_q ± e_r ± e_s` with `{p,q,r,s}` the
        four imaginary units OFF a Fano line             (112 vectors)

  all of squared-norm 4. (The leading `±1` is the `e0` coordinate.)

  The octonion product is the integer bilinear map `omul`, built from the signed
  Fano multiplication table `Gnosis.FanoOctonionNonAssoc.mulBasis`. The product
  of two norm²=4 units has norm²=16; dividing by `2` (always exact here) returns
  it to the norm²=4 scale. That is the *normalized product* `nprod`.

    `kirmse_not_closed`  — an EXPLICIT witness pair `u, v ∈ kirmseUnits` whose
      normalized product leaves the set:
          u = (1,1,1,1,0,0,0,0),  v = (1,1,0,0,1,1,0,0),
          nprod u v = (0,1,1,0,0,1,0,1)  ∉ kirmseUnits.
      (Out of all 57600 ordered pairs, 43008 leave the set — the mistake is
      not a fluke; the witness is just one certified instance.)

    `coxeter_closed`     — applying Coxeter's coordinate swap `σ = a0 ↔ a7`
      to every unit yields `coxeterUnits`, and ALL 240×240 = 57600 normalized
      products land back inside `coxeterUnits`.

    `kirmse_coxeter_master` — bundles both (not closed before, closed after).

  Footprint: `native_decide` (⇒ `ofReduceBool`, `trustCompiler`) and `decide`
  (⇒ `propext` / none). No `sorryAx`, no `Classical.choice`.
-/

import Gnosis.FanoOctonionNonAssoc

namespace Gnosis
namespace KirmseObstruction

open Gnosis.FanoOctonionNonAssoc (SB mulBasis)

-- ══════════════════════════════════════════════════════════
-- INTEGER OCTONION PRODUCT (length-8 vectors, via the Fano table)
-- ══════════════════════════════════════════════════════════

/-- Euclidean squared norm of an integer 8-vector. -/
def normSq (v : List Int) : Int :=
  (v.map (fun x => x * x)).foldl (· + ·) 0

/-- Look up the integer coefficient at output index `k` of the basis product
`eᵢ · eⱼ`: the signed Fano table gives `eᵢ·eⱼ = ± e_{idx}`; this returns
`±1` if that output index is `k`, else `0`. -/
def basisCoeff (i j : Fin 8) (k : Nat) : Int :=
  let p := mulBasis i j
  if p.idx.val == k then (if p.sign then 1 else -1) else 0

/-- Integer octonion product `a · b` of two length-8 vectors, accumulating
signed contributions per output index from the Fano multiplication table.
Output index `k` gets `Σ_{i,j} a[i] · b[j] · ⟨coeff of e_k in eᵢ·eⱼ⟩`. -/
def omul (a b : List Int) : List Int :=
  (List.range 8).map (fun k =>
    ((List.range 8).flatMap (fun i =>
      (List.range 8).map (fun j =>
        let ai := (a[i]?).getD 0
        let bj := (b[j]?).getD 0
        ai * bj * basisCoeff ⟨i % 8, by omega⟩ ⟨j % 8, by omega⟩ k))).foldl (· + ·) 0)

/-- The normalized product. The product of two scaled-by-2 unit octonions has
squared-norm 16; it is always divisible by 2 (verified by the closure theorems
landing on norm²=4 vectors), and dividing by 2 returns it to the unit scale. -/
def nprod (a b : List Int) : List Int :=
  (omul a b).map (fun x => x / 2)

-- ══════════════════════════════════════════════════════════
-- THE 240 KIRMSE UNITS  (integer model, norm² = 4)
-- ══════════════════════════════════════════════════════════

/-- The seven Fano lines (triples of imaginary indices), matching the triples
used by `Gnosis.FanoOctonionNonAssoc.mulImag`. -/
def fanoLines : List (List Nat) :=
  [[1,2,3],[1,4,5],[1,7,6],[2,4,6],[2,5,7],[3,4,7],[3,6,5]]

/-- All sign patterns of length `n` over `{-1,+1}`. -/
def signs : Nat → List (List Int)
  | 0     => [[]]
  | n + 1 => (signs n).flatMap (fun tl => [(-1 : Int) :: tl, (1 : Int) :: tl])

/-- Place signed `±1` entries at the given index list `idxs`, zeros elsewhere,
producing a length-8 vector. `sgn` supplies the signs in order. -/
def placeSigned (idxs : List Nat) (sgn : List Int) : List Int :=
  (List.range 8).map (fun k =>
    match (idxs.zip sgn).find? (fun p => p.1 == k) with
    | some (_, s) => s
    | none        => 0)

/-- Type-1 units: `±2 eᵢ`, the basis units scaled ×2. 16 vectors. -/
def unitsBasis : List (List Int) :=
  (List.range 8).flatMap (fun i =>
    [(List.range 8).map (fun k => if k == i then (2 : Int) else 0),
     (List.range 8).map (fun k => if k == i then (-2 : Int) else 0)])

/-- Type-2 units: `½(±1 ± eᵢ ± eⱼ ± eₖ)` with `{i,j,k}` a Fano line, scaled ×2
to `±1 ± eᵢ ± eⱼ ± eₖ` (the leading sign is the `e0` coordinate). 112 vectors. -/
def unitsOnLine : List (List Int) :=
  fanoLines.flatMap (fun line =>
    (signs 4).map (fun sg => placeSigned (0 :: line) sg))

/-- Type-3 units: `½(± eₚ ± e_q ± e_r ± e_s)` with `{p,q,r,s}` the four
imaginary units OFF a Fano line (the complement in `{1..7}` of the line),
scaled ×2. 112 vectors. -/
def unitsOffLine : List (List Int) :=
  fanoLines.flatMap (fun line =>
    let comp := ((List.range 7).map (· + 1)).filter (fun x => !(line.contains x))
    (signs 4).map (fun sg => placeSigned comp sg))

/-- The 240 Kirmse units in the integer model (squared-norm 4). -/
def kirmseUnits : List (List Int) :=
  unitsBasis ++ unitsOnLine ++ unitsOffLine

theorem kirmse_count : kirmseUnits.length = 240 := by native_decide

/-- Every Kirmse unit has squared-norm 4 (norm homogeneity in the ×2 model). -/
theorem kirmse_norm_homogeneous :
    kirmseUnits.all (fun v => normSq v == 4) = true := by native_decide

/-- The 240 units are distinct (no duplicates among the three families). -/
theorem kirmse_distinct :
    kirmseUnits.eraseDups.length = 240 := by native_decide

-- ══════════════════════════════════════════════════════════
-- (1) THE KIRMSE MISTAKE — explicit non-closure witness
-- ══════════════════════════════════════════════════════════

/-- Witness `u = (1,1,1,1,0,0,0,0)`: a type-2 unit on the Fano line `{1,2,3}`
(the `e0` coordinate is the leading `+1`). -/
def wu : List Int := [1, 1, 1, 1, 0, 0, 0, 0]

/-- Witness `v = (1,1,0,0,1,1,0,0)`: a type-2 unit on the Fano line `{1,4,5}`. -/
def wv : List Int := [1, 1, 0, 0, 1, 1, 0, 0]

/-- Both witnesses are genuine Kirmse units. -/
theorem witnesses_are_units :
    kirmseUnits.contains wu = true ∧ kirmseUnits.contains wv = true := by
  refine ⟨by native_decide, by native_decide⟩

/-- The normalized product of the two witnesses is `(0,1,1,0,0,1,0,1)`. -/
theorem witness_product_value :
    nprod wu wv = [0, 1, 1, 0, 0, 1, 0, 1] := by native_decide

/-- The normalized product still has squared-norm 4 — it IS a lattice unit,
just not a *Kirmse* one. -/
theorem witness_product_norm :
    normSq (nprod wu wv) = 4 := by native_decide

/--
**The Kirmse mistake, certified.** There exist two Kirmse units whose
normalized octonion product leaves the Kirmse set. The witness pair is
`u = (1,1,1,1,0,0,0,0)` and `v = (1,1,0,0,1,1,0,0)`; their normalized product
`(0,1,1,0,0,1,0,1)` is a norm-4 lattice vector supported on indices
`{1,2,5,7}` — which is neither a Fano line nor an off-line quad — so it is
NOT one of the 240 Kirmse units. Hence the Kirmse integers are not closed
under multiplication, contradicting Kirmse's claim.
-/
theorem kirmse_not_closed :
    kirmseUnits.contains wu = true
  ∧ kirmseUnits.contains wv = true
  ∧ kirmseUnits.contains (nprod wu wv) = false := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- For the record: the failure is pervasive, not a fluke. Of all 240×240 =
57600 ordered pairs of Kirmse units, the count whose normalized product leaves
the set is positive (in fact 43008). -/
theorem kirmse_failure_is_pervasive :
    (kirmseUnits.flatMap (fun u =>
      kirmseUnits.map (fun v =>
        if kirmseUnits.contains (nprod u v) then 0 else 1))).foldl (· + ·) 0
      = 43008 := by native_decide

-- ══════════════════════════════════════════════════════════
-- (2) THE COXETER FIX — swap a0 ↔ a7, then the set closes
-- ══════════════════════════════════════════════════════════

/-- Coxeter's coordinate swap `σ`: exchange the real coordinate `a0` with the
imaginary coordinate `a7`. (Any `j = 1..7` works and gives a maximal order;
we fix `j = 7`.) -/
def sigma (v : List Int) : List Int :=
  (List.range 8).map (fun k =>
    if k == 0 then (v[7]?).getD 0
    else if k == 7 then (v[0]?).getD 0
    else (v[k]?).getD 0)

/-- The Coxeter-corrected set: every Kirmse unit with `a0 ↔ a7` swapped. -/
def coxeterUnits : List (List Int) := kirmseUnits.map sigma

theorem coxeter_count : coxeterUnits.length = 240 := by native_decide

/-- The swap is a bijection on the unit set restricted to norm, so the
corrected units are still 240 distinct norm-4 vectors. -/
theorem coxeter_distinct :
    coxeterUnits.eraseDups.length = 240 := by native_decide

theorem coxeter_norm_homogeneous :
    coxeterUnits.all (fun v => normSq v == 4) = true := by native_decide

/--
**The Coxeter fix, certified.** After swapping `a0 ↔ a7` in every Kirmse unit,
the resulting 240-element set IS closed under the normalized octonion product:
all 240 × 240 = 57600 normalized products land back inside `coxeterUnits`.
This certifies that Coxeter's coordinate swap turns the (non-closed) Kirmse
integers into a genuine maximal arithmetic order — one of the seven octavian
orders, all cyclically equivalent.
-/
theorem coxeter_closed :
    (coxeterUnits.flatMap (fun u =>
      coxeterUnits.map (fun v => nprod u v))).all
      (fun w => coxeterUnits.contains w) = true := by native_decide

/-- The same witness pair that broke the Kirmse set, mapped through `σ`, now
multiplies back into the corrected set — the fix repairs exactly the failure. -/
theorem coxeter_repairs_witness :
    coxeterUnits.contains (nprod (sigma wu) (sigma wv)) = true := by native_decide

-- ══════════════════════════════════════════════════════════
-- MASTER AGGREGATOR
-- ══════════════════════════════════════════════════════════

/--
**Kirmse–Coxeter master theorem.** In the integer (×2) octonion-unit model:

  (1) the 240 Kirmse units are NOT closed under the normalized octonion
      product — the explicit pair `wu, wv` is a certified counterexample; and

  (2) Coxeter's coordinate swap `σ = (a0 ↔ a7)` repairs it: all 57600
      normalized products of `coxeterUnits` land back in `coxeterUnits`.

Both halves are decided over the full finite data; no statement is weakened.
-/
theorem kirmse_coxeter_master :
    -- (1) Kirmse mistake: explicit witness leaves the set
    (kirmseUnits.contains wu = true
      ∧ kirmseUnits.contains wv = true
      ∧ kirmseUnits.contains (nprod wu wv) = false)
    -- (2) Coxeter fix: full closure after the a0 ↔ a7 swap
  ∧ ((coxeterUnits.flatMap (fun u =>
        coxeterUnits.map (fun v => nprod u v))).all
        (fun w => coxeterUnits.contains w) = true)
    -- both sets are the 240 norm-4 units
  ∧ (kirmseUnits.length = 240 ∧ coxeterUnits.length = 240) := by
  refine ⟨kirmse_not_closed, coxeter_closed, ?_⟩
  refine ⟨kirmse_count, coxeter_count⟩

end KirmseObstruction
end Gnosis
