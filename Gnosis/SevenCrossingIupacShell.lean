import Init
import Gnosis.IupacResolutionCubeBound
import Gnosis.KhovanovCategorifiesJones
import Gnosis.KhovanovDiagramWellFormed

/-!
# Seven-crossing resolution **shell** for IUPAC labeling (`2^7 = 128`)

Concrete `Diagram` with `n₊ + n₋ = 7`, `128` `List.ofFn` rows, injective `Fin 118`
labels via distinct cells.

## Scope / non-goals

* **Bookkeeping shell**: the table’s **`2^7`** length matches Kauffman-cube **cardinality** (`KhovanovDiagramWellFormed.isResolutionCubeShaped`) and IUPAC slotting; it does **not** assert a faithful **`k(α)`** column (chemistry), **ambient isotopy** in `ℝ³`, or that tags coincide with classical Seifert-circle counts from a physical projection.
* **Jones / bracket here**: combinatorial **shadows** in `KhovanovCategorifiesJones` (`bracket`, `jonesPoly`); no claim of equality with an externally normalized Jones polynomial package beyond these definitions.

Indexing the `k`-th column by `IupacResolutionCubeBound.rowSlotFin128 row` hits the
`(row.val, 0)` tag that distinguishes lists in `sevenCubeTaggedList_injective`
(`sevenCubeCell_at_rowSlotFin128`, refined as a `List.getElem` equality in
`getElem_sevenCubeTaggedList_rowSlotFin128` and the **`k(α)`-slot second projection**
lemmas `getElem_*_rowSlotFin128_snd` below).  Along `KhovanovCategorifiesJones.qdimVk`, this reads
back **`V^{⊗0}`** (`qdimVk_sevenCrossing_resolutions_rowSlotFin128`).  The matching
**bracket summand** is `khovanovBracketSummand_sevenCrossing_rowSlotFin128`.
`jonesPoly_sevenCrossingTaggedDiagram` unfolds the Jones shift (`q^7 · bracket`) at `n₋ = 0`.
`bracket_sevenCrossingTaggedDiagram_rowSlotFin128` rewrites the same peel onto **`bracket (Diagram …)`**
via `bracket_eq_bracketResolutions`; `jonesPoly_sevenCrossingTaggedDiagram_rowSlotFin128` applies the **`q^7`** shift
to that peeled fold.  **`khovanovBracketSummand_sevenCrossing_pair_row_val`** expands the **`(row.val, 0)`** middle
term to **`shiftPow (scale parity · constP 1) (row.val)`**; **`_*_closedSummand`** lemmas substitute that expansion
inside the peeled **`bracket`** / **`jonesPoly`** folds.
The canonical row is a **member** of `resolutions` (`mem_resolutions_rowSlotFin128`).

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace SevenCrossingIupacShell

open KhovanovCategorifiesJones
open KhovanovDiagramWellFormed (isResolutionCubeShaped resolutionCubeCardinality)

def sevenCubeCell (row : Fin 118) (idx : Fin 128) : Nat × Nat :=
  if idx.val = row.val then (row.val, 0) else (idx.val, 1)

theorem sevenCubeCell_eq_of_val_eq (row : Fin 118) {idx idx' : Fin 128}
    (hv : idx.val = idx'.val) : sevenCubeCell row idx = sevenCubeCell row idx' := by
  simp [sevenCubeCell, hv]

def sevenCubeTaggedList (row : Fin 118) : List (Nat × Nat) :=
  List.ofFn (sevenCubeCell row)

def sevenCrossingTaggedDiagram (row : Fin 118) : Diagram :=
  ⟨7, 0, sevenCubeTaggedList row⟩

/-- The `2^7` slot from `IupacResolutionCubeBound.rowSlotFin128` indexes the row’s
distinguished `(row.val, 0)` cell in the shell table. -/
theorem sevenCubeCell_at_rowSlotFin128 (row : Fin 118) :
    sevenCubeCell row (IupacResolutionCubeBound.rowSlotFin128 row) = (row.val, 0) := by
  simp [sevenCubeCell, IupacResolutionCubeBound.rowSlotFin128]

theorem sevenCrossingTagged_list_length (row : Fin 118) :
    (sevenCubeTaggedList row).length = 128 := by
  rw [sevenCubeTaggedList, List.length_ofFn]

theorem rowSlotFin128_lt_sevenCubeTaggedList_length (row : Fin 118) :
    (IupacResolutionCubeBound.rowSlotFin128 row).val < (sevenCubeTaggedList row).length := by
  rw [sevenCrossingTagged_list_length]
  exact (IupacResolutionCubeBound.rowSlotFin128 row).isLt

/-- `List.getElem` at the canonical `2^7` slot: column `(row.val, 0)` from `sevenCubeCell_at_rowSlotFin128`. -/
theorem getElem_sevenCubeTaggedList_rowSlotFin128 (row : Fin 118) :
    (sevenCubeTaggedList row)[(IupacResolutionCubeBound.rowSlotFin128 row).val]'
      (rowSlotFin128_lt_sevenCubeTaggedList_length row) = (row.val, 0) := by
  -- Avoid `rw [sevenCubeTaggedList]` (no equation lemma); `change` exposes `List.ofFn`.
  change (List.ofFn (sevenCubeCell row))[(IupacResolutionCubeBound.rowSlotFin128 row).val]'
      (rowSlotFin128_lt_sevenCubeTaggedList_length row) = (row.val, 0)
  rw [List.getElem_ofFn]
  rw [← sevenCubeCell_eq_of_val_eq row rfl]
  exact sevenCubeCell_at_rowSlotFin128 row

/-- At the canonical slot, the resolution-row **tag bit** (`Nat × Nat` second component) is `0`. -/
theorem getElem_sevenCubeTaggedList_rowSlotFin128_snd (row : Fin 118) :
    ((sevenCubeTaggedList row)[(IupacResolutionCubeBound.rowSlotFin128 row).val]'
          (rowSlotFin128_lt_sevenCubeTaggedList_length row)).2 =
        0 := by
  rw [getElem_sevenCubeTaggedList_rowSlotFin128 row]

theorem getElem_sevenCrossingTaggedDiagram_resolutions_rowSlotFin128 (row : Fin 118) :
    ((sevenCrossingTaggedDiagram row).resolutions)[(IupacResolutionCubeBound.rowSlotFin128 row).val]'
      (rowSlotFin128_lt_sevenCubeTaggedList_length row) = (row.val, 0) := by
  simpa [sevenCrossingTaggedDiagram] using getElem_sevenCubeTaggedList_rowSlotFin128 row

theorem getElem_sevenCrossingTaggedDiagram_resolutions_rowSlotFin128_snd (row : Fin 118) :
    (((sevenCrossingTaggedDiagram row).resolutions)[(IupacResolutionCubeBound.rowSlotFin128 row).val]'
          (rowSlotFin128_lt_sevenCubeTaggedList_length row)).2 =
        0 := by
  rw [getElem_sevenCrossingTaggedDiagram_resolutions_rowSlotFin128 row]

/-- At `rowSlotFin128`, the shell tags **`k(α) = 0`**, hence **`qdim V^{⊗k}`** is **`1`**
(Bar–Natan `qdimVk k = (q + q⁻¹)^k` with `k = 0`). -/
theorem qdimVk_sevenCrossing_resolutions_rowSlotFin128 (row : Fin 118) :
    qdimVk (((sevenCrossingTaggedDiagram row).resolutions)[(IupacResolutionCubeBound.rowSlotFin128 row).val]'
      (rowSlotFin128_lt_sevenCubeTaggedList_length row)).2 =
      LaurentPoly.constP 1 :=
  (congrArg qdimVk (getElem_sevenCrossingTaggedDiagram_resolutions_rowSlotFin128_snd row)).trans
    qdimVk_zero

/-- `khovanovBracketSummand` at `rowSlotFin128`: parity sign, `q^{|α|}`, and `qdimVk 0 = 1`. -/
theorem khovanovBracketSummand_sevenCrossing_rowSlotFin128 (row : Fin 118) :
    khovanovBracketSummand
      (((sevenCrossingTaggedDiagram row).resolutions)[(IupacResolutionCubeBound.rowSlotFin128 row).val]'
        (rowSlotFin128_lt_sevenCubeTaggedList_length row)) =
      LaurentPoly.shiftPow
        (LaurentPoly.scale (if row.val % 2 = 0 then (1 : Int) else -1) (LaurentPoly.constP 1))
        (Int.ofNat row.val) := by
  rw [getElem_sevenCrossingTaggedDiagram_resolutions_rowSlotFin128 row]
  simp [khovanovBracketSummand, qdimVk_zero]

/-- Closed form of **`khovanovBracketSummand (row.val, 0)`** (same data as `khovanovBracketSummand_sevenCrossing_rowSlotFin128`). -/
theorem khovanovBracketSummand_sevenCrossing_pair_row_val (row : Fin 118) :
    khovanovBracketSummand (row.val, 0) =
      LaurentPoly.shiftPow
        (LaurentPoly.scale (if row.val % 2 = 0 then (1 : Int) else -1) (LaurentPoly.constP 1))
        (Int.ofNat row.val) := by
  simp [khovanovBracketSummand, qdimVk_zero]

/-- Peel `bracketResolutions` at **`rowSlotFin128`**: the middle Khovanov summand is **`(row.val, 0)`**
(`bracketResolutions_split` composed with `getElem_sevenCubeTaggedList_rowSlotFin128`). -/
theorem bracketResolutions_sevenCubeTaggedList_rowSlotFin128 (row : Fin 118) :
    bracketResolutions (sevenCubeTaggedList row) =
      ((sevenCubeTaggedList row).drop ((IupacResolutionCubeBound.rowSlotFin128 row).val + 1)).foldl
        (fun acc p => LaurentPoly.add acc (khovanovBracketSummand p))
        (LaurentPoly.add
          (bracketResolutions ((sevenCubeTaggedList row).take (IupacResolutionCubeBound.rowSlotFin128 row).val))
          (khovanovBracketSummand (row.val, 0))) := by
  simpa [getElem_sevenCubeTaggedList_rowSlotFin128 row] using
    bracketResolutions_split (sevenCubeTaggedList row) (IupacResolutionCubeBound.rowSlotFin128 row).val
      (rowSlotFin128_lt_sevenCubeTaggedList_length row)

/-- Same **`rowSlotFin128`** peel for **`bracket (sevenCrossingTaggedDiagram row)`** (via `bracket_eq_bracketResolutions`). -/
theorem bracket_sevenCrossingTaggedDiagram_rowSlotFin128 (row : Fin 118) :
    bracket (sevenCrossingTaggedDiagram row) =
      ((sevenCrossingTaggedDiagram row).resolutions.drop ((IupacResolutionCubeBound.rowSlotFin128 row).val + 1)).foldl
        (fun acc p => LaurentPoly.add acc (khovanovBracketSummand p))
        (LaurentPoly.add
          (bracketResolutions
            ((sevenCrossingTaggedDiagram row).resolutions.take (IupacResolutionCubeBound.rowSlotFin128 row).val))
          (khovanovBracketSummand (row.val, 0))) := by
  simpa [sevenCrossingTaggedDiagram, bracket_eq_bracketResolutions] using
    bracketResolutions_sevenCubeTaggedList_rowSlotFin128 row

/-- Shell diagrams have **`n₊ = 7`**, **`n₋ = 0`**, so `jonesShift` multiplies `bracket` by **`q^7`** (no sign flip). -/
theorem jonesPoly_sevenCrossingTaggedDiagram (row : Fin 118) :
    jonesPoly (sevenCrossingTaggedDiagram row) =
      LaurentPoly.shiftPow (bracket (sevenCrossingTaggedDiagram row)) (Int.ofNat 7) := by
  simp [jonesPoly, jonesShift, sevenCrossingTaggedDiagram]

/-- `jonesPoly` as **`q^7`** times the **`rowSlotFin128`** bracket peel (compose `jonesPoly_sevenCrossingTaggedDiagram`). -/
theorem jonesPoly_sevenCrossingTaggedDiagram_rowSlotFin128 (row : Fin 118) :
    jonesPoly (sevenCrossingTaggedDiagram row) =
      LaurentPoly.shiftPow
        (((sevenCrossingTaggedDiagram row).resolutions.drop ((IupacResolutionCubeBound.rowSlotFin128 row).val + 1)).foldl
          (fun acc p => LaurentPoly.add acc (khovanovBracketSummand p))
          (LaurentPoly.add
            (bracketResolutions
              ((sevenCrossingTaggedDiagram row).resolutions.take (IupacResolutionCubeBound.rowSlotFin128 row).val))
            (khovanovBracketSummand (row.val, 0))))
        (Int.ofNat 7) := by
  rw [jonesPoly_sevenCrossingTaggedDiagram, bracket_sevenCrossingTaggedDiagram_rowSlotFin128 row]

/-- Peeled **`jonesPoly`** at `rowSlotFin128` with the middle Khovanov summand **expanded** (`khovanovBracketSummand_sevenCrossing_pair_row_val`). -/
theorem jonesPoly_sevenCrossingTaggedDiagram_rowSlotFin128_closedSummand (row : Fin 118) :
    jonesPoly (sevenCrossingTaggedDiagram row) =
      LaurentPoly.shiftPow
        (((sevenCrossingTaggedDiagram row).resolutions.drop ((IupacResolutionCubeBound.rowSlotFin128 row).val + 1)).foldl
          (fun acc p => LaurentPoly.add acc (khovanovBracketSummand p))
          (LaurentPoly.add
            (bracketResolutions
              ((sevenCrossingTaggedDiagram row).resolutions.take (IupacResolutionCubeBound.rowSlotFin128 row).val))
            (LaurentPoly.shiftPow
              (LaurentPoly.scale (if row.val % 2 = 0 then (1 : Int) else -1) (LaurentPoly.constP 1))
              (Int.ofNat row.val))))
        (Int.ofNat 7) := by
  simpa [khovanovBracketSummand_sevenCrossing_pair_row_val row] using
    jonesPoly_sevenCrossingTaggedDiagram_rowSlotFin128 row

/-- Peeled **`bracket`** at `rowSlotFin128` with the middle summand **expanded** (`khovanovBracketSummand_sevenCrossing_pair_row_val`). -/
theorem bracket_sevenCrossingTaggedDiagram_rowSlotFin128_closedSummand (row : Fin 118) :
    bracket (sevenCrossingTaggedDiagram row) =
      ((sevenCrossingTaggedDiagram row).resolutions.drop ((IupacResolutionCubeBound.rowSlotFin128 row).val + 1)).foldl
        (fun acc p => LaurentPoly.add acc (khovanovBracketSummand p))
        (LaurentPoly.add
          (bracketResolutions
            ((sevenCrossingTaggedDiagram row).resolutions.take (IupacResolutionCubeBound.rowSlotFin128 row).val))
          (LaurentPoly.shiftPow
            (LaurentPoly.scale (if row.val % 2 = 0 then (1 : Int) else -1) (LaurentPoly.constP 1))
            (Int.ofNat row.val))) := by
  simpa [khovanovBracketSummand_sevenCrossing_pair_row_val row] using
    bracket_sevenCrossingTaggedDiagram_rowSlotFin128 row

/-- The canonical `rowSlotFin128` entry lies in `Diagram.resolutions` (`getElem_mem`). -/
theorem mem_resolutions_rowSlotFin128 (row : Fin 118) :
    ((sevenCrossingTaggedDiagram row).resolutions)[(IupacResolutionCubeBound.rowSlotFin128 row).val]'
      (rowSlotFin128_lt_sevenCubeTaggedList_length row) ∈
    (sevenCrossingTaggedDiagram row).resolutions := by
  simp [sevenCrossingTaggedDiagram]

theorem sevenCrossingTagged_resolution_cube_shaped (row : Fin 118) :
    isResolutionCubeShaped (sevenCrossingTaggedDiagram row) = true := by
  simp [isResolutionCubeShaped, resolutionCubeCardinality, sevenCrossingTaggedDiagram,
    sevenCrossingTagged_list_length]

theorem sevenCubeTaggedList_injective : Function.Injective sevenCubeTaggedList := by
  intro i j hList
  apply Fin.ext
  by_cases hval : i.val = j.val
  · exact hval
  · let k : Fin 128 := ⟨i.val, Nat.lt_trans i.isLt (by decide : 118 < 128)⟩
    have hk_i : k.val < (sevenCubeTaggedList i).length := by
      rw [sevenCrossingTagged_list_length]; exact k.isLt
    have hk_j : k.val < (sevenCubeTaggedList j).length := by
      rw [sevenCrossingTagged_list_length]; exact k.isLt
    have hcell : sevenCubeCell i k = sevenCubeCell j k := by
      have hget := (List.ext_getElem_iff.mp hList).2 k.val hk_i hk_j
      dsimp only [sevenCubeTaggedList] at hget
      simpa only [List.getElem_ofFn, Fin.eta] using hget
    simp only [sevenCubeCell, k, hval] at hcell
    cases hcell

theorem sevenCrossingTaggedDiagram_injective :
    Function.Injective sevenCrossingTaggedDiagram := by
  intro i j hD
  exact sevenCubeTaggedList_injective (congrArg Diagram.resolutions hD)

end SevenCrossingIupacShell
end Gnosis
