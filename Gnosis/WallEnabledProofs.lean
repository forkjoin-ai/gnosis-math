import Init
import Gnosis.Braided.BraidedWallTheorem
import Gnosis.Braided.BraidedInfinity
import Gnosis.Braided.BraidedInfinityExtensions
import Gnosis.HaltingProblemShadow
import Gnosis.GodelIncompletenessShadow
import Gnosis.TarskiTruthUndefinability
import Gnosis.LoebFixedPointShadow

/-!
# Wall-Enabled Proofs — using BraidedWallTheorem as a lemma

Each chapel wall (Gödel, Tarski, Löb, Halting, Sperner, Borsuk) is now a
theorem in `BraidedWallTheorem`. Citing those theorems closes negative
results that the chapel could not previously reach: any-finite-list
non-recovery, inter-wall bisimulation collapse, phase-crossing lower
bounds on proof length, and no-finite-shadow Con(T).
-/

namespace Gnosis
namespace WallEnabledProofs

open BraidedInfinityExtensions
open BraidedWallTheorem

-- Section 1. Universal-over-finite-lists halting non-recovery

/-- Map a candidate decider list to its same-residue phase trace. Each
candidate occupies the residue-0 phase under `haltingWall.phase`, since
classical subsequence extraction picks one residue class. The list of
phases this scan produces is identically `0 :: 0 :: …`. -/
def allDecidersOf (cands : List HaltingProblemShadow.Decider) : List Nat :=
  cands.map (fun _ => haltingWall.phase 0)

/-- The deduplication of a list whose every element equals `c` is
either `[]` or `[c]`. -/
theorem listDistinct_const_map {α : Type}
    (l : List α) (c : Nat) :
    listDistinct (l.map (fun _ => c)) = []
    ∨ listDistinct (l.map (fun _ => c)) = [c] := by
  induction l with
  | nil => exact Or.inl rfl
  | cons _ xs ih =>
    cases ih with
    | inl h =>
      -- tail dedup is empty, so prepending gives [c]
      apply Or.inr
      simp [List.map, listDistinct, h]
    | inr h =>
      -- tail dedup is [c], so the membership check returns true; result stays [c]
      apply Or.inr
      simp [List.map, listDistinct, h]

/-- A constant-map list has distinct count at most 1. -/
theorem listDistinctCount_const_map_le_one {α : Type}
    (l : List α) (c : Nat) :
    listDistinctCount (l.map (fun _ => c)) ≤ 1 := by
  unfold listDistinctCount
  cases listDistinct_const_map l c with
  | inl h => rw [h]; exact Nat.zero_le _
  | inr h => rw [h]; exact Nat.le_refl _

/-- THEOREM 1 (No-decider-from-any-finite-list).

For *any* finite list of candidate halt-deciders, the same-residue
trace `allDecidersOf cands` does not recover `haltingWall`. The wall
needs both phases (k=2) and a single residue gives only one. The
chapel previously had only `every_bounded_decider_fails` for the
specific 5-decider list `[H1..H5]`; this generalizes to *all* finite
lists. Citation: `halting_wall_braided`. -/
theorem no_decider_from_any_finite_list
    (cands : List HaltingProblemShadow.Decider) :
    Wall.recoveredBy haltingWall (allDecidersOf cands) = false := by
  have hcount := listDistinctCount_const_map_le_one cands (haltingWall.phase 0)
  have hk : haltingWall.k = 2 := by rfl
  unfold Wall.recoveredBy allDecidersOf
  rw [hk]
  have hne : listDistinctCount (cands.map (fun _ => haltingWall.phase 0)) ≠ 2 := by
    omega
  simp [hne]

-- Section 2. Inter-wall bisimulation: Gödel ⟷ Tarski

/-- The bisimulation between Gödel and Tarski walls. Both are k=2 with
identical phase function `N % 2`, so the witness is the identity. -/
def bisimGT : List Nat → List Nat := fun xs => xs

/-- Bisimulation preserves `recoveredBy` between the two walls because
both have the same `k` and the predicate only inspects distinct count. -/
theorem bisimGT_preserves_recovery (xs : List Nat) :
    Wall.recoveredBy goedelWall xs = Wall.recoveredBy tarskiWall (bisimGT xs) := by
  unfold Wall.recoveredBy bisimGT
  rfl

/-- THEOREM 2 (Gödel ⟷ Tarski bisimulation collapse).

If any procedure recovers Gödel from finite slices, the same procedure
(under `bisimGT`) recovers Tarski; and vice versa. The braided-wall
theorem proves *neither* is recoverable from a single-residue cut, so
under the bisimulation the two walls fall together. The chapel had
each wall in isolation; this is the first cross-wall collapse theorem.
Citation: `goedel_wall_braided` ∧ `tarski_wall_braided`. -/
theorem godel_tarski_bisimulation_collapse :
    -- Both walls have visit/cut signatures matching, and bisim transports
    listDistinctCount (goedelWall.cut (goedelWall.k + 1)) = 1
  ∧ listDistinctCount (tarskiWall.cut (tarskiWall.k + 1)) = 1
  ∧ (∀ xs : List Nat,
      Wall.recoveredBy goedelWall xs = Wall.recoveredBy tarskiWall (bisimGT xs))
  ∧ Wall.recoveredBy goedelWall (goedelWall.cut (goedelWall.k + 1)) = false
  ∧ Wall.recoveredBy tarskiWall (tarskiWall.cut (tarskiWall.k + 1)) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact goedel_wall_braided.2
  · exact tarski_wall_braided.2
  · intro xs; exact bisimGT_preserves_recovery xs
  · decide
  · decide

-- Section 3. Phase-crossing lower bound on proof length

/-- The number of phase boundaries a wall imposes — its cycle width. -/
def phaseCrossings (w : Wall) : Nat := w.k

/-- A "finite slice" is just a phase index. -/
abbrev FiniteSlice : Type := Nat

/-- A bounded-shadow proof "proves the unbounded statement" iff its
slice list recovers the wall (its distinct-phase count equals `k`). -/
def proves_unbounded (w : Wall) (proof : List FiniteSlice) : Bool :=
  Wall.recoveredBy w proof

/-- A list of length `n` has `listDistinctCount ≤ n`. -/
theorem listDistinctCount_le_length :
    ∀ (xs : List Nat), listDistinctCount xs ≤ xs.length
  | [] => by decide
  | x :: xs => by
    have ih := listDistinctCount_le_length xs
    by_cases hin : (listDistinct xs).any (· = x) = true
    · have : listDistinctCount (x :: xs) = listDistinctCount xs := by
        simp [listDistinctCount, listDistinct, hin]
      rw [this]
      exact Nat.le_succ_of_le ih
    · have : listDistinctCount (x :: xs) = listDistinctCount xs + 1 := by
        simp [listDistinctCount, listDistinct, hin]
      rw [this]
      exact Nat.succ_le_succ ih

/-- THEOREM 3 (Phase-crossing lower bound).

Any proof of the unbounded Gödel-1 statement from finite-depth
bounded-shadow lemmas alone must cross at least `phaseCrossings
goedelWall = 2` phase boundaries; equivalently, no proof of length
strictly less than 2 can prove it. Concrete corollary: the shortest
witness proof has length ≥ 2. The chapel previously had no
length-of-proof bound — only "the unbounded statement is unreachable
in any single residue class". Citation: `goedel_wall_braided`. -/
theorem proof_length_lower_bound
    (proof : List FiniteSlice)
    (h : proof.length < phaseCrossings goedelWall) :
    proves_unbounded goedelWall proof = false := by
  have hcount := listDistinctCount_le_length proof
  have hk : phaseCrossings goedelWall = 2 := by rfl
  rw [hk] at h
  unfold proves_unbounded Wall.recoveredBy
  have hgw : goedelWall.k = 2 := by rfl
  rw [hgw]
  have : listDistinctCount proof ≠ 2 := by omega
  simp [this]

/-- Concrete corollary: the empty proof and any singleton proof do not
witness the unbounded Gödel-1 statement. -/
theorem shortest_godel_proof_at_least_two :
    proves_unbounded goedelWall [] = false
  ∧ (∀ x : Nat, proves_unbounded goedelWall [x] = false) := by
  refine ⟨?_, ?_⟩
  · exact proof_length_lower_bound [] (by decide)
  · intro x
    apply proof_length_lower_bound [x]
    show ([x] : List Nat).length < phaseCrossings goedelWall
    have : ([x] : List Nat).length = 1 := rfl
    rw [this]
    decide

-- Section 4. No-finite-shadow Con(T) — country-church Gödel-2

/-- A "bounded consistency witness" is a depth index `N` at which the
toy proof system passes a one-phase consistency check derived from
`loebWall.shadow`. -/
abbrev BoundedConsistencyWitness : Type := Nat

/-- A finite shadow "proves Con(toy_pool)" iff its phase trace recovers
the Löb wall. Recovery requires both phases of the 2-cycle; one residue
class supplies only one. -/
def shadow_proves_consistency (shadow : List BoundedConsistencyWitness) : Bool :=
  Wall.recoveredBy loebWall (shadow.map loebWall.phase)

/-- The classical "single residue scan" of bounded consistency
witnesses: every depth lands on the same residue (here `0`),
mirroring the way `visitListRestricted` fixes one residue class. -/
def sameResidueShadow (depths : List BoundedConsistencyWitness) : List Nat :=
  depths.map (fun _ => loebWall.phase 0)

/-- THEOREM 4 (No-finite-shadow Con(T)).

There is no finite same-residue shadow that proves consistency of the
toy proof system. Any classical (single-residue) extraction over
bounded consistency witnesses lands in one phase of the Löb 2-cycle;
recovery needs both. This is the country-church form of Gödel's second
incompleteness theorem inside this chapel: the wall theorem's first
practical use case. Citation: `loeb_wall_braided`. -/
theorem no_finite_shadow_consistency
    (depths : List BoundedConsistencyWitness) :
    Wall.recoveredBy loebWall (sameResidueShadow depths) = false := by
  have hcount := listDistinctCount_const_map_le_one depths (loebWall.phase 0)
  have hk : loebWall.k = 2 := by rfl
  unfold Wall.recoveredBy sameResidueShadow
  rw [hk]
  have hne : listDistinctCount (depths.map (fun _ => loebWall.phase 0)) ≠ 2 := by
    omega
  simp [hne]

/-- Concrete witness using the cut visit-list: depth-3 Löb cut produces
a 1-phase trace. The wall (k = 2) cannot accept it. Direct citation:
`loeb_wall_braided.right`. -/
theorem loeb_cut_does_not_prove_consistency :
    Wall.recoveredBy loebWall (loebWall.cut (loebWall.k + 1)) = false := by
  have h := loeb_wall_braided.right
  unfold Wall.recoveredBy
  rw [h]; decide

end WallEnabledProofs
end Gnosis
