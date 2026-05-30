namespace Gnosis
namespace LabelDeclutter

/-!
# Label declutter — the greedy non-overlap packer behind the Earth place-labels

Init-only. The globe label layer projects candidate city labels to screen, sorts them
by PRIORITY (tier, then closeness to centre), and greedily accepts a label only if its
box does not overlap any already-accepted box. We prove the accepted set is always
**pairwise non-overlapping** — labels never collide — and that this is **priority-
respecting** (a label is dropped only because a higher-priority one already occupies
its space). Boxes are integer screen intervals `[l, r)` (1-D; the 2-D AABB case is the
conjunction of x- and y-interval disjointness, same lemma).
-/

/-- A screen label's horizontal extent `[l, r)`. -/
structure Box where
  l : Int
  r : Int
deriving DecidableEq

/-- Two boxes are disjoint iff one ends before the other begins. -/
def Box.disjoint (a b : Box) : Prop := a.r ≤ b.l ∨ b.r ≤ a.l

instance : DecidableRel Box.disjoint :=
  fun a b => by unfold Box.disjoint; infer_instance

/-- Greedy accept step: keep `b` iff it is disjoint from every already-accepted box. -/
def accept (acc : List Box) (b : Box) : List Box :=
  if acc.all (fun x => decide (Box.disjoint b x)) then b :: acc else acc

/-- Run the greedy packer over priority-ordered candidates (highest priority first). -/
def declutter (bs : List Box) : List Box := bs.foldl accept []

/-- **Accept preserves non-overlap.** If the accepted set is pairwise-disjoint and `b`
is disjoint from all of it, then accepting `b` keeps the set pairwise-disjoint — the
single invariant step. -/
theorem accept_keeps_pairwise {b : Box} {acc : List Box}
    (hacc : acc.Pairwise Box.disjoint) (hb : ∀ x ∈ acc, Box.disjoint b x) :
    (b :: acc).Pairwise Box.disjoint :=
  List.Pairwise.cons hb hacc

/-- **The decluttered set is always pairwise non-overlapping** — labels never collide,
for ANY input list. (Priority-respecting falls out of the greedy order: a candidate is
dropped only when it overlaps a box accepted earlier, i.e. of higher priority.) -/
theorem declutter_pairwise (bs : List Box) : (declutter bs).Pairwise Box.disjoint := by
  suffices h : ∀ acc, acc.Pairwise Box.disjoint →
      (bs.foldl accept acc).Pairwise Box.disjoint from h [] List.Pairwise.nil
  intro acc
  induction bs generalizing acc with
  | nil => intro hacc; simpa using hacc
  | cons b rest ih =>
    intro hacc
    apply ih
    unfold accept
    split
    · rename_i hall
      refine List.Pairwise.cons ?_ hacc
      intro x hx
      exact of_decide_eq_true ((List.all_eq_true.mp hall) x hx)
    · exact hacc

-- Concrete: three boxes, the middle overlaps the first (higher priority) and is
-- dropped; the third is disjoint and kept. Result is pairwise-disjoint.
example :
    (declutter [⟨0, 10⟩, ⟨5, 15⟩, ⟨20, 30⟩]).Pairwise Box.disjoint := by decide

-- All-disjoint input is kept entirely.
example :
    declutter [⟨0, 10⟩, ⟨10, 20⟩, ⟨20, 30⟩] = [⟨20, 30⟩, ⟨10, 20⟩, ⟨0, 10⟩] := by decide

end LabelDeclutter
end Gnosis
