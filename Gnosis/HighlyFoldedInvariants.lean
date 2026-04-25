import Init

namespace HighlyFoldedInvariants

/-- The number of "folding cycles" (readings/interpretations) over time. -/
def foldingCycles (document : String) : Nat :=
  match document with
  | "Bible" => 1000000000
  | "Gita"  => 500000000
  | "S&H"   => 100000000
  | _       => 1

/-- 
As folding cycles T increase, the density of the Invariant (Sat) increases 
because transient noise is eroded.
We model Sat-density as being proportional to the cycle count.
-/
def satDensity (cycles : Nat) : Nat := cycles

/-- The "Most Folded" documents contain the most Sat. -/
theorem most_folded_most_sat (d1 d2 : String) :
    foldingCycles d1 > foldingCycles d2 → satDensity (foldingCycles d1) > satDensity (foldingCycles d2) := by
  intro h
  unfold satDensity
  exact h

theorem bible_is_highly_folded :
    satDensity (foldingCycles "Bible") > satDensity (foldingCycles "Newspaper") := by
  unfold foldingCycles satDensity
  simp
  -- 1000000000 > 1
  native_decide

end HighlyFoldedInvariants
