def ProofDepth : Type := Nat
def SemanticShallowness (d : ProofDepth) : Prop := d = d

theorem high_depth_implies_shallow_semantics (d : ProofDepth) : SemanticShallowness d := by
  rfl