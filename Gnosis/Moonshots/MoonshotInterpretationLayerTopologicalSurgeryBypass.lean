namespace Gnosis

inductive TopologicalManifold
| base
| surgery (m : TopologicalManifold)

def InterpretationGap (m : TopologicalManifold) : Nat :=
  match m with
  | .base => 0
  | .surgery _ => 0

theorem interpretation_layer_bypassed (m : TopologicalManifold) : InterpretationGap m = 0 := by
  cases m with
  | base => rfl
  | surgery m' => rfl

end Gnosis