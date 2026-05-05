def my_test (l : List Nat) (h : l.length = 3) : ∃ x ∈ l, x = x := by
  match eq : l with
  | [a, b, c] =>
    exact ⟨a, List.Mem.head _, rfl⟩
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | _ :: _ :: _ :: _ :: _ => simp at h
