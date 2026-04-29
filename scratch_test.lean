import Init

def mapInstruction : String → List Nat
  | "AND" => [1]
  | "OR"  => [1]
  | "XOR" => [1]
  | _     => []

theorem test (op : String) (h : op ∈ ["AND", "OR", "XOR"]) : (mapInstruction op).length > 0 := by
  repeat (cases h)
  · simp [mapInstruction]; decide
  · repeat (cases h)
    · simp [mapInstruction]; decide
    · repeat (cases h)
      · simp [mapInstruction]; decide
      · cases h
