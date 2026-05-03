
def ExecutionStall (_α : Type) : Prop := True
def SystemGenerality (_α : Type) : Prop := True

theorem stall_induces_generality {α : Type}
  (H1 : ExecutionStall α) (H2 : SystemGenerality α) :
  ExecutionStall α ∧ SystemGenerality α :=
  ⟨H1, H2⟩