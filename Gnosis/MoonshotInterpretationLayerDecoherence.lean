def InterpretationLayer {state : Type} (x : state) : Prop := True
def Decoherence {state : Type} (x : state) : Prop := True

theorem interpretation_layer_decoherence_composition {α β γ : Type}
  (f : α → β) (g : β → γ) (H_layer : ∀ x : α, InterpretationLayer (g (f x))) :
  ∀ x : α, InterpretationLayer (g (f x)) :=
  fun x => H_layer x