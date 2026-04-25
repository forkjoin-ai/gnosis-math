/-!
# Buleyean Logic

Basic logical and functional primitives for the sovereign kernel.
Disconnected from `Mathlib`, anchored in Lean 4 `Init`.
-/

namespace Gnosis.Logic

universe u v

/-- A function is injective if `f x = f y` implies `x = y`. -/
def Injective {α : Sort u} {β : Sort v} (f : α → β) : Prop :=
  ∀ {a₁ a₂}, f a₁ = f a₂ → a₁ = a₂

/-- A function on a partially ordered type is strictly monotonic if `x < y` implies `f x < f y`. -/
def StrictMono {α : Type u} {β : Type v} [LT α] [LT β] (f : α → β) : Prop :=
  ∀ {a b}, a < b → f a < f b

/-- An injective function is its own witness to injectivity (fully constructive for Nat). -/
theorem StrictMono.injective_nat {β : Type v} {f : Nat → β} {lt : β → β → Prop}
    (h_irrefl : ∀ x, ¬ lt x x)
    (h_mono : ∀ {a b}, a < b → lt (f a) (f b)) : Injective f := by
  intro a₁ a₂ heq
  match Nat.lt_trichotomy a₁ a₂ with
  | .inl hlt => 
    have := h_mono hlt
    rw [heq] at this
    exact (h_irrefl _ this).elim
  | .inr (.inl heq') => exact heq'
  | .inr (.inr hgt) => 
    have := h_mono hgt
    rw [heq] at this
    exact (h_irrefl _ this).elim

end Gnosis.Logic
