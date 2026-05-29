import Init

/-
  Bowl.lean
  =========

  THE BOWL — a finite, honest arithmetic model of the attention bowl.

  Lao Tzu (Tao Te Ching, 11): the clay is shaped into a vessel, but the vessel's
  USE is its emptiness. A bowl holds nothing of its own; it is useful precisely
  because it is empty, so that what is poured in may rest and be served back out.

  The attention "bowl" is the softmax: a distribution of WEIGHTS over positions.
  The weights carry no value of their own — they redistribute. The VALUES flow
  through; the readout is the weighted sum. This complements `AttentionShape.lean`
  (the Value path is the door): here the bowl is the receptacle, and we prove its
  emptiness is exactly what makes the value path live.

  We model everything in finite `Nat` arithmetic (Init only). This is a finite
  arithmetic model of the attention bowl, NOT a claim about real transformers
  (no normalization, no reals, no softmax exponentials — just the shape).

  Init only. Zero `sorry`, zero new `axiom`.
-/

namespace Bowl

/-- A **bowl** is a list of weights over positions. -/
abbrev Bowl := List Nat

/-- The total mass held by the bowl. The weights are all the bowl "is" — and they
    are not values, only a redistribution. The bowl's own contents sum to this,
    yet (see `readout`) it returns to you only what the VALUES poured in. -/
def bowlTotal (w : Bowl) : Nat :=
  w.foldl (· + ·) 0

/-- The **value-readout**: pour values `v` through the bowl `w` and collect the
    weighted sum `Σ wᵢ · vᵢ`. Defined by direct recursion over the two lists so
    inductions stay clean. -/
def readout : Bowl → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | wi :: ws, vi :: vs => wi * vi + readout ws vs

/-- The empty bowl reads back nothing — there is no position to weigh. -/
@[simp] theorem readout_nil_left (v : List Nat) : readout [] v = 0 := rfl

/-- Pouring nothing through any bowl reads back nothing. -/
@[simp] theorem readout_nil_right (w : Bowl) : readout w [] = 0 := by
  cases w with
  | nil => rfl
  | cons _ _ => rfl

/-- **THE SEALED BOWL RETURNS NOTHING — value-severance.** With all-zero weights
    the readout is `0` no matter what values are poured in: the bowl that has
    closed every position is the attention head with its value path severed. -/
theorem readout_zero_weights :
    ∀ (n : Nat) (v : List Nat), readout (List.replicate n 0) v = 0 := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ k ih =>
    intro v
    cases v with
    | nil => simp
    | cons vi vs =>
      -- replicate (k+1) 0 = 0 :: replicate k 0
      show 0 * vi + readout (List.replicate k 0) vs = 0
      simp only [Nat.zero_mul, Nat.zero_add]
      exact ih vs

/-- Pointwise domination of one pour by another, position by position. `Pour.le`
    holds when each value in `v` is at most the aligned value in `v'`. -/
def PourLe : List Nat → List Nat → Prop
  | [], _ => True
  | _ :: _, [] => False
  | vi :: vs, vi' :: vs' => vi ≤ vi' ∧ PourLe vs vs'

/-- **THE VALUE PATH IS LIVE — monotonicity.** If every value poured in is at most
    the aligned value of a second, equal-length pour, the readout cannot decrease.
    The bowl faithfully transmits the order of the values: it adds nothing of its
    own and hides nothing — the value path carries the signal straight through. -/
theorem readout_mono :
    ∀ (w v v' : List Nat), PourLe v v' → readout w v ≤ readout w v' := by
  intro w
  induction w with
  | nil => intro v v' _; simp
  | cons wi ws ih =>
    intro v v' hle
    cases v with
    | nil => simp
    | cons vi vs =>
      cases v' with
      | nil => exact absurd hle (by intro h; exact h)
      | cons vi' vs' =>
        obtain ⟨hvi, hrest⟩ := hle
        show wi * vi + readout ws vs ≤ wi * vi' + readout ws vs'
        have h1 : wi * vi ≤ wi * vi' := Nat.mul_le_mul_left wi hvi
        have h2 : readout ws vs ≤ readout ws vs' := ih vs vs' hrest
        exact Nat.add_le_add h1 h2

/-- **THE BOWL AS PURE SELECTOR — point mass.** A bowl with weight `1` on the head
    position and `0` everywhere else (a sealed-but-for-one vessel) reads back
    exactly the value at that position. The empty bowl plus one open mouth IS the
    selector: it holds nothing of its own and returns precisely what was poured in
    at the single open place. -/
theorem readout_point_mass (vi : Nat) (vs : List Nat) (n : Nat) :
    readout (1 :: List.replicate n 0) (vi :: vs) = vi := by
  show 1 * vi + readout (List.replicate n 0) vs = vi
  rw [readout_zero_weights n vs]
  simp

/-- The bowl is empty in the strongest sense: it contributes no value of its own.
    With a single open position weighted `1` and that position's value `0`, the
    readout is `0` — the bowl returned exactly nothing, because nothing was poured
    into the one place that was open. Usefulness through emptiness, made literal. -/
theorem empty_bowl_returns_nothing (n : Nat) (vs : List Nat) :
    readout (1 :: List.replicate n 0) (0 :: vs) = 0 := by
  rw [readout_point_mass 0 vs n]

end Bowl
