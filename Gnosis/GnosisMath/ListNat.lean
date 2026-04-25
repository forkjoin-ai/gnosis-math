import Gnosis.GnosisMathPrelude

/-!
# GnosisMath list / Nat helpers (Init-only)

Small lemmas aligned with common Mathlib *patterns*; proofs stay in `Init`.
-/

namespace GnosisMath

/-- Four-factor rearrangement for `Nat.mul`. -/
theorem mul_mul_mul_mul (a b x y : Nat) : (a * b) * (x * y) = (a * x) * (b * y) := by
  simp [Nat.mul_comm, Nat.mul_left_comm]

/--
`powNat` distributes across a product in the base — parallel to `mul_pow` for `Nat.pow`
(source: Mathlib `mul_pow`).
-/
theorem powNat_mul_distrib (a b n : Nat) : powNat (a * b) n = powNat a n * powNat b n := by
  induction n with
  | zero => simp [powNat]
  | succ n ih =>
    calc
      powNat (a * b) (Nat.succ n)
          = (a * b) * powNat (a * b) n := rfl
      _ = (a * b) * (powNat a n * powNat b n) := by rw [ih]
      _ = (a * powNat a n) * (b * powNat b n) := mul_mul_mul_mul a b (powNat a n) (powNat b n)
      _ = powNat a (Nat.succ n) * powNat b (Nat.succ n) := rfl

theorem powNat_two (a : Nat) : powNat a 2 = a * a := by
  rw [show (2 : Nat) = Nat.succ 1 from rfl, powNat_succ, powNat_one]

theorem powNat_three (a : Nat) : powNat a 3 = a * a * a := by
  rw [show (3 : Nat) = Nat.succ 2 from rfl, powNat_succ, powNat_two, Nat.mul_assoc]

theorem one_powNat (n : Nat) : powNat 1 n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [powNat_succ, ih, Nat.one_mul]

theorem powNat_four (a : Nat) : powNat a 4 = powNat a 2 * powNat a 2 := by
  rw [show (4 : Nat) = Nat.succ 3 from rfl, powNat_succ, powNat_three, powNat_two]
  simp [Nat.mul_left_comm, Nat.mul_comm]

theorem list_nil_length {α : Type} : (@List.nil α).length = 0 := rfl

theorem list_length_singleton {α : Type} (x : α) : List.length [x] = 1 := rfl

theorem list_append_nil {α : Type} (xs : List α) : xs ++ [] = xs := List.append_nil xs

theorem list_length_append {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp [List.length]
  | cons x xs ih =>
    calc
      (List.cons x xs ++ ys).length = (x :: (xs ++ ys)).length := rfl
      _ = Nat.succ (xs ++ ys).length := rfl
      _ = Nat.succ (xs.length + ys.length) := by rw [ih]
      _ = Nat.succ xs.length + ys.length := (Nat.succ_add xs.length ys.length).symm
      _ = (List.cons x xs).length + ys.length := rfl

theorem list_length_map {α β : Type} (f : α → β) (xs : List α) :
    (List.map f xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.length, ih]

/-- Marker that the list/Nat helper module is linked. -/
theorem gnosisMathListNatLinked : True := trivial

end GnosisMath
