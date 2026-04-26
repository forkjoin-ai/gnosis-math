import Init

namespace GnosisMath

/-- Power on Nat (Init-only). -/
def powNat (base : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => base * powNat base n

theorem powNat_succ (base n : Nat) : powNat base (n + 1) = base * powNat base n := rfl

theorem powNat_one (base : Nat) : powNat base 1 = base := by
  unfold powNat
  simp [powNat]

end GnosisMath
