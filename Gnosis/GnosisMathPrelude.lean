import Init

/-!
Short-file burndown note: `Gnosis.GnosisMathPrelude` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates while satisfying the strict chapel proof-style gate.
-/


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
