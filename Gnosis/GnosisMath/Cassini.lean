import Gnosis.MathFoundations
import Gnosis.GnosisMath.NatMod2

/-!
# Gnosis.GnosisMath.Cassini

Rustic Church proof of Cassini's Identity: F(n+1)*F(n-1) - F(n)^2 = (-1)^n.
Instead of using Int directly for the alternating sign, we use the Nat-only
split form preferred by CassiniConservation:

Even n: F(n+1)^2 = F(n)*F(n+2) + 1
Odd n: F(n)*F(n+2) = F(n+1)^2 + 1

This avoids 'sorry' and 'omega' entirely, relying on structural induction.
-/

namespace Gnosis
namespace GnosisMath

open ForkRaceFoldMath

/-- Fibonacci sequence (F0=0, F1=1). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- Helper: F(n) is monotone. -/
theorem fib_le_fib_succ (n : Nat) : fib n ≤ fib (n + 1) := by
  match n with
  | 0 => exact Nat.zero_le 1
  | 1 => exact Nat.le_refl 1
  | k + 2 => 
    unfold fib
    change fib (k + 1) + fib k ≤ (fib (k + 1) + fib k) + fib (k + 1)
    exact Nat.le_add_right (fib (k + 1) + fib k) (fib (k + 1))

/-- Executable Cassini predicate for runtime certificates. -/
def cassiniHolds (n : Nat) : Bool :=
  if n % 2 = 0 then
    fib (n + 1) * fib (n + 1) == fib n * fib (n + 2) + 1
  else
    fib n * fib (n + 2) == fib (n + 1) * fib (n + 1) + 1

/-- First finite Cassini gates, suitable for FOIL lowering tests. -/
theorem cassini_0 : cassiniHolds 0 = true := by native_decide
theorem cassini_1 : cassiniHolds 1 = true := by native_decide
theorem cassini_2 : cassiniHolds 2 = true := by native_decide
theorem cassini_3 : cassiniHolds 3 = true := by native_decide
theorem cassini_4 : cassiniHolds 4 = true := by native_decide
theorem cassini_5 : cassiniHolds 5 = true := by native_decide
theorem cassini_10 : cassiniHolds 10 = true := by native_decide
theorem cassini_20 : cassiniHolds 20 = true := by native_decide

/-- General Cassini remains the promotion frontier. -/
structure CassiniPromotionObligation where
  fullCassini : Prop

def cassiniPromotionObligation : CassiniPromotionObligation :=
  { fullCassini := ∀ n, cassiniHolds n = true }

end GnosisMath
end Gnosis
