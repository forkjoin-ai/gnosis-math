import Init

/-!
# Anomaly Cancellation Closure

Bounded one-generation anomaly-cancellation shell using integer-scaled
left-handed Weyl hypercharges. Values are scaled by `6`, so the standard
one-generation assignments are:

* `qL = 1` for the left quark doublet,
* `uC = -4` for the left-handed anti-up singlet,
* `dC = 2` for the left-handed anti-down singlet,
* `lL = -3` for the left lepton doublet,
* `eC = 6` for the left-handed positron singlet.

The theorem surface is finite arithmetic bookkeeping, not a gauge-theory
derivation.
-/

namespace Gnosis
namespace Closures
namespace AnomalyCancellationClosure

def qLHypercharge6 : Int := 1
def uCHypercharge6 : Int := -4
def dCHypercharge6 : Int := 2
def lLHypercharge6 : Int := -3
def eCHypercharge6 : Int := 6

def cube (n : Int) : Int := n * n * n

/-- The bounded `SU(3)^2 U(1)` anomaly cancels exactly. -/
theorem su3SquaredU1_cancels :
    2 * qLHypercharge6 + uCHypercharge6 + dCHypercharge6 = 0 := by
  native_decide

/-- The bounded `SU(2)^2 U(1)` anomaly cancels exactly. -/
theorem su2SquaredU1_cancels :
    3 * qLHypercharge6 + lLHypercharge6 = 0 := by
  native_decide

/-- The bounded gravitational-`U(1)` anomaly cancels exactly. -/
theorem gravitationalSquaredU1_cancels :
    6 * qLHypercharge6 +
      3 * uCHypercharge6 +
      3 * dCHypercharge6 +
      2 * lLHypercharge6 +
      eCHypercharge6 = 0 := by
  native_decide

/-- The bounded cubic `U(1)` anomaly cancels exactly. -/
theorem cubicU1_cancels :
    6 * cube qLHypercharge6 +
      3 * cube uCHypercharge6 +
      3 * cube dCHypercharge6 +
      2 * cube lLHypercharge6 +
      cube eCHypercharge6 = 0 := by
  native_decide

/-- The bounded one-generation anomaly-cancellation shell closes exactly. -/
theorem anomaly_cancellation_closure :
    (2 * qLHypercharge6 + uCHypercharge6 + dCHypercharge6 = 0) ∧
    (3 * qLHypercharge6 + lLHypercharge6 = 0) ∧
    (6 * qLHypercharge6 +
      3 * uCHypercharge6 +
      3 * dCHypercharge6 +
      2 * lLHypercharge6 +
      eCHypercharge6 = 0) ∧
    (6 * cube qLHypercharge6 +
      3 * cube uCHypercharge6 +
      3 * cube dCHypercharge6 +
      2 * cube lLHypercharge6 +
      cube eCHypercharge6 = 0) := by
  exact ⟨su3SquaredU1_cancels, su2SquaredU1_cancels,
    gravitationalSquaredU1_cancels, cubicU1_cancels⟩

end AnomalyCancellationClosure
end Closures
end Gnosis
