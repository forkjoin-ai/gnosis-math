import Init
import Gnosis.AeonCycleTwelveShadow
import Gnosis.DiscreteClosedTimelikeStep
import Gnosis.TwelveSlotSixtySixPairsCarrier

namespace Gnosis
namespace GnosisTimeClock

/-!
# GnosisTime clock (**mathematical aeon dial**)

**Carrier.** **`TimePhase := Fin twelve`** with **`tick = cyclicSucc h12`** --- one discrete future step wrapping mod **`twelve`**.
Same modulus as **`Circadian.aeon`** (**`twelve_eq_aeon`** in **`AeonCycleTwelveShadow`**) and as **`TwelveSlot`** in the sixty-six-pair spine.

**Scope.** Peano arithmetic and **`Fin`** periodicity only (**`DiscreteClosedTimelikeStep`**). Biological minute interpretations,
drift identities, and manifold stabilization remain in **`Gnosis.Circadian`** -- import that module separately when you need those certificates.

**Bridges.** **`twelveSlotOfPhase`** is definitionally the identity (**both sides are **`Fin twelve`**). **`phaseOfNatTick`** projects any **`Nat`**
counter into the dial; **`phaseOfNatTick_add_aeon_mul`** records **`ℤ/12ℤ`** stability under adding **`k · aeon`**;
**`phaseOfNatTick_add_minutesPerHour_mul`** packages stacked **`Circadian`** solar hours (**`minutesPerHour`** divides **`aeon`**).

**TypeScript mirror:** **`@a0n/gnosis/gnosis-time`** (`open-source/gnosis/src/gnosis-time/`).
-/

open Gnosis.DiscreteClosedTimelikeStep
open Gnosis.AeonCycleTwelveShadow
open Gnosis.Circadian
open Gnosis.TwelveSlotSixtySixPairsCarrier

/-- One position on the twelve-phase dial (**`Fin twelve`**). -/
abbrev TimePhase : Type :=
  Fin twelve

/-- Single **`+1 (mod twelve)`** tick (**discrete future map**). -/
def tick (t : TimePhase) : TimePhase :=
  cyclicSucc h12 t

/-- Same step as **`AeonCycleTwelveShadow.rot`** (**`cyclicSucc h12`**); alias **`rotateTwelveSlot`** lives in **`TwelveSlotSixtySixPairsCyclicShear`**. -/
theorem tick_apply_eq_rot (t : TimePhase) : tick t = rot t :=
  rfl

/-- **`k`** composed ticks. -/
def tickIterate (k : Nat) (t : TimePhase) : TimePhase :=
  iteratedCyclicSucc h12 k t

theorem tickIterate_val (k : Nat) (t : TimePhase) :
    (tickIterate k t).val = (t.val + k) % twelve :=
  iteratedCyclicSucc_val h12 k t

theorem tick_one_eq (t : TimePhase) : tickIterate 1 t = tick t :=
  iteratedCyclicSucc_one_eq_cyclicSucc h12 t

/-- **`twelve`** ticks close every worldline on the dial. -/
theorem tickIterate_twelve (t : TimePhase) : tickIterate twelve t = t :=
  iteratedCyclicSucc_period h12 t

/-- **`Circadian.aeon`** matches the shadow modulus (**numerical bridge**). -/
theorem aeon_eq_twelve_modulus : aeon = twelve :=
  twelve_eq_aeon

/-- Each stacked solar hour (**`minutesPerHour = primitives · aeon`**) is **`0`** mod **`aeon`** on the dial counter. -/
theorem minutes_per_hour_mod_aeon_zero : minutesPerHour % aeon = 0 := by
  native_decide

/-- Project any **`Nat`** counter to the dial (**drumbeat / coarse phase**). -/
def phaseOfNatTick (m : Nat) : TimePhase :=
  ⟨(m % twelve), Nat.mod_lt _ twelve_pos⟩

theorem phaseOfNatTick_succ (m : Nat) :
    phaseOfNatTick (Nat.succ m) = tick (phaseOfNatTick m) := by
  apply Fin.ext
  simp only [phaseOfNatTick, tick, cyclicSucc]
  rw [Nat.succ_eq_add_one, Nat.add_mod]
  simp [Nat.mod_eq_of_lt (show 1 < twelve by decide)]

/-- **`TwelveSlot`** is the same **`Fin twelve`** carrier (**pairsIJ vertex labels**). -/
abbrev twelveSlotOfPhase : TimePhase → TwelveSlot :=
  id

/-- Adding **`k · aeon`** does not move the dial (**mod **`twelve`** identification with **`aeon`**). -/
theorem phaseOfNatTick_add_aeon_mul (m k : Nat) :
    phaseOfNatTick (m + k * aeon) = phaseOfNatTick m := by
  apply Fin.ext
  simp only [phaseOfNatTick, aeon_eq_twelve_modulus]
  rw [Nat.mul_comm k twelve, Nat.add_mul_mod_self_left]

/-- Adding whole **`Circadian`** solar hours leaves **`phaseOfNatTick`** unchanged (**`minutesPerHour = primitives · aeon`**). -/
theorem phaseOfNatTick_add_minutesPerHour_mul (m h : Nat) :
    phaseOfNatTick (m + h * minutesPerHour) = phaseOfNatTick m := by
  apply Fin.ext
  simp only [phaseOfNatTick]
  rw [show h * minutesPerHour = twelve * (h * primitives) by
      rw [minutesPerHour, aeon_eq_twelve_modulus]
      simp [Nat.mul_comm, Nat.mul_left_comm]]
  rw [Nat.add_mul_mod_self_left]

end GnosisTimeClock
end Gnosis
