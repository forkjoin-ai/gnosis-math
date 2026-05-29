import Init
import Gnosis.DoorPaysAboveCrossover

/-
  AdaptiveStoplight.lean
  ======================

  What we formalize BEFORE we measure: the precise claim the benchmark must
  confirm or kill.

  The fused value-door stoplight (`ValueDoorStoplight`) has a YELLOW probe state
  the static gates lack: it MEASURES the recompute/gate crossover, then commits
  RED (recompute) or GREEN (open the door). The benefit of opening the door over
  the serial baseline is `DoorPaysAboveCrossover.netSaved`. The adaptive policy
  captures that benefit when positive and otherwise recomputes — paying a one-time
  probe cost `probe` to learn which.

  The measurable claims:
    1. `adaptive_floors_loss`   — the adaptive gate NEVER loses more than the
       probe. Its downside is bounded; it cannot suffer the unbounded slowdown.
    2. `adaptive_captures_win`  — when the door's benefit exceeds the probe, the
       adaptive gate still comes out ahead.
    3. `static_door_unbounded_loss` — a STATIC always-open gate (no probe) can lose
       an UNBOUNDED amount (the FRF 5–110× regression, the FOIL 0.84×).

  Together: adaptive ≈ optimal ± probe; static-mis-tuned ≈ arbitrarily bad. The
  benchmark's job is to measure the real `probe` against the real `netSaved` on
  FOIL/FRF workloads — to see whether the bounded-downside trade is earned.

  Init + `DoorPaysAboveCrossover`. Zero `sorry`, zero new `axiom`.
-/

namespace AdaptiveStoplight

open DoorPaysAboveCrossover

/-- Net benefit of the adaptive (YELLOW-probe) gate vs the serial baseline: it
    takes the door's benefit when positive, recomputes (benefit 0) otherwise, and
    pays a one-time `probe` to learn which. -/
def adaptiveBenefit (N h r g setup probe : Nat) : Int :=
  (if 0 < netSaved N h r g setup then netSaved N h r g setup else 0) - probe

/-- **The adaptive gate floors its loss at the probe cost.** No matter the
    workload, it never loses more than the one-time measurement — it cannot
    suffer the unbounded blowup of a mis-tuned static gate. -/
theorem adaptive_floors_loss (N h r g setup probe : Nat) :
    -(probe : Int) ≤ adaptiveBenefit N h r g setup probe := by
  unfold adaptiveBenefit
  by_cases hp : 0 < netSaved N h r g setup
  · rw [if_pos hp]; omega
  · rw [if_neg hp]; omega

/-- **The adaptive gate keeps the win.** When the door's benefit exceeds the
    probe cost, the adaptive gate is net-positive — the YELLOW probe pays for
    itself. -/
theorem adaptive_captures_win (N h r g setup probe : Nat)
    (hwin : (probe : Int) < netSaved N h r g setup) :
    0 < adaptiveBenefit N h r g setup probe := by
  unfold adaptiveBenefit
  have hp : 0 < netSaved N h r g setup := by omega
  rw [if_pos hp]; omega

/-- **A static always-open gate loses unboundedly.** For any loss `D`, there is a
    workload (all misses, `h = 0`, batch `D`) where opening the door costs `D`
    more than serial — the FRF 5–110× regression and the FOIL 0.84×, as law. The
    probe (YELLOW) is precisely what bounds this away. -/
theorem static_door_unbounded_loss (D : Nat) :
    ∃ N h r g setup : Nat, netSaved N h r g setup ≤ -(D : Int) := by
  refine ⟨D, 0, 0, 1, 0, ?_⟩
  unfold netSaved
  omega

/-- The contrast in one line: the adaptive gate's loss is bounded by the probe,
    while the static gate's loss is unbounded. This is the trade the benchmark
    must price. -/
theorem adaptive_bounded_static_unbounded (probe : Nat) :
    (∀ N h r g setup : Nat, -(probe : Int) ≤ adaptiveBenefit N h r g setup probe)
    ∧ (∀ D : Nat, ∃ N h r g setup : Nat, netSaved N h r g setup ≤ -(D : Int)) :=
  ⟨fun N h r g setup => adaptive_floors_loss N h r g setup probe,
   static_door_unbounded_loss⟩

end AdaptiveStoplight
