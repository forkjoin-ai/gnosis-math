import Init
import Gnosis.DoorPaysAboveCrossover

/-
  ValueDoorStoplight.lean
  =======================

  Smashing two gnosis ideas into one: the VALUE-DOOR (soundness — check the Value
  to eliminate falsehood) and the STOPLIGHT (scheduling — `gnosis-antiqueue`'s
  red/green admission over `gnosis-frf`). They are the same gate seen from two
  sides, and `gnosis-frf`'s `serial_cutoff` already runs the fused version in
  production (below the cutoff, dispatch costs more than the work — stay serial).

  The fusion: make the light's COLOR the value-door's crossover verdict
  (`DoorPaysAboveCrossover`). Per measured recompute cost `r` and gate cost `g`:

    · RED    — `r ≤ g`: below the crossover, the door costs more than the room.
               Just recompute. (The P-regime; the FOIL "NOT EARNED" 0.84×;
               `gnosis-frf` `total < serial_cutoff()` → serial.)
    · GREEN  — `g < r`: above the crossover, the door pays — verify cheaply, skip
               the expensive search. (The NP-regime.)
    · YELLOW — recompute cost NOT yet measured: PROBE and learn. This is the
               state FOIL's Reynolds EMA and FRF's hardcoded `16` both LACK as an
               explicit phase — the adaptive third light.

  value-door = soundness (which branch is true); stoplight = economics (whether
  checking it is worth the gate). GREEN proves the door pays; RED proves it loses;
  YELLOW says measure. The colour is `decide`-sound against the crossover law.

  Init + `DoorPaysAboveCrossover`. Zero `sorry`, zero new `axiom`.
-/

namespace ValueDoorStoplight

open DoorPaysAboveCrossover

/-- The three lights — the trit of scheduling. -/
inductive Light
  | red      -- below crossover: door loses, just recompute
  | yellow   -- unmeasured: probe and learn the crossover
  | green    -- above crossover: door pays, verify and skip
  deriving DecidableEq, Repr

/-- The fused gate: colour by the value-door crossover. `none` = recompute cost
    not yet measured (probe); `some r` = measured, compare to the gate cost `g`. -/
def light (measuredRecompute : Option Nat) (g : Nat) : Light :=
  match measuredRecompute with
  | none => Light.yellow
  | some r => if g < r then Light.green else Light.red

/-- **GREEN ⟹ the door pays.** A green light means the measured recompute beats
    the gate, so at one hit the value-door has positive net benefit
    (`crossover_is_verify_search_gap`). Green is earned, not asserted. -/
theorem green_door_pays (r g : Nat) (h : light (some r) g = Light.green) :
    0 < netSaved 1 1 r g 0 := by
  simp only [light] at h
  by_cases hc : g < r
  · exact (crossover_is_verify_search_gap r g).mpr hc
  · rw [if_neg hc] at h; exact absurd h (by decide)

/-- **RED ⟹ the door loses.** A red light means recompute is no costlier than the
    gate, so the value-door is a net loss no matter the hit rate
    (`cheap_recompute_no_benefit`) — exactly the measured FOIL slowdown. -/
theorem red_door_loses (r g : Nat) (h : light (some r) g = Light.red) :
    netSaved 1 1 r g 0 ≤ 0 := by
  simp only [light] at h
  by_cases hc : g < r
  · rw [if_pos hc] at h; exact absurd h (by decide)
  · exact cheap_recompute_no_benefit 1 1 r g 0 (by omega) (by omega)

/-- **YELLOW = unmeasured.** With no measurement the light is yellow: probe, learn
    the crossover, then commit. The adaptive state the static `GNOSIS_FRF_SERIAL_CUTOFF`
    and FOIL's fixed Reynolds threshold do not name. -/
theorem yellow_is_unmeasured (g : Nat) : light none g = Light.yellow := rfl

/-- **The light is total and exclusive** — exactly one of red/yellow/green, the
    clean trit. (Every input maps to a single colour.) -/
theorem light_trichotomy (m : Option Nat) (g : Nat) :
    light m g = Light.red ∨ light m g = Light.yellow ∨ light m g = Light.green := by
  cases m with
  | none => right; left; rfl
  | some r =>
    simp only [light]
    by_cases hc : g < r
    · right; right; rw [if_pos hc]
    · left; rw [if_neg hc]

/-! ## Admission eliminates YELLOW — there is always a cert

  YELLOW (probe) is only for UN-attested cost. In gnosis nothing dispatches
  un-admitted: every operation passes a cert that already carries its cost class.
  So the recompute cost is always `some r` (certified), never `none` — and a
  certified light is never yellow. The probe state is vacuous; the gate is total
  RED/GREEN, decided at admission with no measurement, no estimate risk. That is
  why the cost-aware gate is strictly dominant and need not be opt-in: there is
  always some admission to read the cost from. -/

/-- **A certified cost is never YELLOW.** Admission attests the cost, so the gate
    skips the probe entirely. -/
theorem certified_never_yellow (r g : Nat) : light (some r) g ≠ Light.yellow := by
  simp only [light]
  by_cases hc : g < r
  · rw [if_pos hc]; exact (by decide)
  · rw [if_neg hc]; exact (by decide)

/-- **A certified light is decided: RED or GREEN.** With the cost in hand from the
    cert, the gate is total and probe-free — no third state to resolve. -/
theorem certified_is_red_or_green (r g : Nat) :
    light (some r) g = Light.red ∨ light (some r) g = Light.green := by
  simp only [light]
  by_cases hc : g < r
  · right; rw [if_pos hc]
  · left; rw [if_neg hc]

end ValueDoorStoplight
