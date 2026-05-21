import Gnosis.SocialDynamicsHooke

/-
  SocialDynamicsResonance.lean
  ============================

  Rustic Church finite resonance witness for `SocialDynamicsHooke`:
  an external drive aligned with the period-6 undamped orbit
  accumulates more displacement-plus-velocity residue over one closed
  orbit than period-5 or period-7 comparison drives.

  Init-only through `Gnosis.SocialDynamicsHooke`; zero `sorry`, zero
  new `axiom`, no Mathlib, no `omega`, and no `simp`.
-/

namespace SocialDynamicsResonance

open SocialDynamicsHooke

def absInt : Int → Nat
  | Int.ofNat n => n
  | Int.negSucc n => n + 1

def drivenStep (drive : Nat → Int) (t : Nat) (s : SocialMomentumState) :
    SocialMomentumState :=
  let v' := s.vel + hookeForce s + drive t
  { pos := s.pos + v', vel := v' }

def drivenIterate (drive : Nat → Int) : Nat → Nat → SocialMomentumState → SocialMomentumState
  | 0,     _t, s => s
  | n + 1, t,  s => drivenIterate drive n (t + 1) (drivenStep drive t s)

def periodSixDrive : Nat → Int
  | 0 => 1 | 1 => 1 | 2 => 0 | 3 => -1 | 4 => -1 | _ => 0

def periodFiveDrive : Nat → Int
  | 0 => 1 | 1 => 0 | 2 => -1 | 3 => 0 | _ => 0

def periodSevenDrive : Nat → Int
  | 0 => 1 | 1 => 0 | 2 => 0 | 3 => -1 | 4 => 0 | 5 => 0 | _ => 0

def displacementAfter (drive : Nat → Int) (n : Nat) : Nat :=
  absInt ((drivenIterate drive n 0 initialNashState).pos - initialNashState.pos)

def velocityAfter (drive : Nat → Int) (n : Nat) : Nat :=
  absInt ((drivenIterate drive n 0 initialNashState).vel - initialNashState.vel)

def resonanceScore (drive : Nat → Int) (n : Nat) : Nat :=
  displacementAfter drive n + velocityAfter drive n

theorem period_six_drive_accumulates_after_six :
    resonanceScore periodSixDrive 6 = 4 := by
  native_decide

theorem period_five_drive_score_after_six :
    resonanceScore periodFiveDrive 6 = 3 := by
  native_decide

theorem period_seven_drive_score_after_six :
    resonanceScore periodSevenDrive 6 = 2 := by
  native_decide

theorem period_six_drive_beats_period_five :
    resonanceScore periodFiveDrive 6 < resonanceScore periodSixDrive 6 := by
  native_decide

theorem period_six_drive_beats_period_seven :
    resonanceScore periodSevenDrive 6 < resonanceScore periodSixDrive 6 := by
  native_decide

theorem finite_resonance_witness :
    resonanceScore periodSixDrive 6 = 4 ∧
    resonanceScore periodFiveDrive 6 = 3 ∧
    resonanceScore periodSevenDrive 6 = 2 ∧
    resonanceScore periodFiveDrive 6 < resonanceScore periodSixDrive 6 ∧
    resonanceScore periodSevenDrive 6 < resonanceScore periodSixDrive 6 :=
  ⟨period_six_drive_accumulates_after_six,
    period_five_drive_score_after_six,
    period_seven_drive_score_after_six,
    period_six_drive_beats_period_five,
    period_six_drive_beats_period_seven⟩

/-! ## Next exploration

The finite resonance witness is closed at the Rustic Church level.
Further extensions should remain finite and Init-only.
-/

end SocialDynamicsResonance
