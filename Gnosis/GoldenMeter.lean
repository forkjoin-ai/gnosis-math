/-
  GoldenMeter.lean
  ================

  The phi-cut bar: a 13-beat measure split at the golden ratio. Init-only, zero sorry.

  Thirteen beats divide as player(5) + sky(8) = 13 — three consecutive Fibonacci
  numbers, so the cut 8/13 is the closest rational to 1/φ at this scale. Strong
  beats land on the Fibonacci positions {0, 5, 8} (matching MarkovSong / prosody.rs
  `is_strong_beat`), and the bar subdivides Fibonacci-style all the way down:
  13 = 8+5, 8 = 5+3, 5 = 3+2. The golden cut's irrationality shows up as Cassini's
  identity: 8·8 and 5·13 differ by exactly one (the φ-approximation can never be
  perfect — the meter swerves).
-/

namespace GoldenMeter

def barBeats : Nat := 13
def playerBars : Nat := 5
def skyBars : Nat := 8

/-- Player + sky tile the bar: 5 + 8 = 13. -/
theorem bar_is_player_plus_sky : playerBars + skyBars = barBeats := by decide

/-- The three are consecutive Fibonacci numbers (F5,F6,F7 = 5,8,13). -/
theorem consecutive_fibonacci : playerBars + skyBars = barBeats ∧ 3 + playerBars = skyBars := by decide

/-- Strong beats at the Fibonacci positions {0, 5, 8} of the 13-beat bar. -/
def isStrongBeat (b : Nat) : Bool := match b % barBeats with
  | 0 => true
  | 5 => true
  | 8 => true
  | _ => false

/-- The strong beats are exactly 0, 5, 8 (matches prosody.rs / MarkovSong). -/
theorem strong_beats_are_fibonacci :
    isStrongBeat 0 = true ∧ isStrongBeat 5 = true ∧ isStrongBeat 8 = true ∧
    isStrongBeat 1 = false ∧ isStrongBeat 7 = false ∧ isStrongBeat 12 = false := by decide

/-- Gaps between consecutive strong beats are 5, 3, 5 (cyclically) — Fibonacci
    again, the larger φ-cut first. -/
theorem strong_beat_gaps :
    (5 - 0, 8 - 5, barBeats - 8 + 0) = (5, 3, 5) := by decide

/-- Cassini's identity at the φ-cut: 8·8 and 5·13 differ by one — the golden ratio
    is irrational, so the rational cut always swerves by a single unit. -/
theorem cassini_phi_cut : skyBars * skyBars + 1 = playerBars * barBeats := by decide

/-- Fibonacci subdivision: the bar nests 13 = 8+5, 8 = 5+3, 5 = 3+2 — the meter is
    self-similar down to the clinamen pair (2 = 1+1). -/
theorem fibonacci_subdivision :
    (8 + 5 = 13) ∧ (5 + 3 = 8) ∧ (3 + 2 = 5) ∧ (1 + 1 = 2) := by decide

end GoldenMeter
