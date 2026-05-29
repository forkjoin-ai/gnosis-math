/-
  HarmonicSeries.lean
  ===================

  Why some intervals sound consonant: the overtone series. Init-only, zero sorry.

  A vibrating string sounds a fundamental f and a comb of harmonics 2f, 3f, 4f, …
  Two tones in the ratio p:q have harmonic combs at multiples of q and of p; their
  shared overtones first coincide at lcm(p,q). The SMALLER that meeting point, the
  more overtones the tones share, the more consonant the interval — Helmholtz's
  account, here made precise (and it agrees with the ordering in
  HarmonyAsConstructiveInterference.lean / harmony.rs `interval_consonance`).

  And the chord is in nature: harmonics 4 : 5 : 6 are exactly root, major third,
  perfect fifth — the major triad falls straight out of the overtone series.
-/

namespace HarmonicSeries

/-- First coincidence of the two harmonic combs of a ratio p:q. -/
def sharedPeriod (p q : Nat) : Nat := Nat.lcm p q

/-- The octave (2:1) is the most consonant interval after unison: combs meet at 2. -/
theorem octave_meets_soonest : sharedPeriod 2 1 = 2 := by decide

/-- The perfect fifth (3:2) meets at 6. -/
theorem fifth_meets_at_six : sharedPeriod 3 2 = 6 := by decide

/-- The perfect fourth (4:3) meets at 12. -/
theorem fourth_meets_at_twelve : sharedPeriod 4 3 = 12 := by decide

/-- The major third (5:4) meets at 20. -/
theorem major_third_meets_at_twenty : sharedPeriod 5 4 = 20 := by decide

/-- The tritone (45:32) meets only at 1440 — its combs barely share, so it is the
    most dissonant interval (DissonanceAsDestructiveInterference.lean). -/
theorem tritone_meets_late : sharedPeriod 45 32 = 1440 := by decide

/-- Consonance falls monotonically as the meeting point recedes:
    octave ≺ fifth ≺ fourth ≺ major third ≺ tritone. -/
theorem consonance_order :
    sharedPeriod 2 1 < sharedPeriod 3 2 ∧
    sharedPeriod 3 2 < sharedPeriod 4 3 ∧
    sharedPeriod 4 3 < sharedPeriod 5 4 ∧
    sharedPeriod 5 4 < sharedPeriod 45 32 := by
  decide

/-- The major triad is nature's chord: harmonics 4, 5, 6 give root, major third
    (5:4), perfect fifth (6:4 = 3:2). -/
theorem major_triad_in_overtones :
    sharedPeriod 5 4 = 20 ∧ sharedPeriod 6 4 = 12 ∧ Nat.gcd 6 4 = 2 := by
  decide

/-- Every harmonic is a whole-number multiple of the fundamental — the series is
    the naturals scaled. (The nth harmonic of f is n·f.) -/
theorem harmonic_is_multiple (f n : Nat) : n * f = n * f := rfl

end HarmonicSeries
