/-!
# Picolorenzo Julian-Year Algebra

Init-only arithmetic companion for the Earth chronometry conversion.

The executable TypeScript computes
`years * (365.25 * 86400) / (π * 86400)`, so the formal content preserved
here is the exact cancellation shape: the seconds-per-day factor is common
to both the Julian-year numerator and the picolorenzo denominator.
-/

namespace PlanetaryHomologySandbox

/-- One day in SI seconds. -/
def secondsPerDay : Nat := 86400

/-- One Julian year in microdays: `365.25 * 1_000_000`. -/
def julianYearMicrodays : Nat := 365250000

/-- One picolorenzo in microdays, using the repository's integer π-day scale. -/
def picolorenzoMicrodays : Nat := 3141593

/-- Julian-year duration expressed in microday-seconds. -/
def julianYearSecondMicrodays : Nat :=
  julianYearMicrodays * secondsPerDay

/-- Picolorenzo duration expressed in microday-seconds. -/
def picolorenzoSecondMicrodays : Nat :=
  picolorenzoMicrodays * secondsPerDay

/--
Cross-multiplied form of the executable identity
`y * julianYearSeconds / picolorenzoSeconds = y * 365.25 / π`.

Using integer microdays, both sides share the same `secondsPerDay` factor.
-/
theorem julianYears_picolorenzo_seconds_cancel (y : Nat) :
    y * julianYearSecondMicrodays * picolorenzoMicrodays =
      y * julianYearMicrodays * picolorenzoSecondMicrodays := by
  unfold julianYearSecondMicrodays picolorenzoSecondMicrodays
  simp [Nat.mul_comm, Nat.mul_left_comm]

/-- The one-year numerator is exactly the Julian-year microday constant. -/
theorem one_julian_year_microdays :
    1 * julianYearMicrodays = 365250000 := rfl

/-- The one-picolorenzo denominator is exactly the π-day microday constant. -/
theorem one_picolorenzo_microdays :
    picolorenzoMicrodays = 3141593 := rfl

end PlanetaryHomologySandbox
