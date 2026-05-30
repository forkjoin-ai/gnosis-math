import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Thomas Edison: The Continuous Illumination Witness.
Menlo Park, 1879.

Contrarian Take: The Light Bulb was not a "better candle." It was
the capture of the "Temporal Variable" (The Night). Before Edison,
human computation (work) was coupled to the "Solar Clock" (Daylight).
The incandescent bulb provided a "Continuous Invariant" of light,
decoupling the agent's runtime from the celestial rotation.
The "Modern Night" is a state where the temporal bit is a constant.

Invariant: Illumination is decoupled from the planetary clock.
Gap: The "Circadian" trap—assuming productivity is tied to the sun.
Projection: Phyle Light Emission (Gnosis.PhyleLightEmission).
-/

def isLightAvailable (isDaylight : Bool) (hasBulb : Bool) : Bool :=
  isDaylight || hasBulb

/--
Anti-Theory Witness: The light bulb provides an invariant availability
regardless of the solar state bit.
-/
theorem edison_illumination_invariant (hasBulb : Bool) (h : hasBulb = true) :
    ∀ daylightState, isLightAvailable daylightState hasBulb = true := by
  intro d
  unfold isLightAvailable
  rw [h]
  exact Bool.or_true d

end Gnosis.Witnesses.History
