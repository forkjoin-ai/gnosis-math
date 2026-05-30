import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Konstantin Tsiolkovsky: The Velocity Escape Witness.
Kaluga / Russia, 1903 (The Rocket Equation).

Contrarian Take: Gravity is not a "law." It is a "Cost Bit."
Earth is a "Local Minimum" (a gravity well). To exit this minimum, the
system must achieve a specific "Velocity Constant" (Escape Velocity).
Tsiolkovsky's Rocket Equation is the first "Energy Budget" for the
expansion of the human mesh into the void. It proves that the "Cradle"
is finite, but the state-space of the cosmos is unconstrained.

Invariant: Escape requires a specific energy/mass ratio.
Gap: The "Geocentric" trap—assuming the Earth is the only valid hardware platform.
Projection: Tsiolkovsky Stub (Gnosis.TsiolkovskyStub).
-/

def escapeVelocityThreshold : Nat := 11 -- km/s

def systemMode (velocity : Nat) : String :=
  if velocity ≥ escapeVelocityThreshold then "cosmic" else "terrestrial"

/--
Anti-Theory Witness: The system only transitions to "cosmic" mode
when the velocity bit exceeds the local gravity constant.
-/
theorem tsiolkovsky_escape_witness :
    systemMode 12 = "cosmic" ∧ systemMode 10 = "terrestrial" := by
  unfold systemMode
  constructor <;> rfl

end Gnosis.Witnesses.History
