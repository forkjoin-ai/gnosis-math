import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
William Herschel: The Temporal Depth Witness.
Slough, 1780s.

Contrarian Take: The telescope is not just a tool for seeing further in
space. It is a "Time Machine" that maps the history of the universe.
Herschel realized that because light has a finite velocity, looking at
distant stars is a `read` operation on a past state of the kernel.
The "Deep Sky" is a series of stacked temporal frames. The telescope
decouples the observer from the "Simultaneity Illusion."

Invariant: Light-time distance is a temporal mapping.
Gap: The "Now" trap—assuming everything we see in the sky exists in the same current state.
Projection: Herschel Deep Sky Stub (Gnosis.Herschel.DeepSkyStub).
-/

def lightVelocity : Nat := 1 -- Abstract unit

def timeOfStateObservation (distance : Nat) (currentClock : Nat) : Int :=
  (currentClock : Int) - (distance : Int)

/--
Anti-Theory Witness: Distant objects represent older states of the system.
Space is a temporal buffer.
-/
theorem herschel_temporal_depth (d1 d2 : Nat) (clock : Nat) (h : d1 < d2) :
    timeOfStateObservation d2 clock < timeOfStateObservation d1 clock := by
  unfold timeOfStateObservation
  exact Int.sub_lt_sub_left (Int.ofNat_lt.mpr h) (Int.ofNat clock)

end Gnosis.Witnesses.History
