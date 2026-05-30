import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Genghis Khan: The Nomadic Constant Witness.
Karakorum / The Great Steppe, 1206.

Contrarian Take: The Mongol Empire was not a "State" in the sedentary
sense. It was a "High-Velocity Invariant." While sedentary empires
relied on static defensive grids (walls), the Mongols established a
dynamic constant via the speed of the horse (The Yam). Sovereignty was
not a property of the land, but a property of the communication bandwidth.
The nomadic variable produced the largest land constant in history.

Invariant: Sovereignty is proportional to communication velocity.
Gap: The "Static Defense" trap—assuming walls are more stable than speed.
Projection: Contrarian Chaos is Order (Gnosis.Contrarian.ContrarianChaosIsOrder).
-/

def sedentaryBandwidth : Nat := 1
def nomadicBandwidth   : Nat := 10

def empireStability (bandwidth : Nat) : Nat :=
  bandwidth * 100

/--
Anti-Theory Witness: The nomadic empire achieves a higher stability
(state-space coverage) than the sedentary empire due to higher bandwidth.
-/
theorem nomadic_stability_dominance :
    empireStability sedentaryBandwidth < empireStability nomadicBandwidth := by
  unfold empireStability nomadicBandwidth sedentaryBandwidth
  exact (by decide)

end Gnosis.Witnesses.History
