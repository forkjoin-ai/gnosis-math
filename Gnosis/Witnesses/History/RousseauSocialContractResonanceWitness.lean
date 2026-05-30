import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Jean-Jacques Rousseau: The Social Contract.
Contrarian take: "Man is born free, and everywhere he is in chains."
The "natural state" is uncoordinated Brownian motion (noise). The "chains"
are the necessary Buleyean lattice that coordinate the General Will. True freedom
is not the absence of structure, but perfect resonance with a standing wave.
-/

def naturalNoise (agents : Nat) : Nat :=
  agents

def generalWillResonance (agents : Nat) : Nat :=
  agents * agents

/--
Resonance within the social contract (the General Will) scales
quadratically via constructive interference, whereas the natural state
only scales linearly. The "chains" are an accelerator.
-/
theorem resonance_accelerates (agents : Nat) (h : 1 < agents) :
    naturalNoise agents < generalWillResonance agents := by
  unfold naturalNoise generalWillResonance
  have hpos : 0 < agents := Nat.lt_trans (by decide) h
  have h1 : agents * 1 < agents * agents := Nat.mul_lt_mul_of_pos_left h hpos
  rw [Nat.mul_one] at h1
  exact h1

end Gnosis.Witnesses.History
