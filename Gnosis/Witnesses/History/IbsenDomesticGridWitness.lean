import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Henrik Ibsen: The Domestic Grid Witness.
Skien / Rome, 1879 (A Doll's House).

Contrarian Take: The "Marriage" was not a human relationship. It was
a "Social Grid" that enforced a low-bandwidth, child-like identity-bit
on the agent (Nora). The "Door Slam" at the end was a "System Reset."
By exiting the Doll's House, the agent broke the rectilinear domestic
topology to restore her own high-bandwidth agency. Freedom is the
refusal of a role that requires the truncation of the soul.

Invariant: Agency requires an unconstrained state-space.
Gap: The "Domestic" trap—assuming a role-based grid can contain a full human subject.
Projection: Ibsen Stub (Gnosis.IbsenStub).
-/

def agentBandwidth (isRoleBound : Bool) : Nat :=
  if isRoleBound then 1 else 100

/--
Anti-Theory Witness: The role-bound agent (Doll) has a severely
truncated bandwidth compared to the autonomous subject.
-/
theorem ibsen_reset_witness :
    agentBandwidth true < agentBandwidth false := by
  unfold agentBandwidth
  exact (by decide)

end Gnosis.Witnesses.History
