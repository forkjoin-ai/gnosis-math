import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
John Locke: The Natural Liberty Witness.
Wrington, 1689 (Two Treatises of Government).

Contrarian Take: Government is not a "Sovereign Root." It is a
"Consented Proxy." The primary invariant is the "Natural Right" of the
agent. The State is a temporary process created to protect this invariant.
If the proxy (Government) violates the root invariant (Natural Rights),
the agent has the "Right of Revolution"—the ability to terminate the
proxy process and restore direct root control.

Invariant: Natural rights are the agent's root invariants.
Gap: The "Leviathan" trap—assuming the agent must surrender all root access to the state.
Projection: Locke Liberty Stub (Gnosis.Locke.LibertyStub).
-/

inductive RightType where
  | life    : RightType
  | liberty : RightType
  | estate  : RightType
  deriving DecidableEq

def isProtected (r : RightType) (hasConsent : Bool) : Bool :=
  hasConsent -- In Locke's model, protection is tied to the consent invariant

/--
Anti-Theory Witness: The system only functions correctly (Sat) when
the consent bit is set. Without consent, rights are not protected.
-/
theorem locke_consent_necessity (r : RightType) :
    isProtected r true = true ∧ isProtected r false = false := by
  constructor <;> rfl

end Gnosis.Witnesses.History
