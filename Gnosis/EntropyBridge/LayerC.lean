import Init

/-!
# EntropyBridge Layer C

Policy anchor for physical / hardware entropy claims.

Layer C is the firewall for world-facing hypotheses: lab reports, hardware
health tests, min-entropy estimates, implementation alignment, and deployment
certificates. This module does not assert physical randomness. It only records
the finite status vocabulary used by downstream modules to state conditional
claims honestly.

See `Gnosis/EntropyBridge/README.md`.

Zero `sorry`, zero new `axiom`, no Mathlib.
-/

namespace Gnosis
namespace EntropyBridge
namespace LayerC

inductive EntropyClaimStatus where
  | measured
  | certified
  | assumed
  | rejected
  deriving DecidableEq, Repr

def statusAdmitted : EntropyClaimStatus → Bool
  | .measured => true
  | .certified => true
  | .assumed => true
  | .rejected => false

structure EntropyCertificate where
  status : EntropyClaimStatus
  minEntropyBits : Nat
  healthTestsPassed : Bool
  deriving Repr

def certificateAdmitted (certificate : EntropyCertificate) : Bool :=
  statusAdmitted certificate.status && certificate.healthTestsPassed

def measuredPassingCertificate (bits : Nat) : EntropyCertificate :=
  { status := .measured
    minEntropyBits := bits
    healthTestsPassed := true }

def rejectedCertificate (bits : Nat) : EntropyCertificate :=
  { status := .rejected
    minEntropyBits := bits
    healthTestsPassed := false }

theorem measured_passing_certificate_admitted (bits : Nat) :
    certificateAdmitted (measuredPassingCertificate bits) = true := by
  rfl

theorem rejected_certificate_not_admitted (bits : Nat) :
    certificateAdmitted (rejectedCertificate bits) = false := by
  rfl

theorem rejected_status_not_admitted :
    statusAdmitted EntropyClaimStatus.rejected = false := by
  rfl

theorem admitted_certificate_has_passing_health_tests
    (certificate : EntropyCertificate)
    (hadmitted : certificateAdmitted certificate = true) :
    certificate.healthTestsPassed = true := by
  cases certificate with
  | mk status bits healthTestsPassed =>
      cases status <;> cases healthTestsPassed <;> cases hadmitted <;> rfl

end LayerC
end EntropyBridge
end Gnosis
