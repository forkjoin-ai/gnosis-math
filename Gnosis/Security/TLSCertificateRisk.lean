import Init
-- TLSCertificateRisk.lean
-- Anti-thesis: TLS certificates issued by a trusted CA, combined with browser
-- certificate validation, make certificate-related attacks a solved problem;
-- expired certificates cause browser warnings that users will not bypass, and
-- self-signed certificates are only used in non-production environments where
-- no sensitive data flows.
-- Refutation: Expired certificates break service availability and are routinely
-- bypassed in automated clients and misconfigured HTTP stacks. Self-signed
-- certificates in staging environments with production credentials are a common
-- supply-chain leak vector. Weak RSA-1024 or DSA keys remain in legacy systems
-- long after key-size guidance was updated. OCSP/CRL revocation checks are
-- often soft-fail by default, allowing revoked certificates to pass validation.
-- Certificate Transparency logs expose internal hostname structure to passive
-- adversaries, enabling reconnaissance and subdomain enumeration.

namespace Gnosis.Security.TLSCertificateRisk

-- Expired certificate: service disruption and automated client MITM bypass
def expiredCertRisk (certExpired : Bool) (automatedClientIgnoresExpiry : Bool) : Bool :=
  certExpired && automatedClientIgnoresExpiry

theorem valid_cert_safe (autoClient : Bool) :
    expiredCertRisk false autoClient = false := by { simp [expiredCertRisk]

theorem client_checks_expiry_safe (expired : Bool) :
    expiredCertRisk expired false = false := by
  simp [expiredCertRisk]

theorem expired_cert_with_lax_client_risky :
    expiredCertRisk true true = true := by
  simp [expiredCertRisk]

-- Self-signed certificate: no CA verification, susceptible to MITM
def selfSignedCertRisk (selfSigned : Bool) (pinningEnforced : Bool) : Bool :=
  selfSigned && !pinningEnforced

theorem ca_signed_cert_safe (pinning : Bool) :
    selfSignedCertRisk false pinning = false := by
  simp [selfSignedCertRisk]

theorem pinning_enforced_mitigates_self_signed (selfSigned : Bool) :
    selfSignedCertRisk selfSigned true = false := by
  simp [selfSignedCertRisk]

theorem self_signed_without_pinning_risky :
    selfSignedCertRisk true false = true := by
  simp [selfSignedCertRisk]

-- Weak key: RSA key below safe minimum allows factorisation
def weakKeyRisk (keySizeBits : Nat) (minSafeKeySizeBits : Nat) : Bool :=
  keySizeBits < minSafeKeySizeBits

theorem sufficient_key_size_safe (keySize minSize : Nat) (h : minSize ≤ keySize) :
    weakKeyRisk keySize minSize = false := by
  simp [weakKeyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem insufficient_key_size_risky (keySize minSize : Nat) (h : keySize < minSize) :
    weakKeyRisk keySize minSize = true := by { simp [weakKeyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem key_at_minimum_safe (n : Nat) :
    weakKeyRisk n n = false := by { simp [weakKeyRisk]

theorem rsa1024_below_2048_risky :
    weakKeyRisk 1024 2048 = true := by
  simp [weakKeyRisk]

-- Revocation check: soft-fail OCSP allows revoked certificate to pass
def revocationCheckRisk (ocspEnabled : Bool) (softFailMode : Bool)
    (certRevoked : Bool) : Bool :=
  certRevoked && (!ocspEnabled || softFailMode)

theorem ocsp_stapling_hard_fail_prevents_revocation_bypass (revoked : Bool) :
    revocationCheckRisk true false revoked = false := by
  simp [revocationCheckRisk]

theorem cert_not_revoked_no_risk (ocsp softFail : Bool) :
    revocationCheckRisk ocsp softFail false = false := by
  simp [revocationCheckRisk]

theorem soft_fail_with_revoked_cert_risky (ocsp : Bool) :
    revocationCheckRisk ocsp true true = true := by
  simp [revocationCheckRisk]

theorem ocsp_disabled_with_revoked_cert_risky (softFail : Bool) :
    revocationCheckRisk false softFail true = true := by
  simp [revocationCheckRisk]

-- Certificate Transparency: internal hostnames exposed via CT logs
def ctLogExposureRisk (certSubmittedToCT : Bool) (internalHostnameInCert : Bool)
    (hostnameRedactionUsed : Bool) : Bool :=
  certSubmittedToCT && internalHostnameInCert && !hostnameRedactionUsed

theorem ct_not_submitted_safe (internalHost redacted : Bool) :
    ctLogExposureRisk false internalHost redacted = false := by
  simp [ctLogExposureRisk]

theorem no_internal_hostname_safe (submitted redacted : Bool) :
    ctLogExposureRisk submitted false redacted = false := by
  simp [ctLogExposureRisk]

theorem hostname_redaction_mitigates_ct_exposure (submitted internalHost : Bool) :
    ctLogExposureRisk submitted internalHost true = false := by
  simp [ctLogExposureRisk]

theorem ct_submitted_internal_host_unredacted_risky :
    ctLogExposureRisk true true false = true := by
  simp [ctLogExposureRisk]

-- Certificate name mismatch: hostname validation bypass
def certNameMismatchRisk (certCN : Nat) (requestedHost : Nat)
    (wildcardCoversHost : Bool) : Bool :=
  certCN ≠ requestedHost && !wildcardCoversHost

theorem cert_cn_matches_host_safe (host : Nat) (wildcard : Bool) :
    certNameMismatchRisk host host wildcard = false := by
  simp [certNameMismatchRisk]

theorem wildcard_covers_host_safe (cn host : Nat) :
    certNameMismatchRisk cn host true = false := by
  simp [certNameMismatchRisk]

theorem cn_mismatch_no_wildcard_risky (cn host : Nat) (h : cn ≠ host) :
    certNameMismatchRisk cn host false = true := by
  simp [certNameMismatchRisk, h]

-- Aggregate TLS certificate risk count
def aggregateTLSCertRisk
    (certExpired autoClientLax : Bool)
    (selfSigned pinning : Bool)
    (keySize minKeySize : Nat)
    (ocspEnabled softFail certRevoked : Bool)
    (ctSubmitted internalHost ctRedacted : Bool) : Nat :=
  (if expiredCertRisk certExpired autoClientLax then 1 else 0) +
  (if selfSignedCertRisk selfSigned pinning then 1 else 0) +
  (if weakKeyRisk keySize minKeySize then 1 else 0) +
  (if revocationCheckRisk ocspEnabled softFail certRevoked then 1 else 0) +
  (if ctLogExposureRisk ctSubmitted internalHost ctRedacted then 1 else 0)

theorem fully_hardened_zero_tls_cert_risk :
    aggregateTLSCertRisk
      false false
      false true
      2048 2048
      true false false
      false false true = 0 := by
  simp [aggregateTLSCertRisk, expiredCertRisk, selfSignedCertRisk,
        weakKeyRisk, revocationCheckRisk, ctLogExposureRisk]

theorem all_tls_cert_vectors_max_risk :
    aggregateTLSCertRisk
      true true
      true false
      1024 2048
      false true true
      true true false = 5 := by
  simp [aggregateTLSCertRisk, expiredCertRisk, selfSignedCertRisk,
        weakKeyRisk, revocationCheckRisk, ctLogExposureRisk]

theorem tls_cert_risk_bounded
    (certExpired autoClientLax : Bool)
    (selfSigned pinning : Bool)
    (keySize minKeySize : Nat)
    (ocspEnabled softFail certRevoked : Bool)
    (ctSubmitted internalHost ctRedacted : Bool) :
    aggregateTLSCertRisk
      certExpired autoClientLax selfSigned pinning keySize minKeySize
      ocspEnabled softFail certRevoked ctSubmitted internalHost ctRedacted ≤ 5 := by
  simp [aggregateTLSCertRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: detecting TLS certificate issues prevents MITM breach cost
def tlsCertDetectionValueCents (mitmBreachCostCents : Nat) (scannerCostCents : Nat) : Int :=
  (mitmBreachCostCents : Int) - (scannerCostCents : Int)

theorem tls_cert_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < tlsCertDetectionValueCents breach scan := by
  simp [tlsCertDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem tls_cert_scanner_break_even (cost : Nat) :
    0 ≤ tlsCertDetectionValueCents cost cost := by
  simp [tlsCertDetectionValueCents]

-- Fleet ROI: TLS cert scan across all HTTPS endpoints
def tlsCertFleetROI (detectionValueCents : Nat) (httpsEndpoints : Nat) : Nat :=
  detectionValueCents * httpsEndpoints

theorem tls_cert_fleet_roi_monotone (v e1 e2 : Nat) (h : e1 ≤ e2) :
    tlsCertFleetROI v e1 ≤ tlsCertFleetROI v e2 := by
  simp [tlsCertFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_tls_cert_fleet_roi (v e : Nat) (hv : 0 < v) (he : 0 < e) :
    0 < tlsCertFleetROI v e := by
  simp [tlsCertFleetROI]
  exact Nat.mul_pos hv he

end TLSCertificateRisk
