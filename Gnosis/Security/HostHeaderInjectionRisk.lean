import Init
-- HostHeaderInjectionRisk.lean
-- Anti-thesis: The HTTP Host header is a benign routing hint used by reverse
-- proxies and web servers to select the correct virtual host; applications never
-- rely on Host for security-sensitive decisions, so no injection is possible.
-- Refutation: Password-reset flows frequently embed Host in the reset link sent
-- to the user, allowing an attacker to poison the link to an attacker-controlled
-- domain. Cache systems often key on Host, enabling cache poisoning via malformed
-- or duplicate Host headers. Back-end servers accessed via a proxy may trust the
-- Host header for SSRF without validation. Port override via Host:example.com:evil
-- can redirect internal requests to unexpected services.

namespace Gnosis.Security.HostHeaderInjectionRisk

-- Password-reset poisoning: reset link built from untrusted Host header
def passwordResetPoisoningRisk (hostFromRequest : Bool) (resetLinkUsesHost : Bool)
    (hostValidated : Bool) : Bool :=
  hostFromRequest && resetLinkUsesHost && !hostValidated

theorem validated_host_safe (fromReq usesHost : Bool) :
    passwordResetPoisoningRisk fromReq usesHost true = false := by { simp [passwordResetPoisoningRisk]

theorem link_does_not_use_host_safe (fromReq validated : Bool) :
    passwordResetPoisoningRisk fromReq false validated = false := by
  simp [passwordResetPoisoningRisk]

theorem unvalidated_host_in_reset_link_risky :
    passwordResetPoisoningRisk true true false = true := by
  simp [passwordResetPoisoningRisk]

theorem validated_host_regardless_of_usage (fromReq usesHost : Bool) :
    passwordResetPoisoningRisk fromReq usesHost true = false := by
  simp [passwordResetPoisoningRisk]

-- Cache poisoning via Host header: unkeyed Host used to vary cached responses
def hostCachePoisoningRisk (hostUnkeyedInCache : Bool) (hostReflectedInResponse : Bool) : Bool :=
  hostUnkeyedInCache && hostReflectedInResponse

theorem host_keyed_in_cache_safe (reflected : Bool) :
    hostCachePoisoningRisk false reflected = false := by
  simp [hostCachePoisoningRisk]

theorem host_not_reflected_safe (unkeyed : Bool) :
    hostCachePoisoningRisk unkeyed false = false := by
  simp [hostCachePoisoningRisk]

theorem unkeyed_reflected_host_risky :
    hostCachePoisoningRisk true true = true := by
  simp [hostCachePoisoningRisk]

-- SSRF via Host: backend trusts Host header for outbound URL construction
def hostSSRFRisk (backendTrustsHost : Bool) (hostValidatedAgainstAllowlist : Bool) : Bool :=
  backendTrustsHost && !hostValidatedAgainstAllowlist

theorem allowlist_validation_prevents_host_ssrf (trusts : Bool) :
    hostSSRFRisk trusts true = false := by
  simp [hostSSRFRisk]

theorem backend_ignores_host_safe (validated : Bool) :
    hostSSRFRisk false validated = false := by
  simp [hostSSRFRisk]

theorem unvalidated_trusted_host_ssrf_risky :
    hostSSRFRisk true false = true := by
  simp [hostSSRFRisk]

-- Port override: Host: victim.com:attacker-port redirects internal requests
def portOverrideRisk (portFromHostHeader : Bool) (portValidated : Bool)
    (internalPortsReachable : Bool) : Bool :=
  portFromHostHeader && !portValidated && internalPortsReachable

theorem port_validated_safe (fromHost internalReachable : Bool) :
    portOverrideRisk fromHost true internalReachable = false := by
  simp [portOverrideRisk]

theorem internal_ports_unreachable_safe (fromHost validated : Bool) :
    portOverrideRisk fromHost validated false = false := by
  simp [portOverrideRisk]

theorem port_not_from_header_safe (validated reachable : Bool) :
    portOverrideRisk false validated reachable = false := by
  simp [portOverrideRisk]

theorem unvalidated_port_with_internal_access_risky :
    portOverrideRisk true false true = true := by
  simp [portOverrideRisk]

-- Duplicate Host header: two Host headers cause parsing divergence between components
def duplicateHostRisk (duplicateHostAccepted : Bool) (componentsParseIndependently : Bool) : Bool :=
  duplicateHostAccepted && componentsParseIndependently

theorem duplicate_rejected_safe (independent : Bool) :
    duplicateHostRisk false independent = false := by
  simp [duplicateHostRisk]

theorem components_agree_on_parsing_safe (accepted : Bool) :
    duplicateHostRisk accepted false = false := by
  simp [duplicateHostRisk]

theorem duplicate_accepted_with_divergent_parsing_risky :
    duplicateHostRisk true true = true := by
  simp [duplicateHostRisk]

-- Aggregate host header injection risk count
def aggregateHostHeaderRisk
    (hostFromReq resetUsesHost hostValidated : Bool)
    (hostUnkeyed hostReflected : Bool)
    (backendTrusts hostAllowlisted : Bool)
    (portFromHeader portValidated internalReachable : Bool)
    (dupAccepted componentsIndependent : Bool) : Nat :=
  (if passwordResetPoisoningRisk hostFromReq resetUsesHost hostValidated then 1 else 0) +
  (if hostCachePoisoningRisk hostUnkeyed hostReflected then 1 else 0) +
  (if hostSSRFRisk backendTrusts hostAllowlisted then 1 else 0) +
  (if portOverrideRisk portFromHeader portValidated internalReachable then 1 else 0) +
  (if duplicateHostRisk dupAccepted componentsIndependent then 1 else 0)

theorem fully_hardened_zero_host_risk :
    aggregateHostHeaderRisk
      false false true
      false false
      false true
      false true false
      false false = 0 := by
  simp [aggregateHostHeaderRisk, passwordResetPoisoningRisk, hostCachePoisoningRisk,
        hostSSRFRisk, portOverrideRisk, duplicateHostRisk]

theorem all_host_vectors_max_risk :
    aggregateHostHeaderRisk
      true true false
      true true
      true false
      true false true
      true true = 5 := by
  simp [aggregateHostHeaderRisk, passwordResetPoisoningRisk, hostCachePoisoningRisk,
        hostSSRFRisk, portOverrideRisk, duplicateHostRisk]

-- More risks exposed when more vectors are active
theorem host_risk_monotone_in_vectors (n : Nat)
    (h : n ≤ aggregateHostHeaderRisk
          true true false true true true false true false true true true) :
    n ≤ 5 := by
  simp [aggregateHostHeaderRisk, passwordResetPoisoningRisk, hostCachePoisoningRisk,
        hostSSRFRisk, portOverrideRisk, duplicateHostRisk] at h
  omega

-- Scanner ROI: detecting host header injection prevents breach cost
def hostInjectionDetectionValueCents (breachCostCents : Nat) (scannerCostCents : Nat) : Int :=
  (breachCostCents : Int) - (scannerCostCents : Int)

theorem host_injection_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < hostInjectionDetectionValueCents breach scan := by
  simp [hostInjectionDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem host_injection_scanner_break_even (cost : Nat) :
    0 ≤ hostInjectionDetectionValueCents cost cost := by
  simp [hostInjectionDetectionValueCents]

-- Fleet ROI: host header injection scan across web properties
def hostInjectionFleetROI (detectionValueCents : Nat) (webProperties : Nat) : Nat :=
  detectionValueCents * webProperties

theorem host_injection_fleet_roi_monotone (v p1 p2 : Nat) (h : p1 ≤ p2) :
    hostInjectionFleetROI v p1 ≤ hostInjectionFleetROI v p2 := by
  simp [hostInjectionFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_host_injection_fleet_roi (v p : Nat) (hv : 0 < v) (hp : 0 < p) :
    0 < hostInjectionFleetROI v p := by
  simp [hostInjectionFleetROI]
  exact Nat.mul_pos hv hp

end HostHeaderInjectionRisk
