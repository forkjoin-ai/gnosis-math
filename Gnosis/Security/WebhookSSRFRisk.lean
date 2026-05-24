import Init
-- WebhookSSRFRisk.lean
-- Anti-thesis: Webhooks are a standard integration pattern where the server
-- makes an HTTP callback to a URL supplied by the client; because the client
-- already controls the destination server, there is no meaningful security
-- boundary being crossed, and the server is merely delivering data the client
-- already has access to.
-- Refutation: Webhook URLs supplied by clients are outbound SSRF vectors when
-- the server does not validate them against an allowlist. Without private-IP
-- range blocking, an attacker can target 169.254.169.254 (cloud metadata),
-- 10.0.0.0/8, 172.16.0.0/12, or 127.0.0.1 to probe internal services.
-- Redirect chains allow bypassing naive URL validation: the initial URL passes
-- allowlist checks but redirects to an internal target. Cloud metadata endpoints
-- (IMDSv1) return IAM credentials without authentication, giving an attacker
-- full cloud control from a single webhook call.

namespace Gnosis.Security.WebhookSSRFRisk

-- Outbound webhook: client-supplied URL not validated, becomes SSRF vector
def webhookURLValidationRisk (webhookURLFromClient : Bool)
    (webhookURLValidated : Bool) : Bool :=
  webhookURLFromClient && !webhookURLValidated

theorem webhook_url_validated_safe (fromClient : Bool) :
    webhookURLValidationRisk fromClient true = false := by { simp [webhookURLValidationRisk]

theorem webhook_url_not_from_client_safe (validated : Bool) :
    webhookURLValidationRisk false validated = false := by
  simp [webhookURLValidationRisk]

theorem client_webhook_url_unvalidated_risky :
    webhookURLValidationRisk true false = true := by
  simp [webhookURLValidationRisk]

-- Private IP range: webhook targets internal network range
def privateIPRangeRisk (privateIPBlocked : Bool) (urlResolvesToPrivateIP : Bool) : Bool :=
  !privateIPBlocked && urlResolvesToPrivateIP

theorem private_ip_blocked_safe (resolvesPrivate : Bool) :
    privateIPRangeRisk true resolvesPrivate = false := by
  simp [privateIPRangeRisk]

theorem url_resolves_to_public_ip_safe (blocked : Bool) :
    privateIPRangeRisk blocked false = false := by
  simp [privateIPRangeRisk]

theorem unblocked_private_ip_resolution_risky :
    privateIPRangeRisk false true = true := by
  simp [privateIPRangeRisk]

-- Redirect chain: initial URL passes validation then redirects to internal target
def redirectChainBypassRisk (redirectsFollowed : Bool)
    (redirectDestinationValidated : Bool) : Bool :=
  redirectsFollowed && !redirectDestinationValidated

theorem redirect_destination_validated_safe (follows : Bool) :
    redirectChainBypassRisk follows true = false := by
  simp [redirectChainBypassRisk]

theorem no_redirects_followed_safe (destValidated : Bool) :
    redirectChainBypassRisk false destValidated = false := by
  simp [redirectChainBypassRisk]

theorem redirect_followed_dest_unvalidated_risky :
    redirectChainBypassRisk true false = true := by
  simp [redirectChainBypassRisk]

-- Cloud metadata: IMDSv1 accessible from webhook callback context
def cloudMetadataSSRFRisk (imdsv1Enabled : Bool) (webhookCanReachIMDS : Bool)
    (imdsv2TokenRequired : Bool) : Bool :=
  imdsv1Enabled && webhookCanReachIMDS && !imdsv2TokenRequired

theorem imdsv2_required_prevents_metadata_ssrf (enabled reachable : Bool) :
    cloudMetadataSSRFRisk enabled reachable true = false := by
  simp [cloudMetadataSSRFRisk]

theorem imdsv1_disabled_safe (reachable tokenRequired : Bool) :
    cloudMetadataSSRFRisk false reachable tokenRequired = false := by
  simp [cloudMetadataSSRFRisk]

theorem imds_unreachable_safe (enabled tokenRequired : Bool) :
    cloudMetadataSSRFRisk enabled false tokenRequired = false := by
  simp [cloudMetadataSSRFRisk]

theorem imdsv1_enabled_reachable_no_token_requirement_risky :
    cloudMetadataSSRFRisk true true false = true := by
  simp [cloudMetadataSSRFRisk]

-- DNS rebinding via webhook: DNS TTL allows rebinding to private IP after validation
def webhookDNSRebindRisk (dnsRebindingPossible : Bool)
    (ipRevalidatedBeforeRequest : Bool) : Bool :=
  dnsRebindingPossible && !ipRevalidatedBeforeRequest

theorem ip_revalidated_before_each_request_safe (rebinding : Bool) :
    webhookDNSRebindRisk rebinding true = false := by
  simp [webhookDNSRebindRisk]

theorem dns_rebinding_not_possible_safe (revalidated : Bool) :
    webhookDNSRebindRisk false revalidated = false := by
  simp [webhookDNSRebindRisk]

theorem dns_rebinding_without_revalidation_risky :
    webhookDNSRebindRisk true false = true := by
  simp [webhookDNSRebindRisk]

-- Aggregate webhook SSRF risk count
def aggregateWebhookSSRFRisk
    (urlFromClient urlValidated : Bool)
    (privateIPBlocked resolvesPrivate : Bool)
    (redirectsFollowed redirectDestValidated : Bool)
    (imdsv1Enabled webhookReachesIMDS imdsv2Required : Bool)
    (dnsRebinding ipRevalidated : Bool) : Nat :=
  (if webhookURLValidationRisk urlFromClient urlValidated then 1 else 0) +
  (if privateIPRangeRisk privateIPBlocked resolvesPrivate then 1 else 0) +
  (if redirectChainBypassRisk redirectsFollowed redirectDestValidated then 1 else 0) +
  (if cloudMetadataSSRFRisk imdsv1Enabled webhookReachesIMDS imdsv2Required then 1 else 0) +
  (if webhookDNSRebindRisk dnsRebinding ipRevalidated then 1 else 0)

theorem fully_hardened_zero_webhook_ssrf_risk :
    aggregateWebhookSSRFRisk
      true true
      true false
      false true
      false false true
      false true = 0 := by
  simp [aggregateWebhookSSRFRisk, webhookURLValidationRisk, privateIPRangeRisk,
        redirectChainBypassRisk, cloudMetadataSSRFRisk, webhookDNSRebindRisk]

theorem all_webhook_ssrf_vectors_max_risk :
    aggregateWebhookSSRFRisk
      true false
      false true
      true false
      true true false
      true false = 5 := by
  simp [aggregateWebhookSSRFRisk, webhookURLValidationRisk, privateIPRangeRisk,
        redirectChainBypassRisk, cloudMetadataSSRFRisk, webhookDNSRebindRisk]

theorem webhook_ssrf_risk_bounded
    (urlFromClient urlValidated : Bool)
    (privateIPBlocked resolvesPrivate : Bool)
    (redirectsFollowed redirectDestValidated : Bool)
    (imdsv1Enabled webhookReachesIMDS imdsv2Required : Bool)
    (dnsRebinding ipRevalidated : Bool) :
    aggregateWebhookSSRFRisk
      urlFromClient urlValidated privateIPBlocked resolvesPrivate
      redirectsFollowed redirectDestValidated imdsv1Enabled webhookReachesIMDS imdsv2Required
      dnsRebinding ipRevalidated ≤ 5 := by
  simp [aggregateWebhookSSRFRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: webhook SSRF detection prevents internal network breach
def webhookSSRFDetectionValueCents (internalBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (internalBreachCostCents : Int) - (scannerCostCents : Int)

theorem webhook_ssrf_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < webhookSSRFDetectionValueCents breach scan := by
  simp [webhookSSRFDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem webhook_ssrf_scanner_break_even (cost : Nat) :
    0 ≤ webhookSSRFDetectionValueCents cost cost := by
  simp [webhookSSRFDetectionValueCents]

-- Fleet ROI: webhook SSRF scan across all webhook-enabled services
def webhookSSRFFleetROI (detectionValueCents : Nat) (webhookServices : Nat) : Nat :=
  detectionValueCents * webhookServices

theorem webhook_ssrf_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    webhookSSRFFleetROI v s1 ≤ webhookSSRFFleetROI v s2 := by
  simp [webhookSSRFFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_webhook_ssrf_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < webhookSSRFFleetROI v s := by
  simp [webhookSSRFFleetROI]
  exact Nat.mul_pos hv hs

end WebhookSSRFRisk
