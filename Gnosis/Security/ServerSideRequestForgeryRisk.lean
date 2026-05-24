import Init
-- ServerSideRequestForgeryRisk.lean
-- Anti-thesis: SSRF is only exploitable when an application fetches user-supplied
-- URLs and the server has no egress filtering; properly configured firewalls
-- block outbound connections to internal RFC-1918 addresses, making SSRF
-- a nuisance finding with negligible real-world impact.
-- Refutation: Cloud metadata endpoints (169.254.169.254 for AWS/GCP/Azure) are
-- reachable without internet egress. DNS rebinding converts hostname-validated
-- requests into internal connections. Redirect-following enables bypassing
-- allowlist validation at URL parse time. Blind SSRF via timing or DNS callbacks
-- confirms internal topology even without response body. SSRF has been the
-- initial access vector for major cloud breaches (Capital One, etc.).

namespace Gnosis.Security.ServerSideRequestForgeryRisk

-- Internal network SSRF: fetching RFC-1918 or loopback addresses
def internalNetworkSSRFRisk (egressFilteringEnabled : Bool) (urlValidated : Bool)
    (privateRangeBlocked : Bool) : Bool :=
  !egressFilteringEnabled || (!urlValidated && !privateRangeBlocked)

theorem full_egress_and_validation_safe :
    internalNetworkSSRFRisk true true true = false := by { simp [internalNetworkSSRFRisk]

theorem egress_filter_sufficient (validated blocked : Bool) :
    internalNetworkSSRFRisk true validated blocked = false := by
  simp [internalNetworkSSRFRisk]

theorem no_egress_filter_always_risky (validated blocked : Bool) :
    internalNetworkSSRFRisk false validated blocked = true := by
  simp [internalNetworkSSRFRisk]

theorem no_validation_no_block_risky :
    internalNetworkSSRFRisk true false false = true := by
  simp [internalNetworkSSRFRisk]

-- Cloud metadata SSRF: IMDSv1 endpoint 169.254.169.254 exposes IAM credentials
def cloudMetadataSSRFRisk (imdsv2Required : Bool) (metadataEndpointFiltered : Bool) : Bool :=
  !imdsv2Required && !metadataEndpointFiltered

theorem imdsv2_prevents_metadata_ssrf (filtered : Bool) :
    cloudMetadataSSRFRisk true filtered = false := by
  simp [cloudMetadataSSRFRisk]

theorem filtered_endpoint_safe (imdsv2 : Bool) :
    cloudMetadataSSRFRisk imdsv2 true = false := by
  simp [cloudMetadataSSRFRisk]
  cases imdsv2 <;> simp

theorem imdsv1_unfiltered_metadata_risk :
    cloudMetadataSSRFRisk false false = true := by
  simp [cloudMetadataSSRFRisk]

-- SSRF via redirect: server follows 3xx to internal destination after host check
def redirectSSRFRisk (redirectFollowingEnabled : Bool) (postRedirectValidation : Bool) : Bool :=
  redirectFollowingEnabled && !postRedirectValidation

theorem redirect_disabled_no_ssrf (postVal : Bool) :
    redirectSSRFRisk false postVal = false := by
  simp [redirectSSRFRisk]

theorem post_redirect_validation_safe (followRedirect : Bool) :
    redirectSSRFRisk followRedirect true = false := by
  simp [redirectSSRFRisk]
  cases followRedirect <;> simp

theorem follow_redirect_without_revalidation_risky :
    redirectSSRFRisk true false = true := by
  simp [redirectSSRFRisk]

-- DNS rebinding SSRF: hostname resolves to public IP at check, internal at use
def dnsRebindSSRFRisk (dnsRebindingMitigated : Bool) (ipPinnedAtFetch : Bool) : Bool :=
  !dnsRebindingMitigated && !ipPinnedAtFetch

theorem dns_rebind_mitigated_safe (pinned : Bool) :
    dnsRebindSSRFRisk true pinned = false := by
  simp [dnsRebindSSRFRisk]

theorem ip_pinned_safe (mitigated : Bool) :
    dnsRebindSSRFRisk mitigated true = false := by
  simp [dnsRebindSSRFRisk]
  cases mitigated <;> simp

theorem no_mitigation_no_pin_dns_rebind_risky :
    dnsRebindSSRFRisk false false = true := by
  simp [dnsRebindSSRFRisk]

-- Blind SSRF: no response body but timing/DNS callbacks confirm internal reach
def blindSSRFRisk (dnsCallbackBlocked : Bool) (timingObservable : Bool) : Bool :=
  !dnsCallbackBlocked && timingObservable

theorem dns_callback_blocked_blind_ssrf_limited (timing : Bool) :
    blindSSRFRisk true timing = false := by
  simp [blindSSRFRisk]

theorem no_timing_observable_no_blind_ssrf (blocked : Bool) :
    blindSSRFRisk blocked false = false := by
  simp [blindSSRFRisk]
  cases blocked <;> simp

theorem unblocked_dns_with_timing_observable_blind_ssrf :
    blindSSRFRisk false true = true := by
  simp [blindSSRFRisk]

-- SSRF impact amplifier: IAM credential theft via metadata endpoint
def ssrfImpactAmplifier (metadataExposed : Bool) (iamRoleAttached : Bool)
    (credentialsRotated : Bool) : Nat :=
  if metadataExposed && iamRoleAttached && !credentialsRotated then 3
  else if metadataExposed && iamRoleAttached then 2
  else if metadataExposed then 1
  else 0

theorem no_metadata_zero_amplifier (role rotated : Bool) :
    ssrfImpactAmplifier false role rotated = 0 := by
  simp [ssrfImpactAmplifier]

theorem metadata_exposed_alone_low_amplifier (role rot : Bool) :
    ssrfImpactAmplifier true false rot = 1 := by
  simp [ssrfImpactAmplifier]

theorem metadata_with_iam_unrotated_max_amplifier :
    ssrfImpactAmplifier true true false = 3 := by
  simp [ssrfImpactAmplifier]

theorem metadata_with_iam_rotated_medium_amplifier :
    ssrfImpactAmplifier true true true = 2 := by
  simp [ssrfImpactAmplifier]

-- Aggregate SSRF risk
def aggregateSSRFRisk
    (egressFilter urlVal privBlock : Bool)
    (imdsv2 metaFilter : Bool)
    (followRedirect postRedirectVal : Bool)
    (dnsRebindMit ipPinned : Bool) : Nat :=
  (if internalNetworkSSRFRisk egressFilter urlVal privBlock then 1 else 0) +
  (if cloudMetadataSSRFRisk imdsv2 metaFilter then 1 else 0) +
  (if redirectSSRFRisk followRedirect postRedirectVal then 1 else 0) +
  (if dnsRebindSSRFRisk dnsRebindMit ipPinned then 1 else 0)

theorem fully_hardened_zero_ssrf_risk :
    aggregateSSRFRisk true true true true true false true true true = 0 := by
  simp [aggregateSSRFRisk, internalNetworkSSRFRisk, cloudMetadataSSRFRisk,
        redirectSSRFRisk, dnsRebindSSRFRisk]

theorem all_vectors_max_ssrf_risk :
    aggregateSSRFRisk false false false false false true false false false = 4 := by
  simp [aggregateSSRFRisk, internalNetworkSSRFRisk, cloudMetadataSSRFRisk,
        redirectSSRFRisk, dnsRebindSSRFRisk]

-- Economic: SSRF scanner detection value (cloud breach is catastrophic)
def ssrfDetectionValueCents (cloudBreachCostCents : Nat) (scannerCostCents : Nat) : Int :=
  (cloudBreachCostCents : Int) - (scannerCostCents : Int)

theorem ssrf_detection_profitable (breach scan : Nat) (h : scan < breach) :
    0 < ssrfDetectionValueCents breach scan := by
  simp [ssrfDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem ssrf_detection_nonneg_break_even (cost : Nat) :
    0 ≤ ssrfDetectionValueCents cost cost := by
  simp [ssrfDetectionValueCents]

-- Fleet ROI: SSRF detections across many services
def ssrfFleetROICents (detectionValue : Nat) (servicesScanned : Nat) : Nat :=
  detectionValue * servicesScanned

theorem fleet_roi_scales_with_services (v s1 s2 : Nat) (h : s1 ≤ s2) :
    ssrfFleetROICents v s1 ≤ ssrfFleetROICents v s2 := by
  simp [ssrfFleetROICents]
  exact Nat.mul_le_mul_left v h

theorem positive_fleet_ssrf_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < ssrfFleetROICents v s := by
  simp [ssrfFleetROICents]
  exact Nat.mul_pos hv hs

end ServerSideRequestForgeryRisk
