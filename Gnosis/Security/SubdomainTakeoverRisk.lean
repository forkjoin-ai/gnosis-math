import Init
-- SubdomainTakeoverRisk.lean
-- Anti-thesis: subdomain takeover requires that an attacker register a specific
-- external service account, which is detectable noise; DNS monitoring tools catch
-- dangling CNAMEs immediately, and deprovisioned cloud resources are automatically
-- reclaimed, making takeover windows too short to exploit.
-- Refutation: DNS TTLs are often 300-3600 seconds, creating exploitation windows
-- after deprovisioning. Wildcard DNS records can expose entire *.example.com
-- namespaces. Abandoned S3 buckets, GitHub Pages, Heroku, and Azure resources
-- remain claimable for hours to days. NS record delegation takeovers are permanent
-- until DNS entry is removed. Subdomain takeover enables phishing, cookie theft
-- (same-site cookies), CSP bypass, and OAuth redirect_uri hijacking.

namespace Gnosis.Security.SubdomainTakeoverRisk

-- Dangling CNAME: CNAME points to deprovisioned external service
def danglingCNAMERisk (cnameTarget : Bool) (targetServiceActive : Bool)
    (dnsMonitoringEnabled : Bool) : Bool :=
  cnameTarget && !targetServiceActive && !dnsMonitoringEnabled

theorem no_cname_no_dangling (active mon : Bool) :
    danglingCNAMERisk false active mon = false := by { simp [danglingCNAMERisk]

theorem target_still_active_no_risk (cname mon : Bool) :
    danglingCNAMERisk cname true mon = false := by
  simp [danglingCNAMERisk]

theorem dns_monitoring_catches_dangling (cname active : Bool) :
    danglingCNAMERisk cname active true = false := by
  simp [danglingCNAMERisk]

theorem unmonitored_deprovisioned_dangling_risky :
    danglingCNAMERisk true false false = true := by
  simp [danglingCNAMERisk]

-- Deprovisioned service claim window: time between deprovisioning and DNS removal
def deprovisionedClaimWindowRisk (ttlSeconds : Nat) (dnsRemovalDelaySeconds : Nat)
    (claimWindowThreshold : Nat) : Bool :=
  claimWindowThreshold < ttlSeconds + dnsRemovalDelaySeconds

theorem zero_delay_within_threshold_safe (ttl threshold : Nat) (h : ttl ≤ threshold) :
    deprovisionedClaimWindowRisk ttl 0 threshold = false := by
  simp [deprovisionedClaimWindowRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem long_ttl_creates_claim_window (ttl delay threshold : Nat)
    (h : threshold < ttl + delay) :
    deprovisionedClaimWindowRisk ttl delay threshold = true := by { simp [deprovisionedClaimWindowRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem immediate_dns_removal_helps (ttl threshold : Nat) (h : ttl ≤ threshold) :
    deprovisionedClaimWindowRisk ttl 0 threshold = false := by { simp [deprovisionedClaimWindowRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- NS record takeover: subdomain NS delegation to expired/claimable registrar account
def nsDelegationTakeoverRisk (nsDelegated : Bool) (delegatedNSActive : Bool)
    (registrarAccountMonitored : Bool) : Bool :=
  nsDelegated && !delegatedNSActive && !registrarAccountMonitored

theorem no_delegation_safe (active mon : Bool) :
    nsDelegationTakeoverRisk false active mon = false := by { simp [nsDelegationTakeoverRisk]

theorem delegated_ns_still_active_safe (deleg mon : Bool) :
    nsDelegationTakeoverRisk deleg true mon = false := by
  simp [nsDelegationTakeoverRisk]

theorem monitored_registrar_catches_lapse (deleg active : Bool) :
    nsDelegationTakeoverRisk deleg active true = false := by
  simp [nsDelegationTakeoverRisk]

theorem unmonitored_expired_ns_takeover_risky :
    nsDelegationTakeoverRisk true false false = true := by
  simp [nsDelegationTakeoverRisk]

-- Wildcard DNS: *.example.com exposes all unregistered subdomains
def wildcardDNSTakeoverRisk (wildcardDNSEnabled : Bool) (wildcardTargetClaimable : Bool)
    (wildcardMonitored : Bool) : Bool :=
  wildcardDNSEnabled && wildcardTargetClaimable && !wildcardMonitored

theorem no_wildcard_safe (claim mon : Bool) :
    wildcardDNSTakeoverRisk false claim mon = false := by
  simp [wildcardDNSTakeoverRisk]

theorem wildcard_target_not_claimable_safe (wild mon : Bool) :
    wildcardDNSTakeoverRisk wild false mon = false := by
  simp [wildcardDNSTakeoverRisk]

theorem wildcard_monitored_safe (wild claim : Bool) :
    wildcardDNSTakeoverRisk wild claim true = false := by
  simp [wildcardDNSTakeoverRisk]

theorem unmonitored_claimable_wildcard_risky :
    wildcardDNSTakeoverRisk true true false = true := by
  simp [wildcardDNSTakeoverRisk]

-- OAuth impact: taken-over subdomain hijacks OAuth redirect_uri
def subdomainTakeoverOAuthImpact (takeoverPossible : Bool) (oauthRedirectToSubdomain : Bool)
    (redirectURIValidated : Bool) : Bool :=
  takeoverPossible && oauthRedirectToSubdomain && !redirectURIValidated

theorem no_takeover_no_oauth_impact (oauth val : Bool) :
    subdomainTakeoverOAuthImpact false oauth val = false := by
  simp [subdomainTakeoverOAuthImpact]

theorem no_oauth_redirect_no_impact (takeover val : Bool) :
    subdomainTakeoverOAuthImpact takeover false val = false := by
  simp [subdomainTakeoverOAuthImpact]

theorem redirect_uri_validated_blocks_impact (takeover oauth : Bool) :
    subdomainTakeoverOAuthImpact takeover oauth true = false := by
  simp [subdomainTakeoverOAuthImpact]

theorem unvalidated_oauth_redirect_to_taken_subdomain_risky :
    subdomainTakeoverOAuthImpact true true false = true := by
  simp [subdomainTakeoverOAuthImpact]

-- Aggregate subdomain takeover risk
def aggregateSubdomainTakeoverRisk
    (cname active dnsMonitor : Bool)
    (nsDelegated nsActive registrarMonitor : Bool)
    (wildcard wildcardClaim wildcardMonitor : Bool) : Nat :=
  (if danglingCNAMERisk cname active dnsMonitor then 1 else 0) +
  (if nsDelegationTakeoverRisk nsDelegated nsActive registrarMonitor then 1 else 0) +
  (if wildcardDNSTakeoverRisk wildcard wildcardClaim wildcardMonitor then 1 else 0)

theorem fully_hardened_zero_subdomain_takeover :
    aggregateSubdomainTakeoverRisk true true true true true true false false true = 0 := by
  simp [aggregateSubdomainTakeoverRisk, danglingCNAMERisk, nsDelegationTakeoverRisk,
        wildcardDNSTakeoverRisk]

theorem all_subdomain_vectors_max_risk :
    aggregateSubdomainTakeoverRisk true false false true false false true true false = 3 := by
  simp [aggregateSubdomainTakeoverRisk, danglingCNAMERisk, nsDelegationTakeoverRisk,
        wildcardDNSTakeoverRisk]

-- Economic: subdomain takeover scanner detection value
def subdomainTakeoverDetectionValueCents (phishingBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (phishingBreachCostCents : Int) - (scannerCostCents : Int)

theorem subdomain_takeover_detection_profitable (breach scan : Nat) (h : scan < breach) :
    0 < subdomainTakeoverDetectionValueCents breach scan := by
  simp [subdomainTakeoverDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem subdomain_takeover_break_even (cost : Nat) :
    0 ≤ subdomainTakeoverDetectionValueCents cost cost := by
  simp [subdomainTakeoverDetectionValueCents]

-- Fleet ROI: subdomain takeover scans across DNS zones
def subdomainTakeoverFleetROI (detectionValue : Nat) (dnsZonesScanned : Nat) : Nat :=
  detectionValue * dnsZonesScanned

theorem subdomain_takeover_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    subdomainTakeoverFleetROI v s1 ≤ subdomainTakeoverFleetROI v s2 := by
  simp [subdomainTakeoverFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_subdomain_takeover_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < subdomainTakeoverFleetROI v s := by
  simp [subdomainTakeoverFleetROI]
  exact Nat.mul_pos hv hs

end SubdomainTakeoverRisk
