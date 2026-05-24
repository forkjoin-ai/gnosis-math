import Init
-- ForceHTTPSRedirectRisk.lean
-- Anti-thesis: Forcing HTTP to HTTPS via a 301/302 redirect is a simple, reliable
-- security control; once HTTPS is enforced and HSTS is set, browsers will never
-- downgrade, and the redirect loop problem is a harmless misconfiguration edge
-- case that only affects localhost testing, not production.
-- Refutation: Redirect loops occur when HTTPS termination happens at the load
-- balancer but the back-end app still sees HTTP and re-issues the redirect.
-- HSTS max-age below the recommended minimum (typically 1 year = 31536000s)
-- allows the policy to expire before the next access, exposing a downgrade window.
-- Missing includeSubDomains allows cookie theft via a subdomain running HTTP.
-- Preload list eligibility requires min-age and includeSubDomains; an incomplete
-- HSTS header is never submitted to the browser preload list, leaving first-visit
-- windows permanently open.

namespace Gnosis.Security.ForceHTTPSRedirectRisk

-- Redirect loop: back-end issues HTTP→HTTPS redirect when TLS terminates at proxy
def redirectLoopRisk (tlsTerminatesAtProxy : Bool) (backendSeesHTTP : Bool)
    (backendRedirectsHTTPS : Bool) : Bool :=
  tlsTerminatesAtProxy && backendSeesHTTP && backendRedirectsHTTPS

theorem tls_not_at_proxy_safe (seesHTTP redirects : Bool) :
    redirectLoopRisk false seesHTTP redirects = false := by { simp [redirectLoopRisk]

theorem backend_sees_https_safe (atProxy redirects : Bool) :
    redirectLoopRisk atProxy false redirects = false := by
  simp [redirectLoopRisk]

theorem backend_not_redirecting_safe (atProxy seesHTTP : Bool) :
    redirectLoopRisk atProxy seesHTTP false = false := by
  simp [redirectLoopRisk]

theorem proxy_tls_backend_http_redirecting_loops :
    redirectLoopRisk true true true = true := by
  simp [redirectLoopRisk]

-- HSTS max-age insufficient: policy expires before next user visit
def hstsMaxAgeRisk (maxAgeSeconds : Nat) (minRecommendedSeconds : Nat) : Bool :=
  maxAgeSeconds < minRecommendedSeconds

theorem sufficient_max_age_safe (maxAge minAge : Nat) (h : minAge ≤ maxAge) :
    hstsMaxAgeRisk maxAge minAge = false := by
  simp [hstsMaxAgeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem insufficient_max_age_risky (maxAge minAge : Nat) (h : maxAge < minAge) :
    hstsMaxAgeRisk maxAge minAge = true := by { simp [hstsMaxAgeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem zero_max_age_always_risky (minAge : Nat) (h : 0 < minAge) :
    hstsMaxAgeRisk 0 minAge = true := by { simp [hstsMaxAgeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem recommended_min_age_boundary (n : Nat) :
    hstsMaxAgeRisk n n = false := by { simp [hstsMaxAgeRisk]

-- includeSubDomains missing: cookie theft via HTTP subdomain
def includeSubdomainsMissingRisk (includeSubdomains : Bool)
    (subdomainRunsHTTP : Bool) (cookieSharedWithSubdomain : Bool) : Bool :=
  !includeSubdomains && subdomainRunsHTTP && cookieSharedWithSubdomain

theorem include_subdomains_set_safe (subHTTP cookieShared : Bool) :
    includeSubdomainsMissingRisk true subHTTP cookieShared = false := by
  simp [includeSubdomainsMissingRisk]

theorem subdomain_not_on_http_safe (incl cookieShared : Bool) :
    includeSubdomainsMissingRisk incl false cookieShared = false := by
  simp [includeSubdomainsMissingRisk]

theorem cookie_not_shared_with_subdomain_safe (incl subHTTP : Bool) :
    includeSubdomainsMissingRisk incl subHTTP false = false := by
  simp [includeSubdomainsMissingRisk]

theorem missing_incl_subdomain_http_shared_cookie_risky :
    includeSubdomainsMissingRisk false true true = true := by
  simp [includeSubdomainsMissingRisk]

-- Preload eligibility: HSTS header must have min-age + includeSubDomains + preload flag
def preloadIneligibleRisk (preloadFlagSet : Bool) (includeSubdomains : Bool)
    (maxAgeSeconds : Nat) (preloadMinAgeSeconds : Nat) : Bool :=
  !(preloadFlagSet && includeSubdomains && preloadMinAgeSeconds ≤ maxAgeSeconds)

theorem preload_eligible_not_risky (maxAge minAge : Nat) (h : minAge ≤ maxAge) :
    preloadIneligibleRisk true true maxAge minAge = false := by
  simp [preloadIneligibleRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem preload_flag_missing_risky (incl : Bool) (maxAge minAge : Nat) :
    preloadIneligibleRisk false incl maxAge minAge = true := by { simp [preloadIneligibleRisk]

theorem include_subdomains_missing_prevents_preload (preload : Bool) (maxAge minAge : Nat) :
    preloadIneligibleRisk preload false maxAge minAge = true := by
  simp [preloadIneligibleRisk]

theorem short_max_age_prevents_preload (maxAge minAge : Nat) (h : maxAge < minAge) :
    preloadIneligibleRisk true true maxAge minAge = true := by
  simp [preloadIneligibleRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Mixed-content: HTTPS page loads HTTP sub-resource, downgrading protection
def mixedContentRisk (pageIsHTTPS : Bool) (subresourceIsHTTP : Bool)
    (cspUpgradeInsecureRequests : Bool) : Bool :=
  pageIsHTTPS && subresourceIsHTTP && !cspUpgradeInsecureRequests

theorem page_not_https_no_mixed_content (subHTTP cspUpgrade : Bool) :
    mixedContentRisk false subHTTP cspUpgrade = false := by { simp [mixedContentRisk]

theorem subresource_is_https_safe (pageHTTPS cspUpgrade : Bool) :
    mixedContentRisk pageHTTPS false cspUpgrade = false := by
  simp [mixedContentRisk]

theorem csp_upgrade_insecure_prevents_mixed (pageHTTPS subHTTP : Bool) :
    mixedContentRisk pageHTTPS subHTTP true = false := by
  simp [mixedContentRisk]

theorem https_page_with_http_resource_and_no_csp_risky :
    mixedContentRisk true true false = true := by
  simp [mixedContentRisk]

-- Aggregate HTTPS enforcement risk count
def aggregateForceHTTPSRisk
    (tlsAtProxy backendHTTP backendRedirects : Bool)
    (maxAge minAge : Nat)
    (inclSubdomains subHTTP cookieShared : Bool)
    (preloadFlag preloadIncl : Bool) (preloadAge preloadMin : Nat)
    (pageHTTPS subHTTP2 cspUpgrade : Bool) : Nat :=
  (if redirectLoopRisk tlsAtProxy backendHTTP backendRedirects then 1 else 0) +
  (if hstsMaxAgeRisk maxAge minAge then 1 else 0) +
  (if includeSubdomainsMissingRisk inclSubdomains subHTTP cookieShared then 1 else 0) +
  (if preloadIneligibleRisk preloadFlag preloadIncl preloadAge preloadMin then 1 else 0) +
  (if mixedContentRisk pageHTTPS subHTTP2 cspUpgrade then 1 else 0)

theorem fully_hardened_zero_https_risk :
    aggregateForceHTTPSRisk
      false false false
      31536000 31536000
      true false false
      true true 31536000 31536000
      true false true = 0 := by
  simp [aggregateForceHTTPSRisk, redirectLoopRisk, hstsMaxAgeRisk,
        includeSubdomainsMissingRisk, preloadIneligibleRisk, mixedContentRisk]

theorem all_https_vectors_max_risk :
    aggregateForceHTTPSRisk
      true true true
      0 31536000
      false true true
      false false 0 31536000
      true true false = 5 := by
  simp [aggregateForceHTTPSRisk, redirectLoopRisk, hstsMaxAgeRisk,
        includeSubdomainsMissingRisk, preloadIneligibleRisk, mixedContentRisk]

theorem https_risk_bounded
    (tlsAtProxy backendHTTP backendRedirects : Bool)
    (maxAge minAge : Nat)
    (inclSubdomains subHTTP cookieShared : Bool)
    (preloadFlag preloadIncl : Bool) (preloadAge preloadMin : Nat)
    (pageHTTPS subHTTP2 cspUpgrade : Bool) :
    aggregateForceHTTPSRisk
      tlsAtProxy backendHTTP backendRedirects
      maxAge minAge
      inclSubdomains subHTTP cookieShared
      preloadFlag preloadIncl preloadAge preloadMin
      pageHTTPS subHTTP2 cspUpgrade ≤ 5 := by
  simp [aggregateForceHTTPSRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: detecting HTTPS enforcement gaps prevents MITM / downgrade cost
def httpsEnforcementDetectionValueCents (mitMcostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (mitMcostCents : Int) - (scannerCostCents : Int)

theorem https_enforcement_scanner_profitable (mitm scan : Nat) (h : scan < mitm) :
    0 < httpsEnforcementDetectionValueCents mitm scan := by
  simp [httpsEnforcementDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem https_enforcement_scanner_break_even (cost : Nat) :
    0 ≤ httpsEnforcementDetectionValueCents cost cost := by
  simp [httpsEnforcementDetectionValueCents]

-- Fleet ROI: HTTPS enforcement scan across all hosts
def httpsEnforcementFleetROI (detectionValueCents : Nat) (hosts : Nat) : Nat :=
  detectionValueCents * hosts

theorem https_fleet_roi_monotone (v h1 h2 : Nat) (hle : h1 ≤ h2) :
    httpsEnforcementFleetROI v h1 ≤ httpsEnforcementFleetROI v h2 := by
  simp [httpsEnforcementFleetROI]
  exact Nat.mul_le_mul_left v hle

theorem positive_https_fleet_roi (v h : Nat) (hv : 0 < v) (hh : 0 < h) :
    0 < httpsEnforcementFleetROI v h := by
  simp [httpsEnforcementFleetROI]
  exact Nat.mul_pos hv hh

end ForceHTTPSRedirectRisk
