import Init
-- CookieSecurityRisk.lean
-- Anti-thesis: Cookies are a mature, well-understood browser mechanism; setting
-- the Secure flag and using HTTPS is sufficient to protect session cookies from
-- network interception, and modern browsers enforce these semantics correctly.
-- Refutation: HttpOnly absence allows JavaScript to read session cookies via XSS.
-- Missing Secure flag sends cookies over HTTP when a user visits an HTTP URL.
-- SameSite=Lax (the browser default) does not protect against cross-site POST
-- CSRF. Cookie path-scope misconfiguration leaks cookies to other app paths on
-- the same origin. __Host- and __Secure- prefix enforcement is only as strong
-- as the server-side validation; missing prefix checks allow cookie override
-- from subdomains or HTTP origins.

namespace Gnosis.Security.CookieSecurityRisk

-- HttpOnly missing: session cookie readable by JavaScript (XSS amplifier)
def httpOnlyMissingRisk (httpOnlySet : Bool) (xssPossible : Bool) : Bool :=
  !httpOnlySet && xssPossible

theorem http_only_set_safe (xss : Bool) :
    httpOnlyMissingRisk true xss = false := by { simp [httpOnlyMissingRisk]

theorem no_xss_path_safe (httpOnly : Bool) :
    httpOnlyMissingRisk httpOnly false = false := by
  simp [httpOnlyMissingRisk]

theorem http_only_absent_with_xss_risky :
    httpOnlyMissingRisk false true = true := by
  simp [httpOnlyMissingRisk]

-- Secure flag missing: cookie sent over HTTP (network eavesdropping)
def secureFlagMissingRisk (secureFlagSet : Bool) (httpAccessible : Bool) : Bool :=
  !secureFlagSet && httpAccessible

theorem secure_flag_set_safe (http : Bool) :
    secureFlagMissingRisk true http = false := by
  simp [secureFlagMissingRisk]

theorem http_not_accessible_safe (secure : Bool) :
    secureFlagMissingRisk secure false = false := by
  simp [secureFlagMissingRisk]

theorem secure_absent_over_http_risky :
    secureFlagMissingRisk false true = true := by
  simp [secureFlagMissingRisk]

-- SameSite=Lax allows cross-site POST CSRF: top-level navigation only
def sameSiteLaxCSRFRisk (sameSiteValue : Nat) (requestIsPost : Bool)
    (crossSiteRequest : Bool) : Bool :=
  -- 0 = None, 1 = Lax, 2 = Strict
  sameSiteValue < 2 && requestIsPost && crossSiteRequest

theorem same_site_strict_safe (isPost crossSite : Bool) :
    sameSiteLaxCSRFRisk 2 isPost crossSite = false := by
  simp [sameSiteLaxCSRFRisk]

theorem same_site_strict_plus_safe (v : Nat) (isPost crossSite : Bool) (h : 2 ≤ v) :
    sameSiteLaxCSRFRisk v isPost crossSite = false := by
  simp [sameSiteLaxCSRFRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem not_post_request_safe (samesite : Nat) (crossSite : Bool) :
    sameSiteLaxCSRFRisk samesite false crossSite = false := by { simp [sameSiteLaxCSRFRisk]

theorem same_origin_request_safe (samesite : Nat) (isPost : Bool) :
    sameSiteLaxCSRFRisk samesite isPost false = false := by
  simp [sameSiteLaxCSRFRisk]

theorem lax_with_cross_site_post_risky :
    sameSiteLaxCSRFRisk 1 true true = true := by
  simp [sameSiteLaxCSRFRisk]

theorem none_with_cross_site_post_risky :
    sameSiteLaxCSRFRisk 0 true true = true := by
  simp [sameSiteLaxCSRFRisk]

-- Cookie path scope: overly broad path leaks cookie to unintended app paths
def cookiePathScopeRisk (cookiePath : Nat) (sensitivePath : Nat)
    (cookieSensitive : Bool) : Bool :=
  -- cookiePath=0 means '/' (broadest), sensitivePath is any path depth
  cookiePath = 0 && cookieSensitive

theorem narrow_cookie_path_safe (sensitivePath : Nat) (sensitive : Bool) (h : 0 < sensitivePath) :
    cookiePathScopeRisk sensitivePath sensitivePath sensitive = false := by
  simp [cookiePathScopeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem root_path_non_sensitive_safe (sensitivePath : Nat) :
    cookiePathScopeRisk 0 sensitivePath false = false := by { simp [cookiePathScopeRisk]

theorem root_path_sensitive_cookie_risky (sensitivePath : Nat) :
    cookiePathScopeRisk 0 sensitivePath true = true := by
  simp [cookiePathScopeRisk]

-- Cookie prefix bypass: __Host- / __Secure- not enforced allows subdomain override
def cookiePrefixBypassRisk (prefixRequired : Bool) (serverEnforcePrefix : Bool)
    (subdomainCanSetCookie : Bool) : Bool :=
  prefixRequired && !serverEnforcePrefix && subdomainCanSetCookie

theorem prefix_enforced_by_server_safe (required subdomainAccess : Bool) :
    cookiePrefixBypassRisk required true subdomainAccess = false := by
  simp [cookiePrefixBypassRisk]

theorem prefix_not_required_safe (enforced subdomainAccess : Bool) :
    cookiePrefixBypassRisk false enforced subdomainAccess = false := by
  simp [cookiePrefixBypassRisk]

theorem subdomain_cannot_set_cookie_safe (required enforced : Bool) :
    cookiePrefixBypassRisk required enforced false = false := by
  simp [cookiePrefixBypassRisk]

theorem required_prefix_unenforced_subdomain_access_risky :
    cookiePrefixBypassRisk true false true = true := by
  simp [cookiePrefixBypassRisk]

-- Aggregate cookie security risk count
def aggregateCookieSecurityRisk
    (httpOnlySet xssPossible : Bool)
    (secureSet httpAccessible : Bool)
    (sameSite : Nat) (isPost crossSite : Bool)
    (cookiePath sensitivePath : Nat) (cookieSensitive : Bool)
    (prefixRequired serverEnforces subdomainCanSet : Bool) : Nat :=
  (if httpOnlyMissingRisk httpOnlySet xssPossible then 1 else 0) +
  (if secureFlagMissingRisk secureSet httpAccessible then 1 else 0) +
  (if sameSiteLaxCSRFRisk sameSite isPost crossSite then 1 else 0) +
  (if cookiePathScopeRisk cookiePath sensitivePath cookieSensitive then 1 else 0) +
  (if cookiePrefixBypassRisk prefixRequired serverEnforces subdomainCanSet then 1 else 0)

theorem fully_hardened_zero_cookie_risk :
    aggregateCookieSecurityRisk
      true false
      true false
      2 true true
      1 1 false
      true true false = 0 := by
  simp [aggregateCookieSecurityRisk, httpOnlyMissingRisk, secureFlagMissingRisk,
        sameSiteLaxCSRFRisk, cookiePathScopeRisk, cookiePrefixBypassRisk]

theorem all_cookie_vectors_max_risk :
    aggregateCookieSecurityRisk
      false true
      false true
      0 true true
      0 0 true
      true false true = 5 := by
  simp [aggregateCookieSecurityRisk, httpOnlyMissingRisk, secureFlagMissingRisk,
        sameSiteLaxCSRFRisk, cookiePathScopeRisk, cookiePrefixBypassRisk]

theorem cookie_risk_bounded (
    httpOnlySet xssPossible secureSet httpAccessible : Bool)
    (sameSite : Nat) (isPost crossSite : Bool)
    (cookiePath sensitivePath : Nat) (cookieSensitive : Bool)
    (prefixRequired serverEnforces subdomainCanSet : Bool) :
    aggregateCookieSecurityRisk
      httpOnlySet xssPossible secureSet httpAccessible
      sameSite isPost crossSite
      cookiePath sensitivePath cookieSensitive
      prefixRequired serverEnforces subdomainCanSet ≤ 5 := by
  simp [aggregateCookieSecurityRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: cookie security flaw detection prevents XSS/CSRF/session theft
def cookieSecurityDetectionValueCents (sessionTheftCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (sessionTheftCostCents : Int) - (scannerCostCents : Int)

theorem cookie_scanner_profitable (theft scan : Nat) (h : scan < theft) :
    0 < cookieSecurityDetectionValueCents theft scan := by
  simp [cookieSecurityDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem cookie_scanner_break_even (cost : Nat) :
    0 ≤ cookieSecurityDetectionValueCents cost cost := by
  simp [cookieSecurityDetectionValueCents]

-- Fleet ROI: cookie security scan across all web endpoints
def cookieSecurityFleetROI (detectionValueCents : Nat) (endpoints : Nat) : Nat :=
  detectionValueCents * endpoints

theorem cookie_fleet_roi_monotone (v e1 e2 : Nat) (h : e1 ≤ e2) :
    cookieSecurityFleetROI v e1 ≤ cookieSecurityFleetROI v e2 := by
  simp [cookieSecurityFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_cookie_fleet_roi (v e : Nat) (hv : 0 < v) (he : 0 < e) :
    0 < cookieSecurityFleetROI v e := by
  simp [cookieSecurityFleetROI]
  exact Nat.mul_pos hv he

end CookieSecurityRisk
