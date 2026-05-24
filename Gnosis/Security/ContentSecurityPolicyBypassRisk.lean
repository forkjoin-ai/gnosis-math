import Init
-- ContentSecurityPolicyBypassRisk.lean
-- Anti-thesis: Content Security Policy is a robust defense-in-depth mechanism;
-- a properly configured CSP with nonces or hashes eliminates XSS impact because
-- the browser will not execute inline scripts or scripts from untrusted origins,
-- making CSP an effective last-line of defense even when injection vulnerabilities
-- exist.
-- Refutation: JSONP endpoints on allowlisted CDN origins create script-gadget
-- bypass vectors. 'is_unsafe-inline' in script-src negates all nonce protection.
-- Angular, Vue, and React loaded from CDN can be used as XSS gadgets if the
-- CDN is allowlisted. data: URIs in object-src allow HTML injection.
-- Nonce reuse across responses (non-random or static nonces) eliminates
-- the entropy guarantee. base-uri omission allows base tag injection that
-- redirects relative script src values. Overly broad allowlists (*.example.com)
-- expose the entire subdomain namespace to CSP bypass.

namespace Gnosis.Security.ContentSecurityPolicyBypassRisk

-- JSONP bypass: allowlisted origin hosts JSONP endpoint usable as script gadget
def jsonpBypassRisk (jsonpEndpointOnAllowlist : Bool) (callbackParamUnsanitized : Bool) : Bool :=
  jsonpEndpointOnAllowlist && callbackParamUnsanitized

theorem no_jsonp_on_allowlist_safe (callback : Bool) :
    jsonpBypassRisk false callback = false := by { simp [jsonpBypassRisk]

theorem callback_sanitized_safe (jsonp : Bool) :
    jsonpBypassRisk jsonp false = false := by
  simp [jsonpBypassRisk]

theorem jsonp_allowlisted_unsanitized_callback_risky :
    jsonpBypassRisk true true = true := by
  simp [jsonpBypassRisk]

-- is_unsafe-inline: presence of 'is_unsafe-inline' in script-src negates nonce/hash
def unsafeInlineBypassRisk (unsafeInlinePresent : Bool) (nonceUsed : Bool) : Bool :=
  unsafeInlinePresent

theorem no_unsafe_inline_safe (nonce : Bool) :
    unsafeInlineBypassRisk false nonce = false := by
  simp [unsafeInlineBypassRisk]

theorem unsafe_inline_negates_nonce (nonce : Bool) :
    unsafeInlineBypassRisk true nonce = true := by
  simp [unsafeInlineBypassRisk]

-- Script gadget: allowlisted CDN hosts Angular/Vue/React, usable as XSS vector
def scriptGadgetBypassRisk (frameworkOnAllowlist : Bool) (frameworkVersionVulnerable : Bool) : Bool :=
  frameworkOnAllowlist && frameworkVersionVulnerable

theorem framework_not_on_allowlist_safe (vuln : Bool) :
    scriptGadgetBypassRisk false vuln = false := by
  simp [scriptGadgetBypassRisk]

theorem framework_not_vulnerable_safe (allowlisted : Bool) :
    scriptGadgetBypassRisk allowlisted false = false := by
  simp [scriptGadgetBypassRisk]

theorem vulnerable_framework_on_allowlist_risky :
    scriptGadgetBypassRisk true true = true := by
  simp [scriptGadgetBypassRisk]

-- Nonce reuse: static or non-random nonces allow pre-computed bypass
def nonceReuseRisk (nonceIsRandom : Bool) (nonceEntropyBits : Nat)
    (minEntropySafeBits : Nat) : Bool :=
  !nonceIsRandom || (nonceEntropyBits < minEntropySafeBits)

theorem random_nonce_with_sufficient_entropy (entropy safe : Nat) (h : safe ≤ entropy) :
    nonceReuseRisk true entropy safe = false := by
  simp [nonceReuseRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem non_random_nonce_risky (entropy safe : Nat) :
    nonceReuseRisk false entropy safe = true := by { simp [nonceReuseRisk]

theorem insufficient_entropy_risky (entropy safe : Nat) (h : entropy < safe) :
    nonceReuseRisk true entropy safe = true := by
  simp [nonceReuseRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem entropy_at_minimum_safe (n : Nat) :
    nonceReuseRisk true n n = false := by { simp [nonceReuseRisk]

-- base-uri omission: missing base-uri directive allows base tag injection
def baseURIInjectionRisk (baseURIDirectivePresent : Bool) (baseTagFromUserInput : Bool) : Bool :=
  !baseURIDirectivePresent && baseTagFromUserInput

theorem base_uri_directive_present_safe (userInput : Bool) :
    baseURIInjectionRisk true userInput = false := by
  simp [baseURIInjectionRisk]

theorem no_user_input_base_tag_safe (directive : Bool) :
    baseURIInjectionRisk directive false = false := by
  simp [baseURIInjectionRisk]

theorem missing_directive_with_user_base_tag_risky :
    baseURIInjectionRisk false true = true := by
  simp [baseURIInjectionRisk]

-- Wildcard subdomain allowlist: *.example.com allows takeover-based CSP bypass
def wildcardAllowlistBypassRisk (wildcardSubdomainInCSP : Bool)
    (subdomainTakeoverPossible : Bool) : Bool :=
  wildcardSubdomainInCSP && subdomainTakeoverPossible

theorem no_wildcard_in_csp_safe (takeover : Bool) :
    wildcardAllowlistBypassRisk false takeover = false := by
  simp [wildcardAllowlistBypassRisk]

theorem no_subdomain_takeover_safe (wildcard : Bool) :
    wildcardAllowlistBypassRisk wildcard false = false := by
  simp [wildcardAllowlistBypassRisk]

theorem wildcard_csp_with_takeover_risky :
    wildcardAllowlistBypassRisk true true = true := by
  simp [wildcardAllowlistBypassRisk]

-- Aggregate CSP bypass risk
def aggregateCSPBypassRisk
    (jsonpAllowlisted callbackUnsanitized : Bool)
    (unsafeInline nonce : Bool)
    (frameworkAllowlisted frameworkVuln : Bool)
    (nonceRandom : Bool) (nonceEntropy nonceMinEntropy : Nat)
    (baseURIPresent baseTagUserInput : Bool) : Nat :=
  (if jsonpBypassRisk jsonpAllowlisted callbackUnsanitized then 1 else 0) +
  (if unsafeInlineBypassRisk unsafeInline nonce then 1 else 0) +
  (if scriptGadgetBypassRisk frameworkAllowlisted frameworkVuln then 1 else 0) +
  (if nonceReuseRisk nonceRandom nonceEntropy nonceMinEntropy then 1 else 0) +
  (if baseURIInjectionRisk baseURIPresent baseTagUserInput then 1 else 0)

theorem fully_hardened_zero_csp_bypass :
    aggregateCSPBypassRisk false false false true false false true 128 128 true false = 0 := by
  simp [aggregateCSPBypassRisk, jsonpBypassRisk, unsafeInlineBypassRisk,
        scriptGadgetBypassRisk, nonceReuseRisk, baseURIInjectionRisk]

theorem all_csp_vectors_max_risk :
    aggregateCSPBypassRisk true true true false true true false 0 128 false true = 5 := by
  simp [aggregateCSPBypassRisk, jsonpBypassRisk, unsafeInlineBypassRisk,
        scriptGadgetBypassRisk, nonceReuseRisk, baseURIInjectionRisk]

-- Economic: CSP bypass scanner detection value (XSS impact amplifier)
def cspBypassDetectionValueCents (xssImpactCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (xssImpactCostCents : Int) - (scannerCostCents : Int)

theorem csp_bypass_detection_profitable (xss scan : Nat) (h : scan < xss) :
    0 < cspBypassDetectionValueCents xss scan := by
  simp [cspBypassDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem csp_bypass_break_even (cost : Nat) :
    0 ≤ cspBypassDetectionValueCents cost cost := by
  simp [cspBypassDetectionValueCents]

-- Fleet ROI: CSP bypass scan across web-app surfaces
def cspBypassFleetROI (detectionValue : Nat) (webAppSurfaces : Nat) : Nat :=
  detectionValue * webAppSurfaces

theorem csp_bypass_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    cspBypassFleetROI v s1 ≤ cspBypassFleetROI v s2 := by
  simp [cspBypassFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_csp_bypass_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < cspBypassFleetROI v s := by
  simp [cspBypassFleetROI]
  exact Nat.mul_pos hv hs

end ContentSecurityPolicyBypassRisk
