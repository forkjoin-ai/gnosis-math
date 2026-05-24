import Init
-- InsecureAPIExposureRisk.lean
-- Anti-thesis: Internal or partner-facing APIs are safe because they are
-- not listed in public documentation and require knowing the endpoint URL.
-- Refutation: Security through obscurity fails at scale; unauthenticated
-- endpoints, excessive data in responses, and absent rate limiting each
-- yield strictly positive exploitation windows discoverable via JS bundle
-- analysis, Shodan, or traffic interception.

namespace Gnosis.Security.InsecureAPIExposureRisk

-- Unauthenticated endpoint: endpoint accessible without any credential check
def unauthenticatedEndpointRisk (authRequired : Bool) (dataSensitivity : Nat) : Nat :=
  if authRequired then 0 else dataSensitivity + 1

theorem api_auth_required_safe (s : Nat) :
    unauthenticatedEndpointRisk true s = 0 := by { simp [unauthenticatedEndpointRisk]

theorem api_no_auth_risk (s : Nat) :
    0 < unauthenticatedEndpointRisk false s := by
  simp [unauthenticatedEndpointRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Excessive data exposure: API returns full object when only subset needed
def excessiveDataRisk (fieldsReturned : Nat) (fieldsNeeded : Nat) : Nat :=
  if fieldsReturned <= fieldsNeeded then 0 else fieldsReturned - fieldsNeeded

theorem api_minimal_response_safe (r n : Nat) (h : r <= n) :
    excessiveDataRisk r n = 0 := by { simp [excessiveDataRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem api_excess_fields_risk (r n : Nat) (h : n < r) :
    0 < excessiveDataRisk r n := by { simp [excessiveDataRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Missing rate limit: no throttle enables data scraping or credential stuffing
def missingRateLimitRisk (rateLimitEnabled : Bool) (requestsPerMin : Nat) : Nat :=
  if rateLimitEnabled then 0 else requestsPerMin

theorem api_rate_limited_safe (r : Nat) :
    missingRateLimitRisk true r = 0 := by { simp [missingRateLimitRisk]

theorem api_no_rate_limit_risk (r : Nat) (h : 0 < r) :
    0 < missingRateLimitRisk false r := by
  simp [missingRateLimitRisk]; exact h

-- API key in response: server echoes credentials in JSON response body
def apiKeyInResponseRisk (keyRedacted : Bool) : Nat :=
  if keyRedacted then 0 else 1

theorem api_key_redacted_safe :
    apiKeyInResponseRisk true = 0 := by
  simp [apiKeyInResponseRisk]

theorem api_key_exposed_risk :
    0 < apiKeyInResponseRisk false := by
  simp [apiKeyInResponseRisk]

-- Mass data export_: bulk endpoint with no pagination or field restriction
def massExportRisk (paginationEnforced : Bool) (maxPageSize : Nat) (requestedSize : Nat) : Nat :=
  if paginationEnforced && requestedSize <= maxPageSize then 0
  else if paginationEnforced then requestedSize - maxPageSize
  else requestedSize + 1

theorem api_paginated_within_limit_safe (m r : Nat) (h : r <= m) :
    massExportRisk true m r = 0 := by
  simp [massExportRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem api_no_pagination_risk (m r : Nat) :
    0 < massExportRisk false m r := by { simp [massExportRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in data sensitivity
theorem api_unauth_risk_monotone (s1 s2 : Nat) (h : s1 <= s2) :
    unauthenticatedEndpointRisk false s1 <= unauthenticatedEndpointRisk false s2 := by { simp [unauthenticatedEndpointRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires auth, minimal response, rate limit, key redaction
def netAPIExposureRisk (authRequired : Bool) (fieldsReturned fieldsNeeded : Nat)
    (rateLimited : Bool) (keyRedacted : Bool) : Nat :=
  unauthenticatedEndpointRisk authRequired 0 +
  excessiveDataRisk fieldsReturned fieldsNeeded +
  missingRateLimitRisk rateLimited 0 +
  apiKeyInResponseRisk keyRedacted

theorem api_net_risk_zero_fully_mitigated (f n : Nat) (h : f <= n) :
    netAPIExposureRisk true f n true true = 0 := by { simp [netAPIExposureRisk, unauthenticatedEndpointRisk, excessiveDataRisk,
        missingRateLimitRisk, apiKeyInResponseRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem api_net_risk_pos_unmitigated (f n : Nat) (h : n < f) :
    0 < netAPIExposureRisk false f n false false := by { simp [netAPIExposureRisk, unauthenticatedEndpointRisk, excessiveDataRisk,
        missingRateLimitRisk, apiKeyInResponseRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end InsecureAPIExposureRisk
