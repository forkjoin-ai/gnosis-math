import Init
-- CORSMisconfigRisk.lean
-- Anti-thesis: Setting Access-Control-Allow-Origin to a wildcard or reflecting
-- the request Origin carries no risk because CORS is a browser-only control.
-- Refutation: Wildcard ACAO combined with credentials, or reflected Origin
-- without validation, allows any attacker page to read authenticated API
-- responses, yielding a strictly positive vulnerability window.

namespace Gnosis.Security.CORSMisconfigRisk

-- Wildcard ACAO with credentials: browsers block but misconfigured servers expose data
def wildcardWithCredentialsRisk (allowCredentials : Bool) (wildcardOrigin : Bool) : Nat :=
  if allowCredentials && wildcardOrigin then 1 else 0

-- Wildcard without credentials is safe (browsers enforce this)
theorem cors_wildcard_no_credentials_safe :
    wildcardWithCredentialsRisk false true = 0 := by { simp [wildcardWithCredentialsRisk]

-- Wildcard with credentials is a misconfiguration
theorem cors_wildcard_with_credentials_risk :
    0 < wildcardWithCredentialsRisk true true := by
  simp [wildcardWithCredentialsRisk]

-- Reflected Origin: server echoes any Origin header without validation
def reflectedOriginRisk (originLen : Nat) (originValidated : Bool) : Nat :=
  if originValidated then 0 else originLen + 1

theorem cors_origin_validated_safe (n : Nat) :
    reflectedOriginRisk n true = 0 := by
  simp [reflectedOriginRisk]

theorem cors_origin_reflected_risk (n : Nat) :
    0 < reflectedOriginRisk n false := by
  simp [reflectedOriginRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Null origin: ACAO: null accepts sandboxed iframe requests
def nullOriginRisk (nullOriginAllowed : Bool) : Nat :=
  if nullOriginAllowed then 1 else 0

theorem cors_null_origin_blocked_safe :
    nullOriginRisk false = 0 := by { simp [nullOriginRisk]

theorem cors_null_origin_allowed_risk :
    0 < nullOriginRisk true := by
  simp [nullOriginRisk]

-- Subdomain wildcard: *.trusted.com allows attacker.trusted.com
def subdomainWildcardRisk (subdomainLen : Nat) (exactMatchRequired : Bool) : Nat :=
  if exactMatchRequired then 0 else subdomainLen + 1

theorem cors_exact_match_safe (n : Nat) :
    subdomainWildcardRisk n true = 0 := by
  simp [subdomainWildcardRisk]

theorem cors_subdomain_wildcard_risk (n : Nat) :
    0 < subdomainWildcardRisk n false := by
  simp [subdomainWildcardRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Exposed internal API: internal endpoint with permissive CORS accessible externally
def internalApiExposureRisk (isInternal : Bool) (corsRestricted : Bool) : Nat :=
  if !isInternal || corsRestricted then 0 else 1

theorem cors_internal_api_restricted_safe :
    internalApiExposureRisk true true = 0 := by { simp [internalApiExposureRisk]

theorem cors_internal_api_open_risk :
    0 < internalApiExposureRisk true false := by
  simp [internalApiExposureRisk]

-- Risk monotone in reflected origin length
theorem cors_reflected_risk_monotone (n m : Nat) (h : n ≤ m) :
    reflectedOriginRisk n false ≤ reflectedOriginRisk m false := by
  simp [reflectedOriginRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires origin validated AND no wildcard-with-credentials
def netCorsRisk (originLen : Nat) (originValidated : Bool) (wildcardWithCreds : Bool) : Nat :=
  reflectedOriginRisk originLen originValidated + wildcardWithCredentialsRisk true wildcardWithCreds

theorem cors_net_risk_zero_fully_mitigated (n : Nat) :
    netCorsRisk n true false = 0 := by { simp [netCorsRisk, reflectedOriginRisk, wildcardWithCredentialsRisk]

theorem cors_net_risk_pos_unmitigated (n : Nat) :
    0 < netCorsRisk n false true := by
  simp [netCorsRisk, reflectedOriginRisk, wildcardWithCredentialsRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end CORSMisconfigRisk
