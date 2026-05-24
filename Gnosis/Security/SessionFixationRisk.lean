import Init
-- SessionFixationRisk.lean
-- Anti-thesis: session fixation is a legacy issue; modern frameworks always
-- regenerate session IDs on login, so an attacker who pre-sets a session token
-- gains nothing because the server issues a fresh token upon authentication.
-- Refutation: Many frameworks regenerate the session ID but preserve session data
-- (including pre-auth attacker-planted data). URL-based session tokens survive
-- after login regeneration if the application falls back to URL parameter sessions.
-- Cookie scope misconfigurations (Domain=.example.com) allow subdomain-controlled
-- tokens to survive across the auth boundary. OWASP A07 includes session fixation
-- as a root cause for broken authentication at scale.

namespace Gnosis.Security.SessionFixationRisk

-- Pre-auth token fixation: attacker plants a known session ID before user logs in
def preAuthTokenFixationRisk (sessionIdRegeneratedOnLogin : Bool)
    (urlSessionFallback : Bool) : Bool :=
  !sessionIdRegeneratedOnLogin || urlSessionFallback

theorem regeneration_and_no_url_fallback_safe :
    preAuthTokenFixationRisk true false = false := by { simp [preAuthTokenFixationRisk]

theorem no_regeneration_always_risky (url : Bool) :
    preAuthTokenFixationRisk false url = true := by
  simp [preAuthTokenFixationRisk]

theorem url_session_fallback_fixable_even_with_regen :
    preAuthTokenFixationRisk true true = true := by
  simp [preAuthTokenFixationRisk]

-- Session regeneration: after login, old session ID must be fully invalidated
def sessionRegenerationRisk (oldSessionInvalidated : Bool) (sessionDataPreserved : Bool)
    (preAuthDataTrusted : Bool) : Bool :=
  !oldSessionInvalidated || (sessionDataPreserved && preAuthDataTrusted)

theorem old_session_invalidated_no_trust_safe :
    sessionRegenerationRisk true false false = false := by
  simp [sessionRegenerationRisk]

theorem old_session_not_invalidated_risky (preserved trusted : Bool) :
    sessionRegenerationRisk false preserved trusted = true := by
  simp [sessionRegenerationRisk]

theorem data_preserved_and_trusted_risky (invalidated : Bool) :
    sessionRegenerationRisk invalidated true true = true := by
  simp [sessionRegenerationRisk]
  cases invalidated <;> simp

theorem data_preserved_not_trusted_safe :
    sessionRegenerationRisk true true false = false := by
  simp [sessionRegenerationRisk]

-- Cookie scope: overly broad Domain= allows attacker on subdomain to fix session
def cookieScopeFixationRisk (cookieDomainBroad : Bool) (subdomainAttackerControlled : Bool)
    (secureFlagSet : Bool) : Bool :=
  cookieDomainBroad && subdomainAttackerControlled && !secureFlagSet

theorem narrow_cookie_scope_safe (sub secure : Bool) :
    cookieScopeFixationRisk false sub secure = false := by
  simp [cookieScopeFixationRisk]

theorem no_attacker_subdomain_safe (broad secure : Bool) :
    cookieScopeFixationRisk broad false secure = false := by
  simp [cookieScopeFixationRisk]

theorem secure_flag_limits_scope_risk (broad sub : Bool) :
    cookieScopeFixationRisk broad sub true = false := by
  simp [cookieScopeFixationRisk]

theorem broad_scope_attacker_subdomain_no_secure_risky :
    cookieScopeFixationRisk true true false = true := by
  simp [cookieScopeFixationRisk]

-- Post-login session entropy: low-entropy tokens are guessable even without fixation
def sessionEntropyRisk (tokenBits : Nat) (minimumSafeBits : Nat) : Bool :=
  tokenBits < minimumSafeBits

theorem sufficient_entropy_safe (bits min : Nat) (h : min ≤ bits) :
    sessionEntropyRisk bits min = false := by
  simp [sessionEntropyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem insufficient_entropy_risky (bits min : Nat) (h : bits < min) :
    sessionEntropyRisk bits min = true := by { simp [sessionEntropyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem entropy_at_minimum_just_safe (n : Nat) :
    sessionEntropyRisk n n = false := by { simp [sessionEntropyRisk]

-- Session expiry: persistent sessions extend the fixation window
def sessionExpiryRisk (maxSessionAgeSeconds : Nat) (policyMaxSeconds : Nat) : Bool :=
  policyMaxSeconds < maxSessionAgeSeconds

theorem session_within_policy_safe (age policy : Nat) (h : age ≤ policy) :
    sessionExpiryRisk age policy = false := by
  simp [sessionExpiryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem session_exceeds_policy_risky (age policy : Nat) (h : policy < age) :
    sessionExpiryRisk age policy = true := by { simp [sessionExpiryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem policy_matches_age_safe (n : Nat) :
    sessionExpiryRisk n n = false := by { simp [sessionExpiryRisk]

-- Aggregate session fixation risk
def aggregateSessionFixationRisk
    (regenerated urlFallback : Bool)
    (invalidated preserved trusted : Bool)
    (broadDomain subAttacker secure : Bool) : Nat :=
  (if preAuthTokenFixationRisk regenerated urlFallback then 1 else 0) +
  (if sessionRegenerationRisk invalidated preserved trusted then 1 else 0) +
  (if cookieScopeFixationRisk broadDomain subAttacker secure then 1 else 0)

theorem fully_hardened_zero_fixation_risk :
    aggregateSessionFixationRisk true false true false false false false true = 0 := by
  simp [aggregateSessionFixationRisk, preAuthTokenFixationRisk,
        sessionRegenerationRisk, cookieScopeFixationRisk]

theorem all_vectors_max_fixation_risk :
    aggregateSessionFixationRisk false true false true true true true false = 3 := by
  simp [aggregateSessionFixationRisk, preAuthTokenFixationRisk,
        sessionRegenerationRisk, cookieScopeFixationRisk]

-- Economic: session fixation detection value
def sessionFixationDetectionValueCents (accountTakeoverCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (accountTakeoverCostCents : Int) - (scannerCostCents : Int)

theorem fixation_detection_profitable (ato scan : Nat) (h : scan < ato) :
    0 < sessionFixationDetectionValueCents ato scan := by
  simp [sessionFixationDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem fixation_break_even (cost : Nat) :
    0 ≤ sessionFixationDetectionValueCents cost cost := by
  simp [sessionFixationDetectionValueCents]

-- Fleet ROI: session fixation detections across authenticated services
def sessionFixationFleetROI (detectionValue : Nat) (authenticatedServices : Nat) : Nat :=
  detectionValue * authenticatedServices

theorem fixation_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    sessionFixationFleetROI v s1 ≤ sessionFixationFleetROI v s2 := by
  simp [sessionFixationFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_fixation_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < sessionFixationFleetROI v s := by
  simp [sessionFixationFleetROI]
  exact Nat.mul_pos hv hs

end SessionFixationRisk
