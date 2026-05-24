import Init
-- AccountEnumerationRisk.lean
-- Anti-thesis: account enumeration is a minor information disclosure; an attacker
-- who learns that a username exists must still guess the password, so enumeration
-- provides negligible real-world advantage compared to credential-stuffing attacks
-- that already possess breached username lists.
-- Refutation: Enumeration dramatically improves targeted phishing and spear-phishing
-- by confirming high-value account existence (executives, admins). Timing differences
-- as small as 5ms between "user not found" and "wrong password" paths are
-- statistically distinguishable at scale. Response-body differences ("Invalid
-- username" vs "Invalid password") give attackers a binary oracle. Password-reset
-- flows frequently disclose account existence via email confirmation messages.
-- Enumeration is the prerequisite for credential-stuffing campaigns that deliver
-- 85%+ of account takeover incidents.

namespace Gnosis.Security.AccountEnumerationRisk

-- Timing-based enumeration: different response times for valid vs invalid usernames
def timingEnumerationRisk (responsesConstantTime : Bool) (timingVarianceMs : Nat)
    (detectableThresholdMs : Nat) : Bool :=
  !responsesConstantTime && (detectableThresholdMs < timingVarianceMs)

theorem constant_time_prevents_timing_enum (variance threshold : Nat) :
    timingEnumerationRisk true variance threshold = false := by { simp [timingEnumerationRisk]

theorem variance_within_threshold_safe (variance threshold : Nat) (h : variance ≤ threshold) :
    timingEnumerationRisk false variance threshold = false := by
  simp [timingEnumerationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem variance_exceeds_threshold_risky (variance threshold : Nat)
    (h : threshold < variance) :
    timingEnumerationRisk false variance threshold = true := by { simp [timingEnumerationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem zero_variance_safe (threshold : Nat) :
    timingEnumerationRisk false 0 threshold = false := by { simp [timingEnumerationRisk]

-- Response-body enumeration: different error messages for unknown vs known accounts
def responseBodyEnumerationRisk (genericErrorMessage : Bool) (sameHttpStatusCode : Bool) : Bool :=
  !genericErrorMessage || !sameHttpStatusCode

theorem generic_error_same_status_safe :
    responseBodyEnumerationRisk true true = false := by
  simp [responseBodyEnumerationRisk]

theorem specific_error_message_risky (status : Bool) :
    responseBodyEnumerationRisk false status = true := by
  simp [responseBodyEnumerationRisk]

theorem different_status_codes_risky (generic : Bool) :
    responseBodyEnumerationRisk generic false = true := by
  simp [responseBodyEnumerationRisk]

-- Password reset enumeration: reset flow confirms account existence
def passwordResetEnumerationRisk (resetConfirmsEmailExists : Bool)
    (genericResetMessage : Bool) : Bool :=
  resetConfirmsEmailExists && !genericResetMessage

theorem generic_reset_message_safe (confirms : Bool) :
    passwordResetEnumerationRisk confirms true = false := by
  simp [passwordResetEnumerationRisk]

theorem no_confirmation_safe (generic : Bool) :
    passwordResetEnumerationRisk false generic = false := by
  simp [passwordResetEnumerationRisk]

theorem reset_confirms_specific_message_risky :
    passwordResetEnumerationRisk true false = true := by
  simp [passwordResetEnumerationRisk]

-- Rate limiting: unrestricted enumeration attempts allow statistical attack
def rateLimitEnumerationRisk (rateLimitingEnabled : Bool) (attemptsPerMinuteAllowed : Nat)
    (safeAttemptsPerMinute : Nat) : Bool :=
  !rateLimitingEnabled || (safeAttemptsPerMinute < attemptsPerMinuteAllowed)

theorem rate_limiting_within_safe_limit (attempts safe : Nat) (h : attempts ≤ safe) :
    rateLimitEnumerationRisk true attempts safe = false := by
  simp [rateLimitEnumerationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem no_rate_limiting_always_risky (attempts safe : Nat) :
    rateLimitEnumerationRisk false attempts safe = true := by { simp [rateLimitEnumerationRisk]

theorem excessive_rate_limit_risky (attempts safe : Nat) (h : safe < attempts) :
    rateLimitEnumerationRisk true attempts safe = true := by
  simp [rateLimitEnumerationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem zero_attempts_allowed_safe (safe : Nat) :
    rateLimitEnumerationRisk true 0 safe = false := by { simp [rateLimitEnumerationRisk]

-- User harvesting via registration: registration form leaks existing emails
def registrationEnumerationRisk (registrationDisclosesDuplicate : Bool)
    (captchaEnabled : Bool) : Bool :=
  registrationDisclosesDuplicate && !captchaEnabled

theorem registration_generic_safe (captcha : Bool) :
    registrationEnumerationRisk false captcha = false := by
  simp [registrationEnumerationRisk]

theorem captcha_limits_registration_harvest (discloses : Bool) :
    registrationEnumerationRisk discloses true = false := by
  simp [registrationEnumerationRisk]

theorem discloses_without_captcha_risky :
    registrationEnumerationRisk true false = true := by
  simp [registrationEnumerationRisk]

-- Aggregate account enumeration risk
def aggregateAccountEnumerationRisk
    (constantTime : Bool) (variance threshold : Nat)
    (genericMsg sameStatus : Bool)
    (resetConfirms genericReset : Bool)
    (rateLimit : Bool) (attempts safe : Nat) : Nat :=
  (if timingEnumerationRisk constantTime variance threshold then 1 else 0) +
  (if responseBodyEnumerationRisk genericMsg sameStatus then 1 else 0) +
  (if passwordResetEnumerationRisk resetConfirms genericReset then 1 else 0) +
  (if rateLimitEnumerationRisk rateLimit attempts safe then 1 else 0)

theorem fully_hardened_zero_enumeration :
    aggregateAccountEnumerationRisk true 0 10 true true false true true 5 10 = 0 := by
  simp [aggregateAccountEnumerationRisk, timingEnumerationRisk,
        responseBodyEnumerationRisk, passwordResetEnumerationRisk,
        rateLimitEnumerationRisk]

theorem all_enumeration_vectors_max :
    aggregateAccountEnumerationRisk false 50 5 false false true false false 1000 10 = 4 := by
  simp [aggregateAccountEnumerationRisk, timingEnumerationRisk,
        responseBodyEnumerationRisk, passwordResetEnumerationRisk,
        rateLimitEnumerationRisk]

-- Economic: account enumeration detection value (ATO prevention)
def accountEnumerationDetectionValueCents (atoBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (atoBreachCostCents : Int) - (scannerCostCents : Int)

theorem enumeration_detection_profitable (ato scan : Nat) (h : scan < ato) :
    0 < accountEnumerationDetectionValueCents ato scan := by
  simp [accountEnumerationDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem enumeration_break_even (cost : Nat) :
    0 ≤ accountEnumerationDetectionValueCents cost cost := by
  simp [accountEnumerationDetectionValueCents]

-- Fleet ROI: enumeration scan across login surfaces
def accountEnumerationFleetROI (detectionValue : Nat) (loginSurfaces : Nat) : Nat :=
  detectionValue * loginSurfaces

theorem enumeration_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    accountEnumerationFleetROI v s1 ≤ accountEnumerationFleetROI v s2 := by
  simp [accountEnumerationFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_enumeration_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < accountEnumerationFleetROI v s := by
  simp [accountEnumerationFleetROI]
  exact Nat.mul_pos hv hs

end AccountEnumerationRisk
