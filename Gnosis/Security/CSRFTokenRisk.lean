import Init
-- CSRFTokenRisk.lean
-- Anti-thesis: State-changing HTTP endpoints without CSRF token validation
-- carry no risk because browsers enforce same-origin policy for requests.
-- Refutation: Cross-site form submissions and simple-method XHR requests
-- are not blocked by SOP, allowing an attacker page to forge authenticated
-- requests, yielding a strictly positive vulnerability window.

namespace Gnosis.Security.CSRFTokenRisk

-- Missing CSRF token: state-changing endpoint accepts requests without token
def csrfRisk (isStateMutating : Bool) (tokenRequired : Bool) : Nat :=
  if !isStateMutating || tokenRequired then 0 else 1

-- Token required eliminates CSRF on state-mutating endpoints
theorem csrf_token_required_safe :
    csrfRisk true true = 0 := by { simp [csrfRisk]

-- Missing token on state-mutating endpoint is strictly vulnerable
theorem csrf_token_missing_risk :
    0 < csrfRisk true false := by
  simp [csrfRisk]

-- Predictable token: token derived from user ID without entropy
def predictableTokenRisk (tokenEntropy : Nat) (minEntropy : Nat) : Nat :=
  if tokenEntropy ≥ minEntropy then 0 else minEntropy - tokenEntropy + 1

theorem csrf_sufficient_entropy_safe (t m : Nat) (h : t ≥ m) :
    predictableTokenRisk t m = 0 := by
  simp [predictableTokenRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem csrf_insufficient_entropy_risk (t m : Nat) (h : t < m) :
    0 < predictableTokenRisk t m := by { simp [predictableTokenRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Token not validated server-side: token present in form but ignored
def tokenNotValidatedRisk (tokenPresent : Bool) (tokenChecked : Bool) : Nat :=
  if tokenPresent && !tokenChecked then 1 else 0

theorem csrf_token_checked_safe :
    tokenNotValidatedRisk true true = 0 := by
  simp [tokenNotValidatedRisk]

theorem csrf_token_present_unchecked_risk :
    0 < tokenNotValidatedRisk true false := by
  simp [tokenNotValidatedRisk]

-- Double-submit cookie: cookie and request param must match
def doubleSubmitRisk (cookieVal : Nat) (paramVal : Nat) (validated : Bool) : Nat :=
  if validated then 0 else if cookieVal = paramVal then 0 else 1

theorem csrf_double_submit_match_safe (v : Nat) :
    doubleSubmitRisk v v false = 0 := by
  simp [doubleSubmitRisk]

theorem csrf_double_submit_validated_safe (c p : Nat) :
    doubleSubmitRisk c p true = 0 := by
  simp [doubleSubmitRisk]

-- SameSite cookie attribute: Lax/Strict mitigates cross-site requests
def sameSiteMitigatedRisk (isStateMutating : Bool) (sameSiteStrict : Bool) : Nat :=
  if !isStateMutating || sameSiteStrict then 0 else 1

theorem csrf_samesite_strict_safe :
    sameSiteMitigatedRisk true true = 0 := by
  simp [sameSiteMitigatedRisk]

theorem csrf_samesite_none_risk :
    0 < sameSiteMitigatedRisk true false := by
  simp [sameSiteMitigatedRisk]

-- Origin header check: reject requests where Origin ≠ expected host
def originCheckRisk (isStateMutating : Bool) (originChecked : Bool) : Nat :=
  if !isStateMutating || originChecked then 0 else 1

theorem csrf_origin_checked_safe :
    originCheckRisk true true = 0 := by
  simp [originCheckRisk]

theorem csrf_origin_unchecked_risk :
    0 < originCheckRisk true false := by
  simp [originCheckRisk]

-- Net: zero-risk requires token required AND SameSite strict
def netCsrfRisk (isStateMutating : Bool) (tokenRequired : Bool) (sameSiteStrict : Bool) : Nat :=
  csrfRisk isStateMutating tokenRequired + sameSiteMitigatedRisk isStateMutating sameSiteStrict

theorem csrf_net_risk_zero_fully_mitigated :
    netCsrfRisk true true true = 0 := by
  simp [netCsrfRisk, csrfRisk, sameSiteMitigatedRisk]

theorem csrf_net_risk_pos_unmitigated :
    0 < netCsrfRisk true false false := by
  simp [netCsrfRisk, csrfRisk, sameSiteMitigatedRisk]

end CSRFTokenRisk
