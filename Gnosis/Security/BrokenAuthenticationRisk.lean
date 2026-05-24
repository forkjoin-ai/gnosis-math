import Init
-- BrokenAuthenticationRisk.lean
-- Anti-thesis: Once a session is established over HTTPS, the session ID
-- is safe indefinitely because TLS protects the channel.
-- Refutation: Session fixation, token reuse after logout, missing expiry, and
-- low-entropy IDs each yield a strictly positive hijack window independent
-- of transport security, because the vulnerability lives in session lifecycle
-- management, not the channel.

namespace Gnosis.Security.BrokenAuthenticationRisk

-- Session fixation: attacker plants a known session ID before login
def sessionFixationRisk (sessionRotatedOnLogin : Bool) : Nat :=
  if sessionRotatedOnLogin then 0 else 1

theorem auth_session_rotated_safe :
    sessionFixationRisk true = 0 := by { simp [sessionFixationRisk]

theorem auth_session_not_rotated_risk :
    0 < sessionFixationRisk false := by
  simp [sessionFixationRisk]

-- Token reuse: session token valid after explicit logout
def tokenReuseRisk (tokenInvalidatedOnLogout : Bool) : Nat :=
  if tokenInvalidatedOnLogout then 0 else 1

theorem auth_token_invalidated_safe :
    tokenReuseRisk true = 0 := by
  simp [tokenReuseRisk]

theorem auth_token_reuse_risk :
    0 < tokenReuseRisk false := by
  simp [tokenReuseRisk]

-- Weak entropy: short session ID bruteforceable in polynomial time
def weakEntropyRisk (entropyBits : Nat) (minBits : Nat) : Nat :=
  if entropyBits >= minBits then 0 else minBits - entropyBits + 1

theorem auth_sufficient_entropy_safe (e m : Nat) (h : e >= m) :
    weakEntropyRisk e m = 0 := by
  simp [weakEntropyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem auth_insufficient_entropy_risk (e m : Nat) (h : e < m) :
    0 < weakEntropyRisk e m := by { simp [weakEntropyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Missing expiry: session lives forever, enabling long-window replay
def missingExpiryRisk (sessionLifetimeSecs : Nat) (maxLifetimeSecs : Nat) : Nat :=
  if maxLifetimeSecs = 0 then sessionLifetimeSecs + 1
  else if sessionLifetimeSecs <= maxLifetimeSecs then 0
  else sessionLifetimeSecs - maxLifetimeSecs

theorem auth_bounded_session_safe (s m : Nat) (h1 : m ≠ 0) (h2 : s <= m) :
    missingExpiryRisk s m = 0 := by { simp [missingExpiryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem auth_unbounded_session_risk (s : Nat) :
    0 < missingExpiryRisk s 0 := by { simp [missingExpiryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Credential stuffing: reused password + no rate limit = account takeover
def credentialStuffingRisk (rateLimit : Bool) (mfaEnabled : Bool) : Nat :=
  if rateLimit && mfaEnabled then 0
  else if rateLimit || mfaEnabled then 1
  else 2

theorem auth_rate_limit_and_mfa_safe :
    credentialStuffingRisk true true = 0 := by { simp [credentialStuffingRisk]

theorem auth_neither_control_max_risk :
    credentialStuffingRisk false false = 2 := by
  simp [credentialStuffingRisk]

theorem auth_single_control_partial_risk :
    credentialStuffingRisk true false = 1 := by
  simp [credentialStuffingRisk]

-- Risk monotone in entropy deficit
theorem auth_entropy_risk_monotone (e1 e2 m : Nat) (h : e2 <= e1) (hm : e1 < m) :
    weakEntropyRisk e1 m <= weakEntropyRisk e2 m := by
  simp [weakEntropyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires rotation + invalidation + sufficient entropy + bounded lifetime
def netBrokenAuthRisk (rotated : Bool) (invalidated : Bool)
    (entropyBits minBits : Nat) (lifetimeSecs maxSecs : Nat) : Nat :=
  sessionFixationRisk rotated + tokenReuseRisk invalidated +
  weakEntropyRisk entropyBits minBits + missingExpiryRisk lifetimeSecs maxSecs

theorem auth_net_risk_zero_fully_mitigated (e m s mx : Nat)
    (he : e >= m) (hs : mx ≠ 0) (hlt : s <= mx) :
    netBrokenAuthRisk true true e m s mx = 0 := by { simp [netBrokenAuthRisk, sessionFixationRisk, tokenReuseRisk,
        weakEntropyRisk, missingExpiryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem auth_net_risk_pos_unmitigated :
    0 < netBrokenAuthRisk false false 0 128 0 0 := by { simp [netBrokenAuthRisk, sessionFixationRisk, tokenReuseRisk,
        weakEntropyRisk, missingExpiryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end BrokenAuthenticationRisk
