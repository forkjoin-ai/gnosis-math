import Init
-- JWTVerificationBypassRisk.lean
-- Anti-thesis: JWT is a signed standard; as long as the library validates the
-- signature, the token is trustworthy regardless of the algorithm field or
-- key configuration details.
-- Refutation: The `alg:none` attack, algorithm confusion (RS256→HS256 with
-- public key as HMAC secret), absent expiry claims, and kid-header injection
-- all allow forging or replaying tokens without knowing the private key.

namespace Gnosis.Security.JWTVerificationBypassRisk

-- Algorithm whitelist: server must enforce its own algorithm expectation
-- algId: 0 = none (unsigned), 1 = HS256, 2 = RS256, etc.
def algAccepted (whitelistedAlg : Nat) (tokenAlg : Nat) : Bool :=
  if whitelistedAlg = tokenAlg then true else false

theorem alg_match_allowed (a : Nat) :
    algAccepted a a = true := by { simp [algAccepted]

theorem alg_mismatch_rejected (e t : Nat) (h : e ≠ t) :
    algAccepted e t = false := by
  simp [algAccepted]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- alg:none risk: accepting unsigned tokens (tokenAlg = 0) is a vulnerability
def algNoneRisk (rejectNoneAlg : Bool) (tokenAlgId : Nat) : Nat :=
  if rejectNoneAlg then 0
  else if tokenAlgId = 0 then 1
  else 0

theorem none_alg_risk_zero_when_rejected (t : Nat) :
    algNoneRisk true t = 0 := by { simp [algNoneRisk]

theorem none_alg_risk_positive_when_accepted :
    0 < algNoneRisk false 0 := by
  simp [algNoneRisk]

theorem nonzero_alg_not_none_risk (t : Nat) (h : t ≠ 0) :
    algNoneRisk false t = 0 := by
  simp [algNoneRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Algorithm confusion: RS256 public key used as HS256 HMAC secret
-- serverExpectedAlg ≠ tokenAlg and no whitelist = confusion succeeds
def algConfusionRisk (serverExpectedAlg : Nat) (tokenAlg : Nat)
    (algWhitelistEnforced : Bool) : Nat :=
  if algWhitelistEnforced then 0
  else if serverExpectedAlg = tokenAlg then 0
  else 1

theorem alg_confusion_blocked_by_whitelist (s t : Nat) :
    algConfusionRisk s t true = 0 := by { simp [algConfusionRisk]

theorem alg_confusion_safe_when_alg_matches (alg : Nat) (enforced : Bool) :
    algConfusionRisk alg alg enforced = 0 := by
  simp [algConfusionRisk]
  cases enforced <;> simp

theorem alg_confusion_succeeds_without_whitelist (s t : Nat) (h : s ≠ t) :
    0 < algConfusionRisk s t false := by
  simp [algConfusionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Expiry validation: absent or past-not-checked exp claim allows indefinite reuse
def tokenExpiredCheck (expTimestamp : Nat) (nowTimestamp : Nat) : Bool :=
  if expTimestamp ≤ nowTimestamp then true else false

theorem token_expired_when_exp_past (exp now : Nat) (h : exp ≤ now) :
    tokenExpiredCheck exp now = true := by { simp [tokenExpiredCheck, h]

theorem token_valid_when_exp_future (exp now : Nat) (h : now < exp) :
    tokenExpiredCheck exp now = false := by
  simp [tokenExpiredCheck]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Replay risk: missing or unchecked exp claim enables token replay
def replayRisk (hasExpClaim : Bool) (expValidated : Bool) : Nat :=
  if hasExpClaim && expValidated then 0 else 1

theorem no_replay_risk_when_exp_validated :
    replayRisk true true = 0 := by { simp [replayRisk]

theorem replay_risk_no_claim (validated : Bool) :
    0 < replayRisk false validated := by
  simp [replayRisk]
  cases validated <;> simp

theorem replay_risk_not_validated (hasClaim : Bool) :
    0 < replayRisk hasClaim false := by
  simp [replayRisk]
  cases hasClaim <;> simp

-- Clock skew: excessive allowance extends replay window
def clockSkewReplayWindowSecs (allowedSkewSecs : Nat) : Nat :=
  allowedSkewSecs

theorem zero_skew_no_window :
    clockSkewReplayWindowSecs 0 = 0 := by
  simp [clockSkewReplayWindowSecs]

theorem skew_window_monotone (s1 s2 : Nat) (h : s1 ≤ s2) :
    clockSkewReplayWindowSecs s1 ≤ clockSkewReplayWindowSecs s2 := by
  simp [clockSkewReplayWindowSecs]; exact h

-- kid-header injection: unvalidated kid used in key lookup enables path traversal
def kidInjectionRisk (kidValidated : Bool) (kidAllowlisted : Bool) : Nat :=
  if kidValidated && kidAllowlisted then 0 else 1

theorem kid_safe_when_validated_and_allowlisted :
    kidInjectionRisk true true = 0 := by
  simp [kidInjectionRisk]

theorem kid_risky_when_not_validated (allowlisted : Bool) :
    0 < kidInjectionRisk false allowlisted := by
  simp [kidInjectionRisk]
  cases allowlisted <;> simp

theorem kid_risky_when_not_allowlisted (validated : Bool) :
    0 < kidInjectionRisk validated false := by
  simp [kidInjectionRisk]
  cases validated <;> simp

-- Weak HMAC secret: brute-forceable secret negates signature security
def weakSecretRisk (secretEntropyBits : Nat) (minimumEntropyBits : Nat) : Nat :=
  if secretEntropyBits < minimumEntropyBits then 1 else 0

theorem sufficient_entropy_safe (e m : Nat) (h : m ≤ e) :
    weakSecretRisk e m = 0 := by
  simp [weakSecretRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem insufficient_entropy_risky (e m : Nat) (h : e < m) :
    0 < weakSecretRisk e m := by { simp [weakSecretRisk]; exact h

theorem more_entropy_reduces_risk (e1 e2 m : Nat) (he : e1 ≤ e2)
    (h2 : weakSecretRisk e2 m = 0) :
    weakSecretRisk e1 m = 0 := by
  simp [weakSecretRisk] at *; omega

-- Aggregate JWT risk score
def jwtTotalRisk (rejectNoneAlg : Bool) (algWhitelisted : Bool)
    (hasExp : Bool) (expValidated : Bool) (kidValidated : Bool)
    (kidAllowlisted : Bool) (entropyBits : Nat) (minEntropy : Nat) : Nat :=
  algNoneRisk rejectNoneAlg 0 +
  algConfusionRisk 2 1 algWhitelisted +
  replayRisk hasExp expValidated +
  kidInjectionRisk kidValidated kidAllowlisted +
  weakSecretRisk entropyBits minEntropy

theorem jwt_risk_zero_full_controls (minE : Nat) (hE : minE ≤ 256) :
    jwtTotalRisk true true true true true true 256 minE = 0 := by
  simp [jwtTotalRisk, algNoneRisk, algConfusionRisk, replayRisk,
        kidInjectionRisk, weakSecretRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem jwt_risk_positive_no_alg_none_rejection :
    0 < jwtTotalRisk false true true true true true 256 128 := by { simp [jwtTotalRisk, algNoneRisk, algConfusionRisk, replayRisk,
        kidInjectionRisk, weakSecretRisk]

-- Defence: alg whitelist is strictly necessary to prevent alg confusion
theorem alg_whitelist_necessary :
    0 < algConfusionRisk 2 1 false ∧ algConfusionRisk 2 1 true = 0 := by
  constructor
  · simp [algConfusionRisk]
  · simp [algConfusionRisk]

-- Defence: exp claim + validation is strictly necessary to prevent replay
theorem exp_validation_necessary :
    0 < replayRisk false false ∧ replayRisk true true = 0 := by
  simp [replayRisk]

-- Each control independently reduces total risk
theorem alg_none_rejection_reduces_risk (aw he ev kv ka : Bool) (e m : Nat) :
    jwtTotalRisk true aw he ev kv ka e m ≤
    jwtTotalRisk false aw he ev kv ka e m := by
  simp [jwtTotalRisk, algNoneRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end JWTVerificationBypassRisk
