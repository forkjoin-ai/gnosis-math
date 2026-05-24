import Init
-- OAuth2TokenLeakRisk.lean
-- Anti-thesis: OAuth 2.0 access tokens are bearer credentials that expire
-- quickly; even if briefly exposed in a log, they are rotated so frequently
-- that the exposure window is negligible and poses no real security risk.
-- Refutation: Short expiry only helps if rotation actually happens before
-- exploitation. Tokens in URLs appear in: browser history, server access logs,
-- CDN/proxy logs, Referer headers sent to third-party scripts, and postMessage
-- leaks to cross-origin iframes. Any of these can persist the token for its
-- full lifetime. The structural leak — not the lifetime — is the vulnerability.

namespace Gnosis.Security.OAuth2TokenLeakRisk

-- Token in URL: access token passed as query parameter leaks to logs/history
def tokenInURLRisk (tokenInQueryParam : Bool) (accessLogEnabled : Bool)
    (browserHistoryPersisted : Bool) : Bool :=
  tokenInQueryParam && (accessLogEnabled || browserHistoryPersisted)

theorem fragment_binding_no_url_risk (log hist : Bool) :
    tokenInURLRisk false log hist = false := by { simp [tokenInURLRisk]

theorem token_in_url_no_log_no_history_no_risk :
    tokenInURLRisk true false false = false := by
  simp [tokenInURLRisk]

theorem token_in_url_with_log_risky :
    tokenInURLRisk true true false = true := by
  simp [tokenInURLRisk]

theorem token_in_url_with_history_risky :
    tokenInURLRisk true false true = true := by
  simp [tokenInURLRisk]

theorem token_in_url_both_log_and_history_risky :
    tokenInURLRisk true true true = true := by
  simp [tokenInURLRisk]

-- Log exposure: tokens written to structured or plain-text logs
def logExposureRisk (tokenLoggedInPlaintext : Bool) (logRetentionDays : Nat)
    (logAccessControlled : Bool) : Bool :=
  tokenLoggedInPlaintext && logRetentionDays > 0 && !logAccessControlled

theorem no_plaintext_logging_no_log_exposure (days : Nat) (acl : Bool) :
    logExposureRisk false days acl = false := by
  simp [logExposureRisk]

theorem zero_retention_no_log_exposure (logged acl : Bool) :
    logExposureRisk logged 0 acl = false := by
  simp [logExposureRisk]

theorem access_controlled_logs_no_exposure (logged : Bool) (days : Nat) :
    logExposureRisk logged days true = false := by
  simp [logExposureRisk]
  cases logged <;> simp

theorem plaintext_logged_retained_uncontrolled_risky (days : Nat) (hd : 0 < days) :
    logExposureRisk true days false = true := by
  simp [logExposureRisk, hd]

-- Referer header leak: token in URL sent via Referer to third-party resources
def refererLeakRisk (tokenInURL : Bool) (referrerPolicyStrict : Bool)
    (thirdPartyResourcesLoaded : Bool) : Bool :=
  tokenInURL && !referrerPolicyStrict && thirdPartyResourcesLoaded

theorem strict_referrer_policy_prevents_leak (inURL third : Bool) :
    refererLeakRisk inURL true third = false := by
  simp [refererLeakRisk]
  cases inURL <;> cases third <;> simp

theorem no_third_party_no_referer_leak (inURL strict : Bool) :
    refererLeakRisk inURL strict false = false := by
  simp [refererLeakRisk]
  cases inURL <;> cases strict <;> simp

theorem token_in_url_lax_policy_third_party_leaks :
    refererLeakRisk true false true = true := by
  simp [refererLeakRisk]

-- postMessage leak: token sent via postMessage without origin validation
def postMessageLeakRisk (originValidated : Bool) (wildcardTargetOrigin : Bool) : Bool :=
  !originValidated || wildcardTargetOrigin

theorem origin_validated_no_wildcard_safe :
    postMessageLeakRisk true false = false := by
  simp [postMessageLeakRisk]

theorem wildcard_always_risky (validated : Bool) :
    postMessageLeakRisk validated true = true := by
  simp [postMessageLeakRisk]
  cases validated <;> simp

theorem no_validation_risky (wildcard : Bool) :
    postMessageLeakRisk false wildcard = true := by
  simp [postMessageLeakRisk]

-- Token lifetime: longer-lived tokens increase exposure window
def tokenExposureWindowSecs (tokenLifetimeSecs : Nat) (detectedAt : Nat) : Nat :=
  if detectedAt ≤ tokenLifetimeSecs then tokenLifetimeSecs - detectedAt else 0

theorem immediate_detection_zero_window (lifetime : Nat) :
    tokenExposureWindowSecs lifetime lifetime = 0 := by
  simp [tokenExposureWindowSecs]

theorem undetected_token_full_lifetime (lifetime : Nat) :
    tokenExposureWindowSecs lifetime 0 = lifetime := by
  simp [tokenExposureWindowSecs]

theorem longer_lifetime_wider_window (l1 l2 d : Nat) (h : l1 ≤ l2) :
    tokenExposureWindowSecs l1 d ≤ tokenExposureWindowSecs l2 d := by
  simp [tokenExposureWindowSecs]
  split_ifs with h1 h2
  · omega
  · omega
  · omega
  · omega

-- Refresh token theft: stealing long-lived refresh token enables persistent access
def refreshTokenTheftRisk (refreshTokenInStorage : Bool) (storageSandboxed : Bool)
    (bindingPresent : Bool) : Bool :=
  refreshTokenInStorage && !storageSandboxed && !bindingPresent

theorem sandboxed_storage_prevents_theft (inStorage binding : Bool) :
    refreshTokenTheftRisk inStorage true binding = false := by
  simp [refreshTokenTheftRisk]
  cases inStorage <;> cases binding <;> simp

theorem token_binding_prevents_theft (inStorage sandboxed : Bool) :
    refreshTokenTheftRisk inStorage sandboxed true = false := by
  simp [refreshTokenTheftRisk]
  cases inStorage <;> cases sandboxed <;> simp

theorem refresh_token_exposed_unsandboxed_unbound_risky :
    refreshTokenTheftRisk true false false = true := by
  simp [refreshTokenTheftRisk]

-- Aggregate OAuth2 token leak risk
def aggregateTokenLeakRisk
    (tokenInQP logEnabled histPersisted : Bool)
    (logged : Bool) (retDays : Nat) (logACL : Bool)
    (refPolicy thirdParty : Bool)
    (originVal wildcard : Bool) : Nat :=
  (if tokenInURLRisk tokenInQP logEnabled histPersisted then 1 else 0) +
  (if logExposureRisk logged retDays logACL then 1 else 0) +
  (if refererLeakRisk tokenInQP refPolicy thirdParty then 1 else 0) +
  (if postMessageLeakRisk originVal wildcard then 1 else 0)

theorem fully_hardened_zero_token_leak_risk :
    aggregateTokenLeakRisk false false false false 0 true true false true false = 0 := by
  simp [aggregateTokenLeakRisk, tokenInURLRisk, logExposureRisk,
        refererLeakRisk, postMessageLeakRisk]

theorem all_vectors_max_token_leak_risk :
    aggregateTokenLeakRisk true true true true 30 false false true false true = 4 := by
  simp [aggregateTokenLeakRisk, tokenInURLRisk, logExposureRisk,
        refererLeakRisk, postMessageLeakRisk]

-- Economic: breach cost from token exposure
def tokenLeakBreachCostCents (exposureWindowSecs : Nat) (costPerSecCents : Nat) : Nat :=
  exposureWindowSecs * costPerSecCents

theorem zero_window_zero_cost (cps : Nat) :
    tokenLeakBreachCostCents 0 cps = 0 := by
  simp [tokenLeakBreachCostCents]

theorem cost_scales_with_window (w1 w2 cps : Nat) (h : w1 ≤ w2) :
    tokenLeakBreachCostCents w1 cps ≤ tokenLeakBreachCostCents w2 cps := by
  simp [tokenLeakBreachCostCents]
  exact Nat.mul_le_mul_right cps h

theorem positive_window_and_rate_positive_cost (w cps : Nat) (hw : 0 < w) (hc : 0 < cps) :
    0 < tokenLeakBreachCostCents w cps := by
  simp [tokenLeakBreachCostCents]
  exact Nat.mul_pos hw hc

-- Scanner ROI: finding token-in-URL patterns before breach
def tokenLeakScannerROI (breachCostCents : Nat) (scannerCostCents : Nat) : Int :=
  (breachCostCents : Int) - (scannerCostCents : Int)

theorem scanner_roi_positive_when_breach_exceeds_cost (b s : Nat) (h : s < b) :
    0 < tokenLeakScannerROI b s := by
  simp [tokenLeakScannerROI]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem scanner_roi_nonneg_at_break_even (b : Nat) :
    0 ≤ tokenLeakScannerROI b b := by
  simp [tokenLeakScannerROI]

end OAuth2TokenLeakRisk
