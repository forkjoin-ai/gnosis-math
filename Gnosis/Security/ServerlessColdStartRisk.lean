import Init
-- ServerlessColdStartRisk.lean
-- Anti-thesis: Serverless functions are stateless and ephemeral, so they present
-- a smaller attack surface than long-running servers; cold-start isolation is
-- a security feature, not a risk.
-- Refutation: The cold-start initialisation window loads secrets and config
-- before the runtime sandbox is fully locked; event-injection via trigger
-- payloads bypasses IAM at the function level; and cross-invocation data leakage
-- across warm re-use violates isolation assumptions.

namespace Gnosis.Security.ServerlessColdStartRisk

-- Cold-start init window: vulnerable before handler is locked
def coldStartVulnerabilityWindowMs (coldStart : Bool) (initDurationMs : Nat) : Nat :=
  if coldStart then initDurationMs else 0

theorem cold_start_exposes_init_window (d : Nat) (h : 0 < d) :
    0 < coldStartVulnerabilityWindowMs true d := by { simp [coldStartVulnerabilityWindowMs]; exact h

theorem warm_start_no_init_window (d : Nat) :
    coldStartVulnerabilityWindowMs false d = 0 := by
  simp [coldStartVulnerabilityWindowMs]

-- Secrets loaded during init are accessible in the vulnerability window
def secretsExposedDuringInit (windowMs : Nat) (secretCount : Nat) : Nat :=
  if windowMs = 0 then 0 else secretCount

theorem init_window_exposes_secrets (w s : Nat) (hw : 0 < w) (hs : 0 < s) :
    0 < secretsExposedDuringInit w s := by
  unfold secretsExposedDuringInit
  split_ifs with h0
  · omega
  · exact hs

theorem no_window_no_secrets (s : Nat) :
    secretsExposedDuringInit 0 s = 0 := by
  simp [secretsExposedDuringInit]

theorem secrets_exposed_monotone_in_count (w s1 s2 : Nat) (hs : s1 ≤ s2) (hw : 0 < w) :
    secretsExposedDuringInit w s1 ≤ secretsExposedDuringInit w s2 := by
  unfold secretsExposedDuringInit
  split_ifs with h0
  · omega
  · exact hs

-- Event-injection: malicious trigger payload bypasses perimeter controls
def eventInjectionRisk (payloadValidated : Bool) (triggerSources : Nat) : Nat :=
  if payloadValidated then 0 else triggerSources

theorem validated_events_safe (n : Nat) :
    eventInjectionRisk true n = 0 := by
  simp [eventInjectionRisk]

theorem unvalidated_events_risk_scales_with_sources (n : Nat) (h : 0 < n) :
    0 < eventInjectionRisk false n := by
  simp [eventInjectionRisk]; exact h

theorem more_trigger_sources_more_risk (n1 n2 : Nat) (h : n1 ≤ n2) :
    eventInjectionRisk false n1 ≤ eventInjectionRisk false n2 := by
  simp [eventInjectionRisk]; exact h

-- Function isolation: cross-invocation data leakage via warm container reuse
def crossInvocationLeakRisk (containerReused : Bool) (globalStateSize : Nat) : Nat :=
  if containerReused then globalStateSize else 0

theorem reused_container_leaks_state (s : Nat) (h : 0 < s) :
    0 < crossInvocationLeakRisk true s := by
  simp [crossInvocationLeakRisk]; exact h

theorem fresh_container_no_leakage (s : Nat) :
    crossInvocationLeakRisk false s = 0 := by
  simp [crossInvocationLeakRisk]

-- IAM over-permissioning: functions often share execution roles
def iamOverpermissionRisk (permissions : Nat) (requiredPermissions : Nat) : Nat :=
  if permissions ≤ requiredPermissions then 0 else permissions - requiredPermissions

theorem iam_least_privilege_safe (p r : Nat) (h : p ≤ r) :
    iamOverpermissionRisk p r = 0 := by
  simp [iamOverpermissionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem iam_excess_permissions_risky (p r : Nat) (h : r < p) :
    0 < iamOverpermissionRisk p r := by { simp [iamOverpermissionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem iam_risk_grows_with_excess (p r : Nat) (h : r < p) :
    iamOverpermissionRisk p r = p - r := by { simp [iamOverpermissionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Dependency injection in init: unvetted packages loaded at cold start
def initDependencyRisk (packageCount : Nat) (unpinnedPackages : Nat) : Nat :=
  min unpinnedPackages packageCount

theorem all_pinned_no_init_dep_risk (n : Nat) :
    initDependencyRisk n 0 = 0 := by { simp [initDependencyRisk]

theorem unpinned_deps_counted (p u : Nat) (h : u ≤ p) :
    initDependencyRisk p u = u := by
  simp [initDependencyRisk]
  exact Nat.min_eq_right h

-- Timeout: long-running functions expand side-channel window
def timeoutExposureRisk (timeoutMs : Nat) (sidechannelThresholdMs : Nat) : Nat :=
  if timeoutMs ≤ sidechannelThresholdMs then 0 else timeoutMs - sidechannelThresholdMs

theorem short_timeout_safe (t s : Nat) (h : t ≤ s) :
    timeoutExposureRisk t s = 0 := by
  simp [timeoutExposureRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem long_timeout_exposes_channel (t s : Nat) (h : s < t) :
    0 < timeoutExposureRisk t s := by { simp [timeoutExposureRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Aggregate serverless risk score
def serverlessTotalRisk (coldStartMs : Nat) (secretCount : Nat) (triggerSources : Nat)
    (globalState : Nat) (excessPerms : Nat) : Nat :=
  secretsExposedDuringInit coldStartMs secretCount +
  eventInjectionRisk false triggerSources +
  crossInvocationLeakRisk true globalState +
  excessPerms

theorem serverless_risk_zero_ideal_config :
    serverlessTotalRisk 0 5 0 0 0 = 0 := by { simp [serverlessTotalRisk, secretsExposedDuringInit, eventInjectionRisk,
        crossInvocationLeakRisk]

theorem serverless_risk_positive_with_cold_start_secrets (s t g p : Nat)
    (hs : 0 < s) (ht : 0 < t) :
    0 < serverlessTotalRisk 1 s t g p := by
  simp [serverlessTotalRisk, secretsExposedDuringInit, eventInjectionRisk,
        crossInvocationLeakRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Cold-start mitigation (windowMs = 0) reduces aggregate risk
theorem cold_start_mitigation_reduces_risk (s t g p : Nat) :
    serverlessTotalRisk 0 s t g p ≤ serverlessTotalRisk 1 s t g p := by { simp [serverlessTotalRisk, secretsExposedDuringInit, eventInjectionRisk,
        crossInvocationLeakRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- IAM hardening reduces risk
theorem iam_hardening_reduces_risk (ms sec trig glob e1 e2 : Nat) (h : e1 ≤ e2) :
    serverlessTotalRisk ms sec trig glob e1 ≤ serverlessTotalRisk ms sec trig glob e2 := by { simp [serverlessTotalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end ServerlessColdStartRisk
