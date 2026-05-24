import Init
-- AuthorizationBypassRisk.lean
-- Anti-thesis: Authorization is enforced at the frontend layer; users
-- cannot access resources they are not shown links to.
-- Refutation: Direct object references, JWT algorithm confusion, and
-- ACL evaluation order bugs each allow privilege escalation without
-- any UI interaction, because authorization decisions must be enforced
-- at the server on every request.

namespace Gnosis.Security.AuthorizationBypassRisk

-- IDOR via sequential ID: predictable numeric ID lets attacker enumerate resources
def idorSequentialRisk (idRandomized : Bool) (authCheckedPerRequest : Bool) : Nat :=
  if authCheckedPerRequest then 0
  else if idRandomized then 1
  else 2

theorem authz_per_request_check_safe (rand : Bool) :
    idorSequentialRisk rand true = 0 := by { simp [idorSequentialRisk]

theorem authz_sequential_no_check_high_risk :
    idorSequentialRisk false false = 2 := by
  simp [idorSequentialRisk]

-- JWT algorithm confusion: server accepts alg:none or RS256 key as HMAC secret
def jwtAlgConfusionRisk (algVerified : Bool) : Nat :=
  if algVerified then 0 else 1

theorem authz_jwt_alg_verified_safe :
    jwtAlgConfusionRisk true = 0 := by
  simp [jwtAlgConfusionRisk]

theorem authz_jwt_alg_unverified_risk :
    0 < jwtAlgConfusionRisk false := by
  simp [jwtAlgConfusionRisk]

-- ACL evaluation order: deny-by-default vs allow-by-default
def aclEvaluationOrderRisk (denyByDefault : Bool) (explicitDenyPresent : Bool) : Nat :=
  if denyByDefault then 0
  else if explicitDenyPresent then 1
  else 2

theorem authz_deny_by_default_safe (explicit : Bool) :
    aclEvaluationOrderRisk true explicit = 0 := by
  simp [aclEvaluationOrderRisk]

theorem authz_allow_by_default_no_explicit_deny_max_risk :
    aclEvaluationOrderRisk false false = 2 := by
  simp [aclEvaluationOrderRisk]

-- Privilege escalation via role parameter: user can pass admin role in request
def roleParameterRisk (roleServerAssigned : Bool) : Nat :=
  if roleServerAssigned then 0 else 1

theorem authz_server_assigned_role_safe :
    roleParameterRisk true = 0 := by
  simp [roleParameterRisk]

theorem authz_client_supplied_role_risk :
    0 < roleParameterRisk false := by
  simp [roleParameterRisk]

-- Horizontal privilege escalation: user A can access user B's data
def horizontalEscalationRisk (ownershipVerified : Bool) (resourceSensitivity : Nat) : Nat :=
  if ownershipVerified then 0 else resourceSensitivity + 1

theorem authz_ownership_verified_safe (s : Nat) :
    horizontalEscalationRisk true s = 0 := by
  simp [horizontalEscalationRisk]

theorem authz_no_ownership_check_risk (s : Nat) :
    0 < horizontalEscalationRisk false s := by
  simp [horizontalEscalationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- IDOR risk is non-decreasing with resource sensitivity
theorem authz_idor_risk_monotone (s1 s2 : Nat) (h : s1 <= s2) :
    horizontalEscalationRisk false s1 <= horizontalEscalationRisk false s2 := by { simp [horizontalEscalationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires per-request auth check, alg verification, deny-by-default, server roles
def netAuthzBypassRisk (perRequestCheck : Bool) (algVerified : Bool)
    (denyByDefault : Bool) (serverAssigned : Bool) : Nat :=
  idorSequentialRisk false perRequestCheck +
  jwtAlgConfusionRisk algVerified +
  aclEvaluationOrderRisk denyByDefault false +
  roleParameterRisk serverAssigned

theorem authz_net_risk_zero_fully_mitigated :
    netAuthzBypassRisk true true true true = 0 := by { simp [netAuthzBypassRisk, idorSequentialRisk, jwtAlgConfusionRisk,
        aclEvaluationOrderRisk, roleParameterRisk]

theorem authz_net_risk_pos_unmitigated :
    0 < netAuthzBypassRisk false false false false := by
  simp [netAuthzBypassRisk, idorSequentialRisk, jwtAlgConfusionRisk,
        aclEvaluationOrderRisk, roleParameterRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end AuthorizationBypassRisk
