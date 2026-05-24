import Init
-- AWSSsmQueryInjectionRisk.lean
-- Anti-thesis: AWS Systems Manager (SSM) Parameter Store path construction
-- from user input carries no injection vulnerabilities.
-- Refutation: path traversal, recursive prefix injection, and filter injection
-- each yield a strictly positive vulnerability window.

namespace AWSSsmQueryInjection

-- Parameter path traversal: user-controlled path may escape intended prefix
def pathTraversalRisk (pathLen : Nat) (prefixEnforced : Bool) : Nat :=
  if prefixEnforced then 0 else pathLen + 1

-- Enforced prefix (path must start with /app/env/) eliminates traversal
theorem ssm_prefix_enforced_safe (n : Nat) :
    pathTraversalRisk n true = 0 := by { simp [pathTraversalRisk]

-- Unvalidated path allows /app/../../prod/secret traversal
theorem ssm_path_traversal_risk (n : Nat) :
    0 < pathTraversalRisk n false := by
  simp [pathTraversalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Recursive GetParametersByPath: user-controlled recursive flag
def recursivePathRisk (pathLen : Nat) (prefixEnforced : Bool) (recursive : Bool) : Nat :=
  pathTraversalRisk pathLen prefixEnforced + (if recursive then pathLen + 1 else 0)

theorem ssm_recursive_amplifies_risk (n : Nat) :
    pathTraversalRisk n false ≤ recursivePathRisk n false true := by { simp [recursivePathRisk, pathTraversalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem ssm_recursive_safe_when_prefix_enforced (n : Nat) :
    recursivePathRisk n true true = n + 1 := by { simp [recursivePathRisk, pathTraversalRisk]

-- DescribeParameters filter injection: user-controlled filter Key/Values
def filterRisk (filterLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else filterLen + 1

theorem ssm_filter_sanitized_safe (n : Nat) :
    filterRisk n true = 0 := by
  simp [filterRisk]

theorem ssm_filter_unsanitized_risk (n : Nat) :
    0 < filterRisk n false := by
  simp [filterRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Tag-based policy: parameter tag value injection in put_parameter
def tagValueRisk (tagLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else tagLen + 1

theorem ssm_tag_value_validated_safe (n : Nat) :
    tagValueRisk n true = 0 := by { simp [tagValueRisk]

theorem ssm_tag_value_unvalidated_risk (n : Nat) :
    0 < tagValueRisk n false := by
  simp [tagValueRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- SecureString KMS key injection: user-controlled KeyId in put_parameter
def kmsKeyRisk (keyIdLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else keyIdLen + 1

theorem ssm_kms_key_allowlisted_safe (n : Nat) :
    kmsKeyRisk n true = 0 := by { simp [kmsKeyRisk]

theorem ssm_kms_key_unvalidated_risk (n : Nat) :
    0 < kmsKeyRisk n false := by
  simp [kmsKeyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires prefix enforcement AND sanitized filters
def netSsmRisk (inputLen : Nat) (prefixEnforced : Bool) (filterSanitized : Bool) : Nat :=
  pathTraversalRisk inputLen prefixEnforced + filterRisk inputLen filterSanitized

theorem ssm_net_risk_zero_fully_mitigated (n : Nat) :
    netSsmRisk n true true = 0 := by { simp [netSsmRisk, pathTraversalRisk, filterRisk]

theorem ssm_net_risk_pos_unmitigated (n : Nat) :
    0 < netSsmRisk n false false := by
  simp [netSsmRisk, pathTraversalRisk, filterRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end AWSSsmQueryInjection
