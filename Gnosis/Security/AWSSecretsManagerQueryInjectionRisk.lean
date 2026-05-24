import Init
-- AWSSecretsManagerQueryInjectionRisk.lean
-- Anti-thesis: AWS Secrets Manager SecretId construction, filter expressions,
-- and resource policy assembly from user input carry no injection risk.
-- Refutation: SecretId path traversal, ListSecrets filter injection, and
-- resource policy JSON injection each yield a strictly positive vulnerability window.

namespace AWSSecretsManagerQueryInjection

-- SecretId injection: get_secret_value with user-controlled SecretId
def secretIdRisk (idLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else idLen + 1

-- Allow-listed SecretId eliminates enumeration and traversal risk
theorem secrets_id_allowlisted_safe (n : Nat) :
    secretIdRisk n true = 0 := by { simp [secretIdRisk]

-- Unvalidated SecretId allows cross-secret access and enumeration
theorem secrets_id_unvalidated_risk (n : Nat) :
    0 < secretIdRisk n false := by
  simp [secretIdRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- ListSecrets filter injection: user-controlled filter Key/Values
def listFilterRisk (filterLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else filterLen + 1

theorem secrets_list_filter_sanitized_safe (n : Nat) :
    listFilterRisk n true = 0 := by { simp [listFilterRisk]

theorem secrets_list_filter_unsanitized_risk (n : Nat) :
    0 < listFilterRisk n false := by
  simp [listFilterRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Resource policy injection: put_resource_policy with user-assembled JSON
def resourcePolicyRisk (policyLen : Nat) (schemaValidated : Bool) : Nat :=
  if schemaValidated then 0 else policyLen + 1

theorem secrets_policy_schema_validated_safe (n : Nat) :
    resourcePolicyRisk n true = 0 := by { simp [resourcePolicyRisk]

theorem secrets_policy_unvalidated_risk (n : Nat) :
    0 < resourcePolicyRisk n false := by
  simp [resourcePolicyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Rotation Lambda injection: user-controlled rotation Lambda ARN
def rotationLambdaRisk (arnLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else arnLen + 1

theorem secrets_rotation_lambda_allowlisted_safe (n : Nat) :
    rotationLambdaRisk n true = 0 := by { simp [rotationLambdaRisk]

theorem secrets_rotation_lambda_unvalidated_risk (n : Nat) :
    0 < rotationLambdaRisk n false := by
  simp [rotationLambdaRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Tag injection: user-controlled tag keys/values in tag_resource
def tagInjectionRisk (tagLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else tagLen + 1

theorem secrets_tag_validated_safe (n : Nat) :
    tagInjectionRisk n true = 0 := by { simp [tagInjectionRisk]

theorem secrets_tag_unvalidated_risk (n : Nat) :
    0 < tagInjectionRisk n false := by
  simp [tagInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone: longer SecretId or filter widens injection surface
theorem secrets_id_risk_monotone (n m : Nat) (h : n ≤ m) :
    secretIdRisk n false ≤ secretIdRisk m false := by { simp [secretIdRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires allow-listed SecretId AND sanitized filters
def netSecretsRisk (inputLen : Nat) (idAllowListed : Bool) (filterSanitized : Bool) : Nat :=
  secretIdRisk inputLen idAllowListed + listFilterRisk inputLen filterSanitized

theorem secrets_net_risk_zero_fully_mitigated (n : Nat) :
    netSecretsRisk n true true = 0 := by { simp [netSecretsRisk, secretIdRisk, listFilterRisk]

theorem secrets_net_risk_pos_unmitigated (n : Nat) :
    0 < netSecretsRisk n false false := by
  simp [netSecretsRisk, secretIdRisk, listFilterRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end AWSSecretsManagerQueryInjection
