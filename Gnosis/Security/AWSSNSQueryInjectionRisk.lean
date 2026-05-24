import Init
-- AWSSNSQueryInjectionRisk.lean
-- Anti-thesis: AWS SNS topic ARN construction, message attribute assembly,
-- and subscription filter policy injection from user input carry no injection risk.
-- Refutation: topic ARN traversal, filter policy injection, and endpoint
-- injection each yield a strictly positive vulnerability window.

namespace AWSSNSQueryInjection

-- Topic ARN injection: publish to user-controlled topic ARN
def topicArnRisk (arnLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else arnLen + 1

-- Allow-listed topic ARN eliminates cross-topic publish
theorem sns_topic_allowlisted_safe (n : Nat) :
    topicArnRisk n true = 0 := by { simp [topicArnRisk]

-- Unvalidated topic ARN allows cross-account/topic injection
theorem sns_topic_unvalidated_risk (n : Nat) :
    0 < topicArnRisk n false := by
  simp [topicArnRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Message attribute injection: user-controlled attribute Name or Value
def messageAttrRisk (attrLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else attrLen + 1

theorem sns_attr_sanitized_safe (n : Nat) :
    messageAttrRisk n true = 0 := by { simp [messageAttrRisk]

theorem sns_attr_unsanitized_risk (n : Nat) :
    0 < messageAttrRisk n false := by
  simp [messageAttrRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Subscription filter policy injection: user-controlled JSON filter policy
def filterPolicyRisk (policyLen : Nat) (schemaValidated : Bool) : Nat :=
  if schemaValidated then 0 else policyLen + 1

theorem sns_filter_policy_validated_safe (n : Nat) :
    filterPolicyRisk n true = 0 := by { simp [filterPolicyRisk]

theorem sns_filter_policy_unvalidated_risk (n : Nat) :
    0 < filterPolicyRisk n false := by
  simp [filterPolicyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Endpoint injection: subscribe with user-controlled HTTP/email endpoint
def endpointRisk (endpointLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else endpointLen + 1

theorem sns_endpoint_validated_safe (n : Nat) :
    endpointRisk n true = 0 := by { simp [endpointRisk]

theorem sns_endpoint_unvalidated_risk (n : Nat) :
    0 < endpointRisk n false := by
  simp [endpointRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Subject injection: user-controlled message Subject field
def subjectRisk (subjectLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else subjectLen + 1

theorem sns_subject_sanitized_safe (n : Nat) :
    subjectRisk n true = 0 := by { simp [subjectRisk]

theorem sns_subject_unsanitized_risk (n : Nat) :
    0 < subjectRisk n false := by
  simp [subjectRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in topic ARN length
theorem sns_arn_risk_monotone (n m : Nat) (h : n ≤ m) :
    topicArnRisk n false ≤ topicArnRisk m false := by { simp [topicArnRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires allow-listed ARN AND sanitized message attributes
def netSNSRisk (inputLen : Nat) (arnAllowListed : Bool) (attrSanitized : Bool) : Nat :=
  topicArnRisk inputLen arnAllowListed + messageAttrRisk inputLen attrSanitized

theorem sns_net_risk_zero_fully_mitigated (n : Nat) :
    netSNSRisk n true true = 0 := by { simp [netSNSRisk, topicArnRisk, messageAttrRisk]

theorem sns_net_risk_pos_unmitigated (n : Nat) :
    0 < netSNSRisk n false false := by
  simp [netSNSRisk, topicArnRisk, messageAttrRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end AWSSNSQueryInjection
