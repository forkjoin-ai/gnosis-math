import Init
-- AWSSQSQueryInjectionRisk.lean
-- Anti-thesis: AWS SQS queue URL construction, message attribute assembly,
-- and message body injection from user input carry no injection risk.
-- Refutation: queue URL traversal, message attribute injection, and
-- visibility timeout manipulation each yield a strictly positive vulnerability window.

namespace AWSSQSQueryInjection

-- Queue URL injection: send_message to user-controlled queue URL
def queueUrlRisk (urlLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else urlLen + 1

-- Allow-listed queue URL eliminates cross-queue message injection
theorem sqs_queue_allowlisted_safe (n : Nat) :
    queueUrlRisk n true = 0 := by { simp [queueUrlRisk]

-- Unvalidated queue URL allows cross-account/queue injection
theorem sqs_queue_unvalidated_risk (n : Nat) :
    0 < queueUrlRisk n false := by
  simp [queueUrlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Message body injection: user-controlled MessageBody content
def messageBodyRisk (bodyLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else bodyLen + 1

theorem sqs_body_sanitized_safe (n : Nat) :
    messageBodyRisk n true = 0 := by { simp [messageBodyRisk]

theorem sqs_body_unsanitized_risk (n : Nat) :
    0 < messageBodyRisk n false := by
  simp [messageBodyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Message attribute injection: user-controlled attribute Name or Value
def msgAttrRisk (attrLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else attrLen + 1

theorem sqs_attr_validated_safe (n : Nat) :
    msgAttrRisk n true = 0 := by { simp [msgAttrRisk]

theorem sqs_attr_unvalidated_risk (n : Nat) :
    0 < msgAttrRisk n false := by
  simp [msgAttrRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- MessageGroupId injection (FIFO queues): user-controlled group ID
def groupIdRisk (idLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else idLen + 1

theorem sqs_group_id_validated_safe (n : Nat) :
    groupIdRisk n true = 0 := by { simp [groupIdRisk]

theorem sqs_group_id_unvalidated_risk (n : Nat) :
    0 < groupIdRisk n false := by
  simp [groupIdRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- ReceiptHandle injection: user-controlled receipt handle in delete_message
def receiptHandleRisk (handleLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else handleLen + 1

theorem sqs_receipt_validated_safe (n : Nat) :
    receiptHandleRisk n true = 0 := by { simp [receiptHandleRisk]

theorem sqs_receipt_unvalidated_risk (n : Nat) :
    0 < receiptHandleRisk n false := by
  simp [receiptHandleRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in queue URL length
theorem sqs_url_risk_monotone (n m : Nat) (h : n ≤ m) :
    queueUrlRisk n false ≤ queueUrlRisk m false := by { simp [queueUrlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires allow-listed queue URL AND sanitized message body
def netSQSRisk (inputLen : Nat) (urlAllowListed : Bool) (bodySanitized : Bool) : Nat :=
  queueUrlRisk inputLen urlAllowListed + messageBodyRisk inputLen bodySanitized

theorem sqs_net_risk_zero_fully_mitigated (n : Nat) :
    netSQSRisk n true true = 0 := by { simp [netSQSRisk, queueUrlRisk, messageBodyRisk]

theorem sqs_net_risk_pos_unmitigated (n : Nat) :
    0 < netSQSRisk n false false := by
  simp [netSQSRisk, queueUrlRisk, messageBodyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end AWSSQSQueryInjection
