import Init
-- StepFunctionsQueryInjectionRisk.lean
-- Anti-thesis: user-assembled AWS Step Functions state machine definitions
-- cannot introduce injection vulnerabilities.
-- Refutation: we prove that JSON state machine assembly from user input,
-- unvalidated ARNs, JSONPath expressions, and Choice conditions each yield
-- a strictly positive vulnerability window.

namespace StepFunctionsQueryInjection

-- State machine definition injection: user input assembled into JSON definition
def stateMachineDefRisk (inputLen : Nat) (jsonValidated : Bool) : Nat :=
  if jsonValidated then 0 else inputLen + 1

-- Schema-validated JSON state machine definition is safe
theorem sfn_json_validated_zero_risk (n : Nat) :
    stateMachineDefRisk n true = 0 := by { simp [stateMachineDefRisk]

-- User-assembled JSON state machine definition is strictly vulnerable
theorem sfn_json_unvalidated_risk (n : Nat) :
    0 < stateMachineDefRisk n false := by
  simp [stateMachineDefRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Resource ARN injection in Task states (user-controlled task Resource)
def arnInjectionRisk (inputLen : Nat) (arnAllowListed : Bool) : Nat :=
  if arnAllowListed then 0 else inputLen + 1

-- Allow-listed ARN set eliminates Task resource injection
theorem sfn_arn_allowlisted_safe (n : Nat) :
    arnInjectionRisk n true = 0 := by { simp [arnInjectionRisk]

-- Unvalidated Resource ARN from user input is strictly vulnerable
theorem sfn_arn_unvalidated_risk (n : Nat) :
    0 < arnInjectionRisk n false := by
  simp [arnInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- JSONPath expression injection ($.field assembled from user-controlled path)
def jsonpathRisk (pathLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else pathLen + 1

-- Unsanitized JSONPath expression from user input is injectable
theorem sfn_jsonpath_injection_possible (n : Nat) :
    0 < jsonpathRisk n false := by { simp [jsonpathRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Sanitized JSONPath expression is safe
theorem sfn_jsonpath_safe_sanitized (n : Nat) :
    jsonpathRisk n true = 0 := by { simp [jsonpathRisk]

-- Wait state timestamp injection: user-controlled HeartbeatSeconds or Timestamp
def waitStateRisk (timestampLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else timestampLen + 1

-- Unvalidated timestamp field yields strictly positive risk
theorem sfn_wait_timestamp_unvalidated_risk (n : Nat) :
    0 < waitStateRisk n false := by
  simp [waitStateRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Choice state condition injection: Variable/StringEquals from user input
def choiceRisk (condLen : Nat) (stateCount : Nat) (validated : Bool) : Nat :=
  if validated then 0 else condLen + stateCount

-- Unvalidated Choice condition from user input is injectable when nonempty
theorem sfn_choice_condition_unvalidated (n k : Nat) (hn : 0 < n) :
    0 < choiceRisk n k false := by { simp [choiceRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- More Choice states widen the injection surface
theorem sfn_choice_risk_monotone_states (n k1 k2 : Nat) (h : k1 ≤ k2) :
    choiceRisk n k1 false ≤ choiceRisk n k2 false := by { simp [choiceRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Map state iterator injection: InputPath/ItemsPath from user-controlled JSONPath
def mapStateRisk (iteratorInputLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else iteratorInputLen + 1

-- Unvalidated Map iterator InputPath is strictly vulnerable
theorem sfn_map_iterator_unvalidated_risk (n : Nat) :
    0 < mapStateRisk n false := by { simp [mapStateRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Parallel state injection amplifies risk across branches
def parallelStateRisk (inputLen : Nat) (branches : Nat) (validated : Bool) : Nat :=
  if validated then 0 else inputLen + branches

-- Parallel branches with unvalidated input are strictly vulnerable
theorem sfn_parallel_amplifies_risk (n b : Nat) (hb : 0 < b) :
    0 < parallelStateRisk n b false := by { simp [parallelStateRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Validated Parallel state eliminates injection
theorem sfn_parallel_safe_validated (n b : Nat) :
    parallelStateRisk n b true = 0 := by { simp [parallelStateRisk]

-- Net: zero-risk path requires schema-validated JSON AND allow-listed ARNs
def netSfnRisk (inputLen : Nat) (validated : Bool) (arnAllowListed : Bool) : Nat :=
  stateMachineDefRisk inputLen validated + arnInjectionRisk inputLen arnAllowListed

theorem sfn_net_risk_zero_fully_mitigated (n : Nat) :
    netSfnRisk n true true = 0 := by
  simp [netSfnRisk, stateMachineDefRisk, arnInjectionRisk]

theorem sfn_net_risk_pos_unmitigated (n : Nat) :
    0 < netSfnRisk n false false := by
  simp [netSfnRisk, stateMachineDefRisk, arnInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end StepFunctionsQueryInjection
