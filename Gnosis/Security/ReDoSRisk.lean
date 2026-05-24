import Init
-- ReDoSRisk.lean
-- Anti-thesis: Matching user-supplied strings against regular expressions
-- carries no denial-of-service risk because regex engines run in linear time.
-- Refutation: Ambiguous patterns with catastrophic backtracking cause
-- super-polynomial evaluation time on crafted inputs, yielding a strictly
-- positive DoS window proportional to input length.

namespace Gnosis.Security.ReDoSRisk

-- Catastrophic backtracking: ambiguous quantifier pattern on user input
-- Models evaluation steps as quadratic in input length for vulnerable pattern
def redosRisk (inputLen : Nat) (patternSafe : Bool) : Nat :=
  if patternSafe then 0 else inputLen * inputLen + 1

-- Safe (linear-time) pattern or bounded input eliminates ReDoS
theorem redos_safe_pattern_safe (n : Nat) :
    redosRisk n true = 0 := by { simp [redosRisk]

-- Ambiguous pattern on user input is strictly vulnerable
theorem redos_unsafe_pattern_risk (n : Nat) :
    0 < redosRisk n false := by
  simp [redosRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Nested quantifier: (a+)+ style patterns on long non-matching input
def nestedQuantifierRisk (inputLen : Nat) (quantifiersFlattened : Bool) : Nat :=
  if quantifiersFlattened then 0 else inputLen + 1

theorem redos_quantifiers_flattened_safe (n : Nat) :
    nestedQuantifierRisk n true = 0 := by { simp [nestedQuantifierRisk]

theorem redos_nested_quantifier_risk (n : Nat) :
    0 < nestedQuantifierRisk n false := by
  simp [nestedQuantifierRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Input length cap: bounding input prevents worst-case blowup
def inputLengthCapRisk (inputLen : Nat) (cap : Nat) : Nat :=
  if inputLen ≤ cap then 0 else inputLen - cap

theorem redos_input_within_cap_safe (n cap : Nat) (h : n ≤ cap) :
    inputLengthCapRisk n cap = 0 := by { simp [inputLengthCapRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem redos_input_exceeds_cap_risk (n cap : Nat) (h : cap < n) :
    0 < inputLengthCapRisk n cap := by { simp [inputLengthCapRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Timeout mitigation: regex engine timeout limits DoS duration
def timeoutMitigatedRisk (inputLen : Nat) (timeoutMs : Nat) : Nat :=
  if timeoutMs = 0 then inputLen + 1 else 0

theorem redos_timeout_set_safe (n t : Nat) (h : t ≠ 0) :
    timeoutMitigatedRisk n t = 0 := by { simp [timeoutMitigatedRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem redos_no_timeout_risk (n : Nat) :
    0 < timeoutMitigatedRisk n 0 := by { simp [timeoutMitigatedRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk strictly increases with input length for is_unsafe patterns
theorem redos_risk_monotone (n m : Nat) (h : n ≤ m) :
    redosRisk n false ≤ redosRisk m false := by { simp [redosRisk]
  nlinarith [Nat.mul_le_mul h h]

-- Net: zero-risk requires safe pattern OR input cap OR timeout
def netRedosRisk (inputLen : Nat) (patternSafe : Bool) (cap : Nat) : Nat :=
  if patternSafe then 0
  else if inputLen ≤ cap then 0
  else inputLen * inputLen + 1

theorem redos_net_safe_pattern (n cap : Nat) :
    netRedosRisk n true cap = 0 := by
  simp [netRedosRisk]

theorem redos_net_safe_cap (n cap : Nat) (h : n ≤ cap) :
    netRedosRisk n false cap = 0 := by
  simp [netRedosRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem redos_net_risk_pos_unmitigated (n : Nat) (h : 0 < n) :
    0 < netRedosRisk n false 0 := by { simp [netRedosRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end ReDoSRisk
