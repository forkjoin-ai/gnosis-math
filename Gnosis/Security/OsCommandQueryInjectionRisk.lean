import Init
-- OsCommandQueryInjectionRisk.lean
-- Anti-thesis: Python os.system(), os.popen(), and os.execve() with user
-- input carry no command injection risk.
-- Refutation: os.system(user_cmd) and os.popen(user_cmd) pass input to
-- /bin/sh, yielding a strictly positive injection vulnerability window.

namespace OsCommandQueryInjection

-- os.system() injection: os.system("cmd " + user_input)
def osSystemRisk (inputLen : Nat) (shellEscaped : Bool) : Nat :=
  if shellEscaped then 0 else inputLen + 1

-- shlex.quote() shell-escaping eliminates os.system injection
theorem os_system_escaped_safe (n : Nat) :
    osSystemRisk n true = 0 := by { simp [osSystemRisk]

-- os.system() with unescaped user input is strictly vulnerable
theorem os_system_unescaped_risk (n : Nat) :
    0 < osSystemRisk n false := by
  simp [osSystemRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- os.popen() injection: os.popen("cmd " + user_input)
def osPopenRisk (inputLen : Nat) (shellEscaped : Bool) : Nat :=
  if shellEscaped then 0 else inputLen + 1

theorem os_popen_escaped_safe (n : Nat) :
    osPopenRisk n true = 0 := by { simp [osPopenRisk]

theorem os_popen_unescaped_risk (n : Nat) :
    0 < osPopenRisk n false := by
  simp [osPopenRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- os.execve() injection: path or argv from user input
def osExecveRisk (pathLen : Nat) (pathValidated : Bool) : Nat :=
  if pathValidated then 0 else pathLen + 1

theorem os_execve_validated_safe (n : Nat) :
    osExecveRisk n true = 0 := by { simp [osExecveRisk]

theorem os_execve_unvalidated_risk (n : Nat) :
    0 < osExecveRisk n false := by
  simp [osExecveRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- os.environ injection: user-controlled env var values propagate to child processes
def envPropagationRisk (valueLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else valueLen + 1

theorem os_environ_sanitized_safe (n : Nat) :
    envPropagationRisk n true = 0 := by { simp [envPropagationRisk]

theorem os_environ_unsanitized_risk (n : Nat) :
    0 < envPropagationRisk n false := by
  simp [envPropagationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- os.path operations: os.path.join with user input can escape base directory
def pathJoinRisk (pathLen : Nat) (normalized : Bool) : Nat :=
  if normalized then 0 else pathLen + 1

theorem os_path_normalized_safe (n : Nat) :
    pathJoinRisk n true = 0 := by { simp [pathJoinRisk]

theorem os_path_unnormalized_risk (n : Nat) :
    0 < pathJoinRisk n false := by
  simp [pathJoinRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem os_system_risk_monotone (n m : Nat) (h : n ≤ m) :
    osSystemRisk n false ≤ osSystemRisk m false := by { simp [osSystemRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires shell-escaped os.system AND validated os.execve path
def netOsCommandRisk (inputLen : Nat) (shellEscaped : Bool) (pathValidated : Bool) : Nat :=
  osSystemRisk inputLen shellEscaped + osExecveRisk inputLen pathValidated

theorem os_cmd_net_risk_zero_fully_mitigated (n : Nat) :
    netOsCommandRisk n true true = 0 := by { simp [netOsCommandRisk, osSystemRisk, osExecveRisk]

theorem os_cmd_net_risk_pos_unmitigated (n : Nat) :
    0 < netOsCommandRisk n false false := by
  simp [netOsCommandRisk, osSystemRisk, osExecveRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end OsCommandQueryInjection
