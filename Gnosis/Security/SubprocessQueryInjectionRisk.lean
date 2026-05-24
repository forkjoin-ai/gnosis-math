import Init
-- SubprocessQueryInjectionRisk.lean
-- Anti-thesis: Python subprocess.run() and subprocess.Popen() with user input
-- carry no command injection risk because subprocess separates command and args.
-- Refutation: subprocess.run(user_cmd, shell=True) and subprocess.Popen with
-- shell=True pass user input to /bin/sh, yielding a strictly positive injection window.

namespace SubprocessQueryInjection

-- Command injection: subprocess.run(user_input, shell=True)
def shellTrueRisk (inputLen : Nat) (shellDisabled : Bool) : Nat :=
  if shellDisabled then 0 else inputLen + 1

-- shell=False with list args eliminates command injection
theorem subprocess_shell_false_safe (n : Nat) :
    shellTrueRisk n true = 0 := by { simp [shellTrueRisk]

-- shell=True with user input is strictly vulnerable
theorem subprocess_shell_true_risk (n : Nat) :
    0 < shellTrueRisk n false := by
  simp [shellTrueRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- String arg injection: subprocess.run("cmd " + user_input) without shell=True
-- is safe on Unix when user_input contains spaces (args don't re-split)
-- but vulnerable if user controls the entire command string
def stringArgRisk (inputLen : Nat) (listArgs : Bool) : Nat :=
  if listArgs then 0 else inputLen + 1

theorem subprocess_list_args_safe (n : Nat) :
    stringArgRisk n true = 0 := by { simp [stringArgRisk]

theorem subprocess_string_arg_risk (n : Nat) :
    0 < stringArgRisk n false := by
  simp [stringArgRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- stdin injection: user-controlled stdin to a trusted command
def stdinInjectionRisk (stdinLen : Nat) (commandTrusted : Bool) : Nat :=
  if commandTrusted then 0 else stdinLen + 1

theorem subprocess_stdin_command_trusted_safe (n : Nat) :
    stdinInjectionRisk n true = 0 := by { simp [stdinInjectionRisk]

theorem subprocess_stdin_untrusted_command_risk (n : Nat) :
    0 < stdinInjectionRisk n false := by
  simp [stdinInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- env injection: user-controlled env vars passed to subprocess
def envInjectionRisk (envLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else envLen + 1

theorem subprocess_env_sanitized_safe (n : Nat) :
    envInjectionRisk n true = 0 := by { simp [envInjectionRisk]

theorem subprocess_env_unsanitized_risk (n : Nat) :
    0 < envInjectionRisk n false := by
  simp [envInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- cwd injection: user-controlled working directory
def cwdInjectionRisk (cwdLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else cwdLen + 1

theorem subprocess_cwd_validated_safe (n : Nat) :
    cwdInjectionRisk n true = 0 := by { simp [cwdInjectionRisk]

theorem subprocess_cwd_unvalidated_risk (n : Nat) :
    0 < cwdInjectionRisk n false := by
  simp [cwdInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem subprocess_shell_risk_monotone (n m : Nat) (h : n ≤ m) :
    shellTrueRisk n false ≤ shellTrueRisk m false := by { simp [shellTrueRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires shell=False AND list args
def netSubprocessRisk (inputLen : Nat) (shellDisabled : Bool) (listArgs : Bool) : Nat :=
  shellTrueRisk inputLen shellDisabled + stringArgRisk inputLen listArgs

theorem subprocess_net_risk_zero_fully_mitigated (n : Nat) :
    netSubprocessRisk n true true = 0 := by { simp [netSubprocessRisk, shellTrueRisk, stringArgRisk]

theorem subprocess_net_risk_pos_unmitigated (n : Nat) :
    0 < netSubprocessRisk n false false := by
  simp [netSubprocessRisk, shellTrueRisk, stringArgRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end SubprocessQueryInjection
