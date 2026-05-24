import Init
-- NodeChildProcessQueryInjectionRisk.lean
-- Anti-thesis: Node.js child_process.exec() and execSync() with user-controlled
-- command strings carry no command injection risk.
-- Refutation: exec(user_cmd) passes the command to /bin/sh, enabling arbitrary
-- command chaining, yielding a strictly positive injection vulnerability window.

namespace NodeChildProcessQueryInjection

-- Command injection: exec("cmd " + userInput) passes to /bin/sh
def execShellRisk (inputLen : Nat) (argsSeparated : Bool) : Nat :=
  if argsSeparated then 0 else inputLen + 1

-- execFile() with array args (no shell) eliminates injection
theorem node_execfile_array_safe (n : Nat) :
    execShellRisk n true = 0 := by { simp [execShellRisk]

-- exec() with string input is strictly vulnerable to shell injection
theorem node_exec_string_risk (n : Nat) :
    0 < execShellRisk n false := by
  simp [execShellRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- execSync() injection: execSync("cmd " + userInput) blocks but still injects
def execSyncRisk (inputLen : Nat) (argsSeparated : Bool) : Nat :=
  if argsSeparated then 0 else inputLen + 1

theorem node_execsync_array_safe (n : Nat) :
    execSyncRisk n true = 0 := by { simp [execSyncRisk]

theorem node_execsync_string_risk (n : Nat) :
    0 < execSyncRisk n false := by
  simp [execSyncRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- spawn() with shell:true is equivalent to exec() risk
def spawnShellRisk (inputLen : Nat) (shellDisabled : Bool) : Nat :=
  if shellDisabled then 0 else inputLen + 1

theorem node_spawn_shell_disabled_safe (n : Nat) :
    spawnShellRisk n true = 0 := by { simp [spawnShellRisk]

theorem node_spawn_shell_enabled_risk (n : Nat) :
    0 < spawnShellRisk n false := by
  simp [spawnShellRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- env injection: user-controlled env vars in child process options
def envInjectionRisk (envLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else envLen + 1

theorem node_env_sanitized_safe (n : Nat) :
    envInjectionRisk n true = 0 := by { simp [envInjectionRisk]

theorem node_env_unsanitized_risk (n : Nat) :
    0 < envInjectionRisk n false := by
  simp [envInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- cwd injection: user-controlled working directory in child process
def cwdInjectionRisk (cwdLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else cwdLen + 1

theorem node_cwd_validated_safe (n : Nat) :
    cwdInjectionRisk n true = 0 := by { simp [cwdInjectionRisk]

theorem node_cwd_unvalidated_risk (n : Nat) :
    0 < cwdInjectionRisk n false := by
  simp [cwdInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem node_exec_risk_monotone (n m : Nat) (h : n ≤ m) :
    execShellRisk n false ≤ execShellRisk m false := by { simp [execShellRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires separated args AND disabled shell
def netNodeChildRisk (inputLen : Nat) (argsSeparated : Bool) (shellDisabled : Bool) : Nat :=
  execShellRisk inputLen argsSeparated + spawnShellRisk inputLen shellDisabled

theorem node_child_net_risk_zero_fully_mitigated (n : Nat) :
    netNodeChildRisk n true true = 0 := by { simp [netNodeChildRisk, execShellRisk, spawnShellRisk]

theorem node_child_net_risk_pos_unmitigated (n : Nat) :
    0 < netNodeChildRisk n false false := by
  simp [netNodeChildRisk, execShellRisk, spawnShellRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end NodeChildProcessQueryInjection
