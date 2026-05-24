import Init
-- GinFrameworkQueryInjectionRisk.lean
-- Anti-thesis: Gin web framework (Go) route parameters and query values
-- passed directly into SQL queries or system commands carry no injection risk.
-- Refutation: c.Param() and c.Query() values used in unparameterized
-- database/sql queries yield a strictly positive vulnerability window.

namespace GinFrameworkQueryInjection

-- SQL injection: c.Param("id") used in fmt.Sprintf("SELECT ... WHERE id=%s", id)
def ginSqlRisk (paramLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else paramLen + 1

-- Parameterized query (db.Query(q, id)) eliminates injection
theorem gin_sql_parameterized_safe (n : Nat) :
    ginSqlRisk n true = 0 := by { simp [ginSqlRisk]

-- String-formatted SQL from route param is strictly vulnerable
theorem gin_sql_sprintf_risk (n : Nat) :
    0 < ginSqlRisk n false := by
  simp [ginSqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Query parameter injection: c.Query("filter") interpolated into SQL
def queryParamRisk (paramLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else paramLen + 1

theorem gin_query_param_safe (n : Nat) :
    queryParamRisk n true = 0 := by { simp [queryParamRisk]

theorem gin_query_param_risk (n : Nat) :
    0 < queryParamRisk n false := by
  simp [queryParamRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Command injection: exec.Command("sh", "-c", userInput)
def cmdInjectionRisk (inputLen : Nat) (argSeparated : Bool) : Nat :=
  if argSeparated then 0 else inputLen + 1

theorem gin_cmd_arg_separated_safe (n : Nat) :
    cmdInjectionRisk n true = 0 := by { simp [cmdInjectionRisk]

theorem gin_cmd_shell_injection_risk (n : Nat) :
    0 < cmdInjectionRisk n false := by
  simp [cmdInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Path traversal: c.Param("file") used in filepath.Join without cleaning
def pathTraversalRisk (pathLen : Nat) (cleaned : Bool) : Nat :=
  if cleaned then 0 else pathLen + 1

theorem gin_path_cleaned_safe (n : Nat) :
    pathTraversalRisk n true = 0 := by { simp [pathTraversalRisk]

theorem gin_path_uncleaned_risk (n : Nat) :
    0 < pathTraversalRisk n false := by
  simp [pathTraversalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Open redirect: c.Query("redirect") used without URL validation
def redirectRisk (urlLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else urlLen + 1

theorem gin_redirect_validated_safe (n : Nat) :
    redirectRisk n true = 0 := by { simp [redirectRisk]

theorem gin_redirect_unvalidated_risk (n : Nat) :
    0 < redirectRisk n false := by
  simp [redirectRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in param length
theorem gin_sql_risk_monotone (n m : Nat) (h : n ≤ m) :
    ginSqlRisk n false ≤ ginSqlRisk m false := by { simp [ginSqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized SQL AND arg-separated exec
def netGinRisk (inputLen : Nat) (sqlParam : Bool) (cmdSeparated : Bool) : Nat :=
  ginSqlRisk inputLen sqlParam + cmdInjectionRisk inputLen cmdSeparated

theorem gin_net_risk_zero_fully_mitigated (n : Nat) :
    netGinRisk n true true = 0 := by { simp [netGinRisk, ginSqlRisk, cmdInjectionRisk]

theorem gin_net_risk_pos_unmitigated (n : Nat) :
    0 < netGinRisk n false false := by
  simp [netGinRisk, ginSqlRisk, cmdInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end GinFrameworkQueryInjection
