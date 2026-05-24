import Init
-- EchoFrameworkQueryInjectionRisk.lean
-- Anti-thesis: Echo web framework (Go) path parameters obtained via c.Param()
-- and query values via c.QueryParam() used in downstream operations
-- carry no injection risk.
-- Refutation: unparameterized use of Echo path/query params in SQL,
-- templates, or system calls yields a strictly positive vulnerability window.

namespace EchoFrameworkQueryInjection

-- SQL injection: c.Param("id") used in db.Query(fmt.Sprintf(...))
def echoParamSqlRisk (paramLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else paramLen + 1

-- Parameterized query eliminates Echo param SQL injection
theorem echo_param_parameterized_safe (n : Nat) :
    echoParamSqlRisk n true = 0 := by { simp [echoParamSqlRisk]

-- String-formatted SQL from Echo path param is strictly vulnerable
theorem echo_param_sprintf_risk (n : Nat) :
    0 < echoParamSqlRisk n false := by
  simp [echoParamSqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Query param injection: c.QueryParam("search") in SQL WHERE clause
def echoQueryParamRisk (queryLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else queryLen + 1

theorem echo_query_param_parameterized_safe (n : Nat) :
    echoQueryParamRisk n true = 0 := by { simp [echoQueryParamRisk]

theorem echo_query_param_unparameterized_risk (n : Nat) :
    0 < echoQueryParamRisk n false := by
  simp [echoQueryParamRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Template injection: text/template with user-controlled data (not html/template)
def templateInjectionRisk (dataLen : Nat) (htmlTemplate : Bool) : Nat :=
  if htmlTemplate then 0 else dataLen + 1

theorem echo_html_template_safe (n : Nat) :
    templateInjectionRisk n true = 0 := by { simp [templateInjectionRisk]

theorem echo_text_template_risk (n : Nat) :
    0 < templateInjectionRisk n false := by
  simp [templateInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Form value injection: c.FormValue used in downstream SQL
def formValueRisk (valueLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else valueLen + 1

theorem echo_form_value_sanitized_safe (n : Nat) :
    formValueRisk n true = 0 := by { simp [formValueRisk]

theorem echo_form_value_unsanitized_risk (n : Nat) :
    0 < formValueRisk n false := by
  simp [formValueRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Multipart file name injection: c.FormFile used with is_unsafe filename
def fileNameRisk (nameLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else nameLen + 1

theorem echo_filename_sanitized_safe (n : Nat) :
    fileNameRisk n true = 0 := by { simp [fileNameRisk]

theorem echo_filename_unsanitized_risk (n : Nat) :
    0 < fileNameRisk n false := by
  simp [fileNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in param length
theorem echo_param_risk_monotone (n m : Nat) (h : n ≤ m) :
    echoParamSqlRisk n false ≤ echoParamSqlRisk m false := by { simp [echoParamSqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized SQL AND html/template for rendering
def netEchoRisk (inputLen : Nat) (sqlParam : Bool) (htmlTemplate : Bool) : Nat :=
  echoParamSqlRisk inputLen sqlParam + templateInjectionRisk inputLen htmlTemplate

theorem echo_net_risk_zero_fully_mitigated (n : Nat) :
    netEchoRisk n true true = 0 := by { simp [netEchoRisk, echoParamSqlRisk, templateInjectionRisk]

theorem echo_net_risk_pos_unmitigated (n : Nat) :
    0 < netEchoRisk n false false := by
  simp [netEchoRisk, echoParamSqlRisk, templateInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end EchoFrameworkQueryInjection
