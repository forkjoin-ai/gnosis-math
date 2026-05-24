import Init
-- KoaQueryInjectionRisk.lean
-- Anti-thesis: Koa.js (Node.js) ctx.query and ctx.params values used in
-- database queries or system operations carry no injection risk.
-- Refutation: ctx.query values passed to unparameterized SQL, MongoDB queries,
-- or file system operations yield a strictly positive vulnerability window.

namespace KoaQueryInjection

-- SQL injection: ctx.query.id used in SQL template literal
def koaSqlRisk (paramLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else paramLen + 1

-- Parameterized query eliminates Koa ctx.query SQL injection
theorem koa_sql_parameterized_safe (n : Nat) :
    koaSqlRisk n true = 0 := by { simp [koaSqlRisk]

-- ctx.query.id in template literal SQL is strictly vulnerable
theorem koa_sql_template_literal_risk (n : Nat) :
    0 < koaSqlRisk n false := by
  simp [koaSqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- MongoDB injection: ctx.query passed to find() without sanitization
def mongoQueryRisk (queryLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else queryLen + 1

theorem koa_mongo_sanitized_safe (n : Nat) :
    mongoQueryRisk n true = 0 := by { simp [mongoQueryRisk]

theorem koa_mongo_unsanitized_risk (n : Nat) :
    0 < mongoQueryRisk n false := by
  simp [mongoQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Middleware ctx.state pollution: user-controlled ctx.state mutation
def statePollutionRisk (stateLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else stateLen + 1

theorem koa_state_validated_safe (n : Nat) :
    statePollutionRisk n true = 0 := by { simp [statePollutionRisk]

theorem koa_state_unvalidated_risk (n : Nat) :
    0 < statePollutionRisk n false := by
  simp [statePollutionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- SSRF: ctx.query.url used in http.get() without validation
def ssrfRisk (urlLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else urlLen + 1

theorem koa_ssrf_allowlisted_safe (n : Nat) :
    ssrfRisk n true = 0 := by { simp [ssrfRisk]

theorem koa_ssrf_unvalidated_risk (n : Nat) :
    0 < ssrfRisk n false := by
  simp [ssrfRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Path traversal: ctx.params.file used without path.resolve/basename
def pathTraversalRisk (pathLen : Nat) (cleaned : Bool) : Nat :=
  if cleaned then 0 else pathLen + 1

theorem koa_path_cleaned_safe (n : Nat) :
    pathTraversalRisk n true = 0 := by { simp [pathTraversalRisk]

theorem koa_path_uncleaned_risk (n : Nat) :
    0 < pathTraversalRisk n false := by
  simp [pathTraversalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in query length
theorem koa_sql_risk_monotone (n m : Nat) (h : n ≤ m) :
    koaSqlRisk n false ≤ koaSqlRisk m false := by { simp [koaSqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized SQL AND sanitized MongoDB queries
def netKoaRisk (inputLen : Nat) (sqlParam : Bool) (mongoSanitized : Bool) : Nat :=
  koaSqlRisk inputLen sqlParam + mongoQueryRisk inputLen mongoSanitized

theorem koa_net_risk_zero_fully_mitigated (n : Nat) :
    netKoaRisk n true true = 0 := by { simp [netKoaRisk, koaSqlRisk, mongoQueryRisk]

theorem koa_net_risk_pos_unmitigated (n : Nat) :
    0 < netKoaRisk n false false := by
  simp [netKoaRisk, koaSqlRisk, mongoQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end KoaQueryInjection
