import Init
-- ExpressQueryInjectionRisk.lean
-- Anti-thesis: Express.js (Node.js) req.params and req.query values used in
-- database queries or system operations carry no injection risk.
-- Refutation: unparameterized use of Express request data in SQL, command
-- execution, or template rendering yields a strictly positive vulnerability window.

namespace ExpressQueryInjection

-- SQL injection: req.params.id used in raw SQL string concatenation
def expressSqlRisk (paramLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else paramLen + 1

-- Parameterized query (db.query(sql, [id])) eliminates injection
theorem express_sql_parameterized_safe (n : Nat) :
    expressSqlRisk n true = 0 := by { simp [expressSqlRisk]

-- req.params.id in template literal SQL is strictly vulnerable
theorem express_sql_template_literal_risk (n : Nat) :
    0 < expressSqlRisk n false := by
  simp [expressSqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Query string injection: req.query.filter used in MongoDB query object
def queryObjectRisk (queryLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else queryLen + 1

theorem express_query_sanitized_safe (n : Nat) :
    queryObjectRisk n true = 0 := by { simp [queryObjectRisk]

theorem express_query_unsanitized_risk (n : Nat) :
    0 < queryObjectRisk n false := by
  simp [queryObjectRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Command injection: req.body.filename used in exec() or spawn() with shell:true
def cmdInjectionRisk (inputLen : Nat) (shellDisabled : Bool) : Nat :=
  if shellDisabled then 0 else inputLen + 1

theorem express_cmd_shell_disabled_safe (n : Nat) :
    cmdInjectionRisk n true = 0 := by { simp [cmdInjectionRisk]

theorem express_cmd_shell_injection_risk (n : Nat) :
    0 < cmdInjectionRisk n false := by
  simp [cmdInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Path traversal: req.params.file used in fs.readFile without path.resolve
def pathTraversalRisk (pathLen : Nat) (resolved : Bool) : Nat :=
  if resolved then 0 else pathLen + 1

theorem express_path_resolved_safe (n : Nat) :
    pathTraversalRisk n true = 0 := by { simp [pathTraversalRisk]

theorem express_path_unresolved_risk (n : Nat) :
    0 < pathTraversalRisk n false := by
  simp [pathTraversalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Prototype pollution: req.body merged into object with Object.assign
def prototypePollutionRisk (bodyLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else bodyLen + 1

theorem express_prototype_sanitized_safe (n : Nat) :
    prototypePollutionRisk n true = 0 := by { simp [prototypePollutionRisk]

theorem express_prototype_unsanitized_risk (n : Nat) :
    0 < prototypePollutionRisk n false := by
  simp [prototypePollutionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in param length
theorem express_sql_risk_monotone (n m : Nat) (h : n ≤ m) :
    expressSqlRisk n false ≤ expressSqlRisk m false := by { simp [expressSqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized SQL AND disabled shell exec
def netExpressRisk (inputLen : Nat) (sqlParam : Bool) (shellDisabled : Bool) : Nat :=
  expressSqlRisk inputLen sqlParam + cmdInjectionRisk inputLen shellDisabled

theorem express_net_risk_zero_fully_mitigated (n : Nat) :
    netExpressRisk n true true = 0 := by { simp [netExpressRisk, expressSqlRisk, cmdInjectionRisk]

theorem express_net_risk_pos_unmitigated (n : Nat) :
    0 < netExpressRisk n false false := by
  simp [netExpressRisk, expressSqlRisk, cmdInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end ExpressQueryInjection
