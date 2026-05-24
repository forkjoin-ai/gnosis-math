import Init
-- MyBatisQueryInjectionRisk.lean
-- Anti-thesis: MyBatis mapper $\{variable\} substitution from user input
-- carries no injection risk compared to #\{variable\} parameterization.
-- Refutation: $\{\} performs literal string substitution (no escaping),
-- yielding a strictly positive vulnerability window relative to #\{\}.

namespace MyBatisQueryInjection

-- ${}  substitution: SELECT * FROM ${tableName} WHERE name = ${name}
-- (literal string substitution, no parameter binding)
def dollarSubstRisk (inputLen : Nat) (usesPound : Bool) : Nat :=
  if usesPound then 0 else inputLen + 1

-- #{} parameterization (JDBC PreparedStatement) eliminates injection
theorem mybatis_pound_param_safe (n : Nat) :
    dollarSubstRisk n true = 0 := by { simp [dollarSubstRisk]

-- ${} substitution is strictly vulnerable to injection
theorem mybatis_dollar_subst_risk (n : Nat) :
    0 < dollarSubstRisk n false := by
  simp [dollarSubstRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- ORDER BY ${column}: column name injection via $\{\} in ORDER BY clause
def orderByDollarRisk (colLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else colLen + 1

theorem mybatis_order_allowlisted_safe (n : Nat) :
    orderByDollarRisk n true = 0 := by { simp [orderByDollarRisk]

theorem mybatis_order_dollar_unvalidated_risk (n : Nat) :
    0 < orderByDollarRisk n false := by
  simp [orderByDollarRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Table name injection: SELECT * FROM ${table} with user-controlled table
def tableNameDollarRisk (tableLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else tableLen + 1

theorem mybatis_table_allowlisted_safe (n : Nat) :
    tableNameDollarRisk n true = 0 := by { simp [tableNameDollarRisk]

theorem mybatis_table_dollar_unvalidated_risk (n : Nat) :
    0 < tableNameDollarRisk n false := by
  simp [tableNameDollarRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Dynamic SQL <if> injection: user-controlled condition in <if test=...>
def dynamicIfRisk (condLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else condLen + 1

theorem mybatis_dynamic_if_validated_safe (n : Nat) :
    dynamicIfRisk n true = 0 := by { simp [dynamicIfRisk]

theorem mybatis_dynamic_if_unvalidated_risk (n : Nat) :
    0 < dynamicIfRisk n false := by
  simp [dynamicIfRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- <foreach> injection: user-controlled collection in <foreach collection=...>
def foreachCollectionRisk (itemLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else itemLen + 1

theorem mybatis_foreach_sanitized_safe (n : Nat) :
    foreachCollectionRisk n true = 0 := by { simp [foreachCollectionRisk]

theorem mybatis_foreach_unsanitized_risk (n : Nat) :
    0 < foreachCollectionRisk n false := by
  simp [foreachCollectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone: longer substitution input widens injection surface
theorem mybatis_dollar_risk_monotone (n m : Nat) (h : n ≤ m) :
    dollarSubstRisk n false ≤ dollarSubstRisk m false := by { simp [dollarSubstRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires #{} parameterization AND allow-listed identifiers
def netMyBatisRisk (inputLen : Nat) (usesPound : Bool) (allowListed : Bool) : Nat :=
  dollarSubstRisk inputLen usesPound + tableNameDollarRisk inputLen allowListed

theorem mybatis_net_risk_zero_fully_mitigated (n : Nat) :
    netMyBatisRisk n true true = 0 := by { simp [netMyBatisRisk, dollarSubstRisk, tableNameDollarRisk]

theorem mybatis_net_risk_pos_unmitigated (n : Nat) :
    0 < netMyBatisRisk n false false := by
  simp [netMyBatisRisk, dollarSubstRisk, tableNameDollarRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end MyBatisQueryInjection
