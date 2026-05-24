import Init
-- Psycopg3QueryInjectionRisk.lean
-- Anti-thesis: psycopg3 (psycopg >= 3.0) async PostgreSQL queries constructed
-- via f-strings or % formatting carry no injection risk.
-- Refutation: server-side binding (binary protocol parameterization) is required;
-- any unparameterized path yields a strictly positive vulnerability window.

namespace Psycopg3QueryInjection

-- SQL risk: unparameterized query via f-string / string format
def sqlRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

-- Server-side binding (%s placeholders with execute args) eliminates injection
theorem psycopg3_parameterized_zero_risk (n : Nat) :
    sqlRisk n true = 0 := by { simp [sqlRisk]

-- f-string query construction yields strictly positive risk
theorem psycopg3_fstring_risk_positive (n : Nat) :
    0 < sqlRisk n false := by
  simp [sqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk is monotone in user input length
theorem psycopg3_risk_monotone (n m : Nat) (h : n ≤ m) :
    sqlRisk n false ≤ sqlRisk m false := by { simp [sqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Async cursor (await conn.execute) does not eliminate injection risk
def asyncSqlRisk (inputLen : Nat) (parameterized : Bool) (_ : Bool) : Nat :=
  sqlRisk inputLen parameterized

theorem psycopg3_async_preserves_risk (n : Nat) :
    asyncSqlRisk n false true = sqlRisk n false := by { simp [asyncSqlRisk]

theorem psycopg3_async_risk_positive (n : Nat) :
    0 < asyncSqlRisk n false true := by
  simp [asyncSqlRisk, sqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- COPY FROM injection: unparameterized table/column names in COPY statement
def copyFromRisk (tableNameLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else tableNameLen + 1

theorem psycopg3_copy_allowlisted_safe (n : Nat) :
    copyFromRisk n true = 0 := by { simp [copyFromRisk]

theorem psycopg3_copy_unvalidated_risk (n : Nat) :
    0 < copyFromRisk n false := by
  simp [copyFromRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- NOTIFY channel injection: channel name from user input
def notifyChannelRisk (channelLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else channelLen + 1

theorem psycopg3_notify_unvalidated_risk (n : Nat) :
    0 < notifyChannelRisk n false := by { simp [notifyChannelRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem psycopg3_notify_validated_safe (n : Nat) :
    notifyChannelRisk n true = 0 := by { simp [notifyChannelRisk]

-- sql.Identifier (psycopg3 composer) eliminates identifier injection
def identifierRisk (nameLen : Nat) (usesSqlIdentifier : Bool) : Nat :=
  if usesSqlIdentifier then 0 else nameLen + 1

theorem psycopg3_identifier_composer_safe (n : Nat) :
    identifierRisk n true = 0 := by
  simp [identifierRisk]

theorem psycopg3_raw_identifier_risk (n : Nat) :
    0 < identifierRisk n false := by
  simp [identifierRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Multi-query risk: executemany with interpolated template
theorem psycopg3_executemany_risk_monotone (n k1 k2 : Nat) (h : k1 ≤ k2) :
    sqlRisk n false + k1 ≤ sqlRisk n false + k2 := by
  omega

-- Net: zero-risk path requires parameterized values AND sql.Identifier for names
def netPsycopg3Risk (inputLen : Nat) (parameterized : Bool) (usesIdentifier : Bool) : Nat :=
  sqlRisk inputLen parameterized + identifierRisk inputLen usesIdentifier

theorem psycopg3_net_risk_zero_fully_mitigated (n : Nat) :
    netPsycopg3Risk n true true = 0 := by { simp [netPsycopg3Risk, sqlRisk, identifierRisk]

theorem psycopg3_net_risk_pos_unmitigated (n : Nat) :
    0 < netPsycopg3Risk n false false := by
  simp [netPsycopg3Risk, sqlRisk, identifierRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end Psycopg3QueryInjection
