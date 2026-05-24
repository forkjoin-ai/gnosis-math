import Init
-- FlaskSQLAlchemyQueryInjectionRisk.lean
-- Anti-thesis: Flask-SQLAlchemy queries using text() with user input or
-- string-formatted filter() conditions carry no injection risk.
-- Refutation: text() with string interpolation and execute() with raw SQL
-- each yield a strictly positive vulnerability window.

namespace FlaskSQLAlchemyQueryInjection

-- text() injection: db.session.execute(text(f"SELECT ... WHERE name='{input}'"))
def textRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

-- text() with bindparams is safe: text(sql).bindparams(name=input)
theorem flask_sa_text_parameterized_safe (n : Nat) :
    textRisk n true = 0 := by { simp [textRisk]

-- f-string in text() is strictly vulnerable
theorem flask_sa_text_fstring_risk (n : Nat) :
    0 < textRisk n false := by
  simp [textRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- filter() string injection: query.filter(f"name = '{input}'")
def filterStringRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

theorem flask_sa_filter_parameterized_safe (n : Nat) :
    filterStringRisk n true = 0 := by { simp [filterStringRisk]

theorem flask_sa_filter_string_risk (n : Nat) :
    0 < filterStringRisk n false := by
  simp [filterStringRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- connection.execute() injection: engine.execute(raw_sql_with_input)
def executeRawRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

theorem flask_sa_execute_parameterized_safe (n : Nat) :
    executeRawRisk n true = 0 := by { simp [executeRawRisk]

theorem flask_sa_execute_raw_risk (n : Nat) :
    0 < executeRawRisk n false := by
  simp [executeRawRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- order_by(text()) injection: query.order_by(text(user_col))
def orderByTextRisk (colLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else colLen + 1

theorem flask_sa_order_allowlisted_safe (n : Nat) :
    orderByTextRisk n true = 0 := by { simp [orderByTextRisk]

theorem flask_sa_order_unvalidated_risk (n : Nat) :
    0 < orderByTextRisk n false := by
  simp [orderByTextRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- column() injection: select(column(user_col)) with unvalidated column name
def columnRisk (colLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else colLen + 1

theorem flask_sa_column_allowlisted_safe (n : Nat) :
    columnRisk n true = 0 := by { simp [columnRisk]

theorem flask_sa_column_unvalidated_risk (n : Nat) :
    0 < columnRisk n false := by
  simp [columnRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem flask_sa_text_risk_monotone (n m : Nat) (h : n ≤ m) :
    textRisk n false ≤ textRisk m false := by { simp [textRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized text() AND allow-listed column names
def netFlaskSARisk (inputLen : Nat) (parameterized : Bool) (allowListed : Bool) : Nat :=
  textRisk inputLen parameterized + columnRisk inputLen allowListed

theorem flask_sa_net_risk_zero_fully_mitigated (n : Nat) :
    netFlaskSARisk n true true = 0 := by { simp [netFlaskSARisk, textRisk, columnRisk]

theorem flask_sa_net_risk_pos_unmitigated (n : Nat) :
    0 < netFlaskSARisk n false false := by
  simp [netFlaskSARisk, textRisk, columnRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end FlaskSQLAlchemyQueryInjection
