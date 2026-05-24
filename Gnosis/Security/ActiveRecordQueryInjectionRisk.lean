import Init
-- ActiveRecordQueryInjectionRisk.lean
-- Anti-thesis: Ruby on Rails ActiveRecord query construction from user input
-- via where(), order(), and select() cannot introduce SQL injection.
-- Refutation: string-interpolated conditions in ActiveRecord bypass parameter
-- binding and yield a strictly positive vulnerability window.

namespace ActiveRecordQueryInjection

-- where() injection: Model.where("name = '#{params[:name]}'") 
def whereStringRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

-- where(name: params[:name]) hash syntax is parameterized and safe
theorem ar_where_hash_parameterized_safe (n : Nat) :
    whereStringRisk n true = 0 := by { simp [whereStringRisk]

-- where("name = '#{input}'") string interpolation is strictly vulnerable
theorem ar_where_string_interpolation_risk (n : Nat) :
    0 < whereStringRisk n false := by
  simp [whereStringRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- order() injection: Model.order(params[:sort]) with unvalidated column
def orderRisk (columnLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else columnLen + 1

theorem ar_order_allowlisted_safe (n : Nat) :
    orderRisk n true = 0 := by { simp [orderRisk]

theorem ar_order_unvalidated_risk (n : Nat) :
    0 < orderRisk n false := by
  simp [orderRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- select() injection: Model.select(params[:columns]) with user-controlled columns
def selectRisk (colsLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else colsLen + 1

theorem ar_select_allowlisted_safe (n : Nat) :
    selectRisk n true = 0 := by { simp [selectRisk]

theorem ar_select_unvalidated_risk (n : Nat) :
    0 < selectRisk n false := by
  simp [selectRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- from() injection: Model.from(user_table) with unvalidated table name
def fromRisk (tableLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else tableLen + 1

theorem ar_from_allowlisted_safe (n : Nat) :
    fromRisk n true = 0 := by { simp [fromRisk]

theorem ar_from_unvalidated_risk (n : Nat) :
    0 < fromRisk n false := by
  simp [fromRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- joins() injection: Model.joins(user_join_clause)
def joinsRisk (clauseLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else clauseLen + 1

theorem ar_joins_parameterized_safe (n : Nat) :
    joinsRisk n true = 0 := by { simp [joinsRisk]

theorem ar_joins_string_risk (n : Nat) :
    0 < joinsRisk n false := by
  simp [joinsRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem ar_where_risk_monotone (n m : Nat) (h : n ≤ m) :
    whereStringRisk n false ≤ whereStringRisk m false := by { simp [whereStringRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized where AND allow-listed order/select
def netARRisk (inputLen : Nat) (parameterized : Bool) (allowListed : Bool) : Nat :=
  whereStringRisk inputLen parameterized + orderRisk inputLen allowListed

theorem ar_net_risk_zero_fully_mitigated (n : Nat) :
    netARRisk n true true = 0 := by { simp [netARRisk, whereStringRisk, orderRisk]

theorem ar_net_risk_pos_unmitigated (n : Nat) :
    0 < netARRisk n false false := by
  simp [netARRisk, whereStringRisk, orderRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end ActiveRecordQueryInjection
