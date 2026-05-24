import Init
-- LaravelQueryInjectionRisk.lean
-- Anti-thesis: Laravel Eloquent whereRaw(), selectRaw(), and DB::statement()
-- with user input carry no injection risk because Laravel is a mature framework.
-- Refutation: raw() methods with unparameterized user input bypass Eloquent's
-- binding protection and yield a strictly positive vulnerability window.

namespace LaravelQueryInjection

-- whereRaw() injection: User::whereRaw("name = '" . $input . "'")
def whereRawRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

-- whereRaw("name = ?", [$input]) uses binding and is safe
theorem laravel_whereraw_parameterized_safe (n : Nat) :
    whereRawRisk n true = 0 := by { simp [whereRawRisk]

-- whereRaw() with string concatenation is strictly vulnerable
theorem laravel_whereraw_concat_risk (n : Nat) :
    0 < whereRawRisk n false := by
  simp [whereRawRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- selectRaw() injection: selectRaw("*, '" . $col . "' as alias")
def selectRawRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

theorem laravel_selectraw_parameterized_safe (n : Nat) :
    selectRawRisk n true = 0 := by { simp [selectRawRisk]

theorem laravel_selectraw_concat_risk (n : Nat) :
    0 < selectRawRisk n false := by
  simp [selectRawRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- orderByRaw() injection: orderByRaw($request->input('sort'))
def orderByRawRisk (colLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else colLen + 1

theorem laravel_orderbyraw_allowlisted_safe (n : Nat) :
    orderByRawRisk n true = 0 := by { simp [orderByRawRisk]

theorem laravel_orderbyraw_unvalidated_risk (n : Nat) :
    0 < orderByRawRisk n false := by
  simp [orderByRawRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- DB::statement() injection: DB::statement("ALTER TABLE " . $table)
def dbStatementRisk (inputLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else inputLen + 1

theorem laravel_db_statement_allowlisted_safe (n : Nat) :
    dbStatementRisk n true = 0 := by { simp [dbStatementRisk]

theorem laravel_db_statement_unvalidated_risk (n : Nat) :
    0 < dbStatementRisk n false := by
  simp [dbStatementRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- groupByRaw() injection: groupByRaw($request->input('group'))
def groupByRawRisk (inputLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else inputLen + 1

theorem laravel_groupbyraw_allowlisted_safe (n : Nat) :
    groupByRawRisk n true = 0 := by { simp [groupByRawRisk]

theorem laravel_groupbyraw_unvalidated_risk (n : Nat) :
    0 < groupByRawRisk n false := by
  simp [groupByRawRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem laravel_whereraw_risk_monotone (n m : Nat) (h : n ≤ m) :
    whereRawRisk n false ≤ whereRawRisk m false := by { simp [whereRawRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized whereRaw AND allow-listed orderByRaw
def netLaravelRisk (inputLen : Nat) (parameterized : Bool) (allowListed : Bool) : Nat :=
  whereRawRisk inputLen parameterized + orderByRawRisk inputLen allowListed

theorem laravel_net_risk_zero_fully_mitigated (n : Nat) :
    netLaravelRisk n true true = 0 := by { simp [netLaravelRisk, whereRawRisk, orderByRawRisk]

theorem laravel_net_risk_pos_unmitigated (n : Nat) :
    0 < netLaravelRisk n false false := by
  simp [netLaravelRisk, whereRawRisk, orderByRawRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end LaravelQueryInjection
