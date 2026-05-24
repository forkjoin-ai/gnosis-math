import Init
-- PDOQueryInjectionRisk.lean
-- Anti-thesis: PHP PDO (PHP Data Objects) database queries constructed
-- from user input via string concatenation carry no injection risk.
-- Refutation: unparameterized PDO::query() with concatenated user input
-- yields a strictly positive vulnerability window.

namespace PDOQueryInjection

-- PDO::query() injection: $pdo->query("SELECT ... WHERE id='" . $id . "'")
def pdoQueryRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

-- PDO::prepare() + execute() eliminates injection
theorem pdo_prepare_execute_safe (n : Nat) :
    pdoQueryRisk n true = 0 := by { simp [pdoQueryRisk]

-- PDO::query() with string concatenation is strictly vulnerable
theorem pdo_query_concat_risk (n : Nat) :
    0 < pdoQueryRisk n false := by
  simp [pdoQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- emulated prepares: PDO emulated prepared statements may not escape correctly
def emulatedPrepareRisk (inputLen : Nat) (nativeDriver : Bool) : Nat :=
  if nativeDriver then 0 else inputLen + 1

theorem pdo_native_driver_safe (n : Nat) :
    emulatedPrepareRisk n true = 0 := by { simp [emulatedPrepareRisk]

theorem pdo_emulated_prepare_risk (n : Nat) :
    0 < emulatedPrepareRisk n false := by
  simp [emulatedPrepareRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Order by injection: "ORDER BY " . $_GET['sort'] with unvalidated column
def orderByRisk (colLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else colLen + 1

theorem pdo_order_allowlisted_safe (n : Nat) :
    orderByRisk n true = 0 := by { simp [orderByRisk]

theorem pdo_order_unvalidated_risk (n : Nat) :
    0 < orderByRisk n false := by
  simp [orderByRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Table name injection: dynamic table from user input (PDO can't parameterize identifiers)
def tableNameRisk (tableLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else tableLen + 1

theorem pdo_table_allowlisted_safe (n : Nat) :
    tableNameRisk n true = 0 := by { simp [tableNameRisk]

theorem pdo_table_unvalidated_risk (n : Nat) :
    0 < tableNameRisk n false := by
  simp [tableNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- LIKE clause injection: "LIKE '%" . $input . "%'" with unescaped wildcards
def likeClauseRisk (inputLen : Nat) (escaped : Bool) : Nat :=
  if escaped then 0 else inputLen + 1

theorem pdo_like_escaped_safe (n : Nat) :
    likeClauseRisk n true = 0 := by { simp [likeClauseRisk]

theorem pdo_like_unescaped_risk (n : Nat) :
    0 < likeClauseRisk n false := by
  simp [likeClauseRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem pdo_query_risk_monotone (n m : Nat) (h : n ≤ m) :
    pdoQueryRisk n false ≤ pdoQueryRisk m false := by { simp [pdoQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized query AND allow-listed identifiers
def netPDORisk (inputLen : Nat) (parameterized : Bool) (allowListed : Bool) : Nat :=
  pdoQueryRisk inputLen parameterized + tableNameRisk inputLen allowListed

theorem pdo_net_risk_zero_fully_mitigated (n : Nat) :
    netPDORisk n true true = 0 := by { simp [netPDORisk, pdoQueryRisk, tableNameRisk]

theorem pdo_net_risk_pos_unmitigated (n : Nat) :
    0 < netPDORisk n false false := by
  simp [netPDORisk, pdoQueryRisk, tableNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end PDOQueryInjection
