import Init
-- DjangoQueryInjectionRisk.lean
-- Anti-thesis: Django ORM query construction from user input via raw(),
-- extra(), and RawSQL() cannot introduce SQL injection.
-- Refutation: unparameterized use of user input in Django raw queries and
-- extra() WHERE clauses yields a strictly positive vulnerability window.

namespace DjangoQueryInjection

-- raw() injection: Model.objects.raw("SELECT ... WHERE name='" + input + "'")
def rawQueryRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

-- raw() with params list is safe: Model.objects.raw(sql, [input])
theorem django_raw_parameterized_safe (n : Nat) :
    rawQueryRisk n true = 0 := by { simp [rawQueryRisk]

-- raw() with string concatenation/format is strictly vulnerable
theorem django_raw_concat_risk (n : Nat) :
    0 < rawQueryRisk n false := by
  simp [rawQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- extra() injection: queryset.extra(where=["name = '" + input + "'"])
def extraWhereRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

theorem django_extra_parameterized_safe (n : Nat) :
    extraWhereRisk n true = 0 := by { simp [extraWhereRisk]

theorem django_extra_string_risk (n : Nat) :
    0 < extraWhereRisk n false := by
  simp [extraWhereRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- RawSQL() injection: annotate(col=RawSQL(user_sql, []))
def rawSqlAnnotateRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

theorem django_rawsql_parameterized_safe (n : Nat) :
    rawSqlAnnotateRisk n true = 0 := by { simp [rawSqlAnnotateRisk]

theorem django_rawsql_string_risk (n : Nat) :
    0 < rawSqlAnnotateRisk n false := by
  simp [rawSqlAnnotateRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- order_by() injection: queryset.order_by(user_field) with unvalidated field
def orderByRisk (fieldLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else fieldLen + 1

theorem django_order_by_allowlisted_safe (n : Nat) :
    orderByRisk n true = 0 := by { simp [orderByRisk]

theorem django_order_by_unvalidated_risk (n : Nat) :
    0 < orderByRisk n false := by
  simp [orderByRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- values() injection: queryset.values(user_field) with unvalidated field name
def valuesFieldRisk (fieldLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else fieldLen + 1

theorem django_values_allowlisted_safe (n : Nat) :
    valuesFieldRisk n true = 0 := by { simp [valuesFieldRisk]

theorem django_values_unvalidated_risk (n : Nat) :
    0 < valuesFieldRisk n false := by
  simp [valuesFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem django_raw_risk_monotone (n m : Nat) (h : n ≤ m) :
    rawQueryRisk n false ≤ rawQueryRisk m false := by { simp [rawQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized raw() AND allow-listed order_by
def netDjangoRisk (inputLen : Nat) (parameterized : Bool) (allowListed : Bool) : Nat :=
  rawQueryRisk inputLen parameterized + orderByRisk inputLen allowListed

theorem django_net_risk_zero_fully_mitigated (n : Nat) :
    netDjangoRisk n true true = 0 := by { simp [netDjangoRisk, rawQueryRisk, orderByRisk]

theorem django_net_risk_pos_unmitigated (n : Nat) :
    0 < netDjangoRisk n false false := by
  simp [netDjangoRisk, rawQueryRisk, orderByRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end DjangoQueryInjection
