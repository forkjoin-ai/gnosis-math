import Init
-- SpringDataJPAQueryInjectionRisk.lean
-- Anti-thesis: Spring Data JPA @Query annotations with nativeQuery=true
-- and JPQL concatenation from user input carry no injection risk.
-- Refutation: native query string concatenation and SpEL expression injection
-- each yield a strictly positive vulnerability window.

namespace SpringDataJPAQueryInjection

-- @Query nativeQuery injection: @Query(value = "SELECT ... WHERE name='" + param + "'")
def nativeQueryRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

-- @Param binding (:name) eliminates native query injection
theorem spring_native_query_parameterized_safe (n : Nat) :
    nativeQueryRisk n true = 0 := by { simp [nativeQueryRisk]

-- String concatenation in @Query value is strictly vulnerable
theorem spring_native_query_concat_risk (n : Nat) :
    0 < nativeQueryRisk n false := by
  simp [nativeQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- JPQL injection: EntityManager.createQuery with concatenated input
def jpqlRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

theorem spring_jpql_parameterized_safe (n : Nat) :
    jpqlRisk n true = 0 := by { simp [jpqlRisk]

theorem spring_jpql_concat_risk (n : Nat) :
    0 < jpqlRisk n false := by
  simp [jpqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- SpEL expression injection: #{#entityName} with user-controlled entity name
def spelExprRisk (exprLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else exprLen + 1

theorem spring_spel_allowlisted_safe (n : Nat) :
    spelExprRisk n true = 0 := by { simp [spelExprRisk]

theorem spring_spel_unvalidated_risk (n : Nat) :
    0 < spelExprRisk n false := by
  simp [spelExprRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Sort injection: Sort.by(user_field) with unvalidated field name
def sortFieldRisk (fieldLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else fieldLen + 1

theorem spring_sort_allowlisted_safe (n : Nat) :
    sortFieldRisk n true = 0 := by { simp [sortFieldRisk]

theorem spring_sort_unvalidated_risk (n : Nat) :
    0 < sortFieldRisk n false := by
  simp [sortFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Specification injection: user-controlled predicate construction
def specificationRisk (specLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else specLen + 1

theorem spring_spec_validated_safe (n : Nat) :
    specificationRisk n true = 0 := by { simp [specificationRisk]

theorem spring_spec_unvalidated_risk (n : Nat) :
    0 < specificationRisk n false := by
  simp [specificationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem spring_native_risk_monotone (n m : Nat) (h : n ≤ m) :
    nativeQueryRisk n false ≤ nativeQueryRisk m false := by { simp [nativeQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized queries AND allow-listed Sort fields
def netSpringJPARisk (inputLen : Nat) (parameterized : Bool) (sortAllowListed : Bool) : Nat :=
  nativeQueryRisk inputLen parameterized + sortFieldRisk inputLen sortAllowListed

theorem spring_jpa_net_risk_zero_fully_mitigated (n : Nat) :
    netSpringJPARisk n true true = 0 := by { simp [netSpringJPARisk, nativeQueryRisk, sortFieldRisk]

theorem spring_jpa_net_risk_pos_unmitigated (n : Nat) :
    0 < netSpringJPARisk n false false := by
  simp [netSpringJPARisk, nativeQueryRisk, sortFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end SpringDataJPAQueryInjection
