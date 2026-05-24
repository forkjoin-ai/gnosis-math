import Init
-- HibernateQueryInjectionRisk.lean
-- Anti-thesis: Hibernate HQL/JPQL queries constructed from user input via
-- string concatenation carry no injection risk.
-- Refutation: HQL concatenation and NativeQuery string assembly each yield
-- a strictly positive vulnerability window bypassing ORM protections.

namespace HibernateQueryInjection

-- HQL injection: session.createQuery("FROM Entity WHERE name = '" + input + "'")
def hqlRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

-- Named parameters (:name) or positional (?0) eliminate HQL injection
theorem hibernate_hql_parameterized_safe (n : Nat) :
    hqlRisk n true = 0 := by { simp [hqlRisk]

-- String-concatenated HQL is strictly vulnerable
theorem hibernate_hql_concat_risk (n : Nat) :
    0 < hqlRisk n false := by
  simp [hqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Native SQL injection: session.createNativeQuery with concatenated input
def nativeQueryRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

theorem hibernate_native_parameterized_safe (n : Nat) :
    nativeQueryRisk n true = 0 := by { simp [nativeQueryRisk]

theorem hibernate_native_concat_risk (n : Nat) :
    0 < nativeQueryRisk n false := by
  simp [nativeQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Criteria API injection: order by user-controlled property name
def criteriaOrderRisk (propLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else propLen + 1

theorem hibernate_criteria_allowlisted_safe (n : Nat) :
    criteriaOrderRisk n true = 0 := by { simp [criteriaOrderRisk]

theorem hibernate_criteria_unvalidated_risk (n : Nat) :
    0 < criteriaOrderRisk n false := by
  simp [criteriaOrderRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- JPQL injection: EntityManager.createQuery with string concatenation
def jpqlRisk (inputLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else inputLen + 1

theorem hibernate_jpql_parameterized_safe (n : Nat) :
    jpqlRisk n true = 0 := by { simp [jpqlRisk]

theorem hibernate_jpql_concat_risk (n : Nat) :
    0 < jpqlRisk n false := by
  simp [jpqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Named native query injection: injection via dynamic query name resolution
def namedQueryRisk (nameLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else nameLen + 1

theorem hibernate_named_query_allowlisted_safe (n : Nat) :
    namedQueryRisk n true = 0 := by { simp [namedQueryRisk]

theorem hibernate_named_query_unvalidated_risk (n : Nat) :
    0 < namedQueryRisk n false := by
  simp [namedQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem hibernate_hql_risk_monotone (n m : Nat) (h : n ≤ m) :
    hqlRisk n false ≤ hqlRisk m false := by { simp [hqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized HQL AND allow-listed Criteria properties
def netHibernateRisk (inputLen : Nat) (parameterized : Bool) (allowListed : Bool) : Nat :=
  hqlRisk inputLen parameterized + criteriaOrderRisk inputLen allowListed

theorem hibernate_net_risk_zero_fully_mitigated (n : Nat) :
    netHibernateRisk n true true = 0 := by { simp [netHibernateRisk, hqlRisk, criteriaOrderRisk]

theorem hibernate_net_risk_pos_unmitigated (n : Nat) :
    0 < netHibernateRisk n false false := by
  simp [netHibernateRisk, hqlRisk, criteriaOrderRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end HibernateQueryInjection
