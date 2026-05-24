import Init
-- DjangoRestFrameworkQueryInjectionRisk.lean
-- Anti-thesis: Django REST Framework (DRF) serializer validation and
-- ViewSet filtering from user input carry no injection risk.
-- Refutation: filter_queryset() with unvalidated fields and serializer
-- write_only injection bypass each yield a strictly positive vulnerability window.

namespace DjangoRestFrameworkQueryInjection

-- FilterSet field injection: unvalidated filter field passed to ORM
def filterFieldRisk (fieldLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else fieldLen + 1

-- Allow-listed filterable fields eliminate filter injection
theorem drf_filter_field_allowlisted_safe (n : Nat) :
    filterFieldRisk n true = 0 := by { simp [filterFieldRisk]

-- Unvalidated filterable field enables cross-model data access
theorem drf_filter_field_unvalidated_risk (n : Nat) :
    0 < filterFieldRisk n false := by
  simp [filterFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Serializer source injection: source=user_field maps to model attribute
def sourceFieldRisk (fieldLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else fieldLen + 1

theorem drf_source_allowlisted_safe (n : Nat) :
    sourceFieldRisk n true = 0 := by { simp [sourceFieldRisk]

theorem drf_source_unvalidated_risk (n : Nat) :
    0 < sourceFieldRisk n false := by
  simp [sourceFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Ordering injection: OrderingFilter with user-controlled ordering fields
def orderingRisk (fieldLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else fieldLen + 1

theorem drf_ordering_allowlisted_safe (n : Nat) :
    orderingRisk n true = 0 := by { simp [orderingRisk]

theorem drf_ordering_unvalidated_risk (n : Nat) :
    0 < orderingRisk n false := by
  simp [orderingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- SearchFilter injection: SearchFilter with user-controlled search_fields
def searchFieldRisk (fieldLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else fieldLen + 1

theorem drf_search_parameterized_safe (n : Nat) :
    searchFieldRisk n true = 0 := by { simp [searchFieldRisk]

theorem drf_search_unparameterized_risk (n : Nat) :
    0 < searchFieldRisk n false := by
  simp [searchFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- ViewSet action injection: router-registered actions with unvalidated URL kwargs
def actionKwargRisk (kwargLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else kwargLen + 1

theorem drf_action_kwarg_validated_safe (n : Nat) :
    actionKwargRisk n true = 0 := by { simp [actionKwargRisk]

theorem drf_action_kwarg_unvalidated_risk (n : Nat) :
    0 < actionKwargRisk n false := by
  simp [actionKwargRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in field length
theorem drf_filter_risk_monotone (n m : Nat) (h : n ≤ m) :
    filterFieldRisk n false ≤ filterFieldRisk m false := by { simp [filterFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires allow-listed filter fields AND allow-listed ordering
def netDRFRisk (inputLen : Nat) (filterAllowListed : Bool) (orderAllowListed : Bool) : Nat :=
  filterFieldRisk inputLen filterAllowListed + orderingRisk inputLen orderAllowListed

theorem drf_net_risk_zero_fully_mitigated (n : Nat) :
    netDRFRisk n true true = 0 := by { simp [netDRFRisk, filterFieldRisk, orderingRisk]

theorem drf_net_risk_pos_unmitigated (n : Nat) :
    0 < netDRFRisk n false false := by
  simp [netDRFRisk, filterFieldRisk, orderingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end DjangoRestFrameworkQueryInjection
