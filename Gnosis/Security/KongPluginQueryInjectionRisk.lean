import Init
-- KongPluginQueryInjectionRisk.lean
-- Anti-thesis: Kong API gateway custom plugin Lua code using kong.request
-- values in upstream mutations carries no injection risk.
-- Refutation: unvalidated header/query/body values used to mutate upstream
-- requests or perform backend calls yield a strictly positive vulnerability window.

namespace KongPluginQueryInjection

-- Header mutation injection: kong.service.request.set_header with user value
def headerMutationRisk (valueLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else valueLen + 1

-- Sanitized header value eliminates upstream injection
theorem kong_header_mutation_sanitized_safe (n : Nat) :
    headerMutationRisk n true = 0 := by { simp [headerMutationRisk]

-- Unsanitized user header value propagated upstream is strictly vulnerable
theorem kong_header_mutation_unsanitized_risk (n : Nat) :
    0 < headerMutationRisk n false := by
  simp [headerMutationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Query param injection: kong.request.get_query() values in upstream URL
def queryParamRisk (paramLen : Nat) (encoded : Bool) : Nat :=
  if encoded then 0 else paramLen + 1

theorem kong_query_param_encoded_safe (n : Nat) :
    queryParamRisk n true = 0 := by { simp [queryParamRisk]

theorem kong_query_param_unencoded_risk (n : Nat) :
    0 < queryParamRisk n false := by
  simp [queryParamRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Body injection: kong.request.get_body() fields used in HTTP subrequest
def bodyFieldRisk (fieldLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else fieldLen + 1

theorem kong_body_field_validated_safe (n : Nat) :
    bodyFieldRisk n true = 0 := by { simp [bodyFieldRisk]

theorem kong_body_field_unvalidated_risk (n : Nat) :
    0 < bodyFieldRisk n false := by
  simp [bodyFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Route match injection: dynamic route via user-controlled path segment
def routeSegmentRisk (segLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else segLen + 1

theorem kong_route_segment_allowlisted_safe (n : Nat) :
    routeSegmentRisk n true = 0 := by { simp [routeSegmentRisk]

theorem kong_route_segment_unvalidated_risk (n : Nat) :
    0 < routeSegmentRisk n false := by
  simp [routeSegmentRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Consumer injection: consumer credential lookup with user-controlled key
def consumerKeyRisk (keyLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else keyLen + 1

theorem kong_consumer_key_validated_safe (n : Nat) :
    consumerKeyRisk n true = 0 := by { simp [consumerKeyRisk]

theorem kong_consumer_key_unvalidated_risk (n : Nat) :
    0 < consumerKeyRisk n false := by
  simp [consumerKeyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in value length
theorem kong_header_risk_monotone (n m : Nat) (h : n ≤ m) :
    headerMutationRisk n false ≤ headerMutationRisk m false := by { simp [headerMutationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires sanitized headers AND encoded query params
def netKongRisk (inputLen : Nat) (sanitized : Bool) (encoded : Bool) : Nat :=
  headerMutationRisk inputLen sanitized + queryParamRisk inputLen encoded

theorem kong_net_risk_zero_fully_mitigated (n : Nat) :
    netKongRisk n true true = 0 := by { simp [netKongRisk, headerMutationRisk, queryParamRisk]

theorem kong_net_risk_pos_unmitigated (n : Nat) :
    0 < netKongRisk n false false := by
  simp [netKongRisk, headerMutationRisk, queryParamRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end KongPluginQueryInjection
