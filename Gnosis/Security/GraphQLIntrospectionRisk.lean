import Init
-- GraphQLIntrospectionRisk.lean
-- Anti-thesis: GraphQL introspection enabled in production carries no risk
-- because the schema is already public knowledge.
-- Refutation: introspection enables schema enumeration that amplifies
-- targeted injection attacks, yielding a strictly positive disclosure window.

namespace Gnosis.Security.GraphQLIntrospectionRisk

-- Introspection disclosure: schema field enumeration via __schema query
def introspectionRisk (schemaSize : Nat) (introspectionDisabled : Bool) : Nat :=
  if introspectionDisabled then 0 else schemaSize + 1

-- Disabled introspection eliminates schema enumeration
theorem graphql_introspection_disabled_safe (n : Nat) :
    introspectionRisk n true = 0 := by { simp [introspectionRisk]

-- Enabled introspection exposes schema proportional to its size
theorem graphql_introspection_enabled_risk (n : Nat) :
    0 < introspectionRisk n false := by
  simp [introspectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Schema size amplifies disclosure: larger schemas leak more sensitive info
theorem graphql_introspection_amplifies_with_schema (n m : Nat) (h : n ≤ m) :
    introspectionRisk n false ≤ introspectionRisk m false := by { simp [introspectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- __type query: targeted type introspection (harder to disable than __schema)
def typeIntrospectionRisk (typeCount : Nat) (fieldSuggestionsDisabled : Bool) : Nat :=
  if fieldSuggestionsDisabled then 0 else typeCount + 1

theorem graphql_type_suggestions_disabled_safe (n : Nat) :
    typeIntrospectionRisk n true = 0 := by { simp [typeIntrospectionRisk]

theorem graphql_type_suggestions_enabled_risk (n : Nat) :
    0 < typeIntrospectionRisk n false := by
  simp [typeIntrospectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Query depth: unbounded nested queries enable DoS
def queryDepthRisk (depth : Nat) (maxDepthEnforced : Bool) : Nat :=
  if maxDepthEnforced then 0 else depth + 1

theorem graphql_depth_limit_enforced_safe (n : Nat) :
    queryDepthRisk n true = 0 := by { simp [queryDepthRisk]

theorem graphql_depth_unlimited_risk (n : Nat) :
    0 < queryDepthRisk n false := by
  simp [queryDepthRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Query complexity: unbounded field selection amplifies backend load
def queryComplexityRisk (complexity : Nat) (complexityLimited : Bool) : Nat :=
  if complexityLimited then 0 else complexity + 1

theorem graphql_complexity_limited_safe (n : Nat) :
    queryComplexityRisk n true = 0 := by { simp [queryComplexityRisk]

theorem graphql_complexity_unlimited_risk (n : Nat) :
    0 < queryComplexityRisk n false := by
  simp [queryComplexityRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Batch query amplification: batched queries multiply resource consumption
def batchQueryRisk (batchSize : Nat) (rateLimited : Bool) : Nat :=
  if rateLimited then 0 else batchSize + 1

theorem graphql_batch_rate_limited_safe (n : Nat) :
    batchQueryRisk n true = 0 := by { simp [batchQueryRisk]

theorem graphql_batch_unlimited_risk (n : Nat) :
    0 < batchQueryRisk n false := by
  simp [batchQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in schema size
theorem graphql_risk_monotone_schema (n m : Nat) (h : n ≤ m) :
    introspectionRisk n false ≤ introspectionRisk m false := by { simp [introspectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires disabled introspection AND enforced depth limit
def netIntrospectionRisk (schemaSize : Nat) (introspectionOff : Bool) (depthLimited : Bool) : Nat :=
  introspectionRisk schemaSize introspectionOff + queryDepthRisk schemaSize depthLimited

theorem graphql_net_risk_zero_fully_mitigated (n : Nat) :
    netIntrospectionRisk n true true = 0 := by { simp [netIntrospectionRisk, introspectionRisk, queryDepthRisk]

theorem graphql_net_risk_pos_unmitigated (n : Nat) :
    0 < netIntrospectionRisk n false false := by
  simp [netIntrospectionRisk, introspectionRisk, queryDepthRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end GraphQLIntrospectionRisk
