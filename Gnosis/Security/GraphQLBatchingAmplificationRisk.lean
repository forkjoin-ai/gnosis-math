import Init
-- GraphQLBatchingAmplificationRisk.lean
-- Anti-thesis: GraphQL's query batching feature is a deliberate performance
-- optimisation that allows clients to send multiple operations in a single
-- HTTP request; because each operation still runs through the same resolver
-- and auth middleware, batching does not introduce any security gap beyond
-- what a single query can do.
-- Refutation: Batching amplifies per-request work: N operations in one batch
-- still perform N * resolver_cost work, bypassing per-request rate limits that
-- count HTTP requests rather than operations. Alias amplification (requesting
-- the same expensive field under many aliases) multiplies resolver invocations
-- within a single operation. Field duplication in the selection set causes
-- redundant database calls. Deeply nested objects trigger N+1 query patterns
-- that can exhaust database connection pools. Without a complexity budget
-- enforced at parse time, no single query is obviously too expensive until
-- the resolver has already begun execution.

namespace Gnosis.Security.GraphQLBatchingAmplificationRisk

-- Batch amplification: N operations in one HTTP request bypasses per-request limit
def batchAmplificationRisk (batchingEnabled : Bool) (rateLimitPerHTTPRequest : Bool)
    (rateLimitPerOperation : Bool) : Bool :=
  batchingEnabled && rateLimitPerHTTPRequest && !rateLimitPerOperation

theorem rate_limit_per_operation_safe (batching perReq : Bool) :
    batchAmplificationRisk batching perReq true = false := by { simp [batchAmplificationRisk]

theorem batching_disabled_safe (perReq perOp : Bool) :
    batchAmplificationRisk false perReq perOp = false := by
  simp [batchAmplificationRisk]

theorem per_request_only_with_batching_risky :
    batchAmplificationRisk true true false = true := by
  simp [batchAmplificationRisk]

-- Alias amplification: same expensive field under many aliases in one query
def aliasAmplificationRisk (maxAliasCount : Nat) (aliasCountInQuery : Nat)
    (aliasLimitEnforced : Bool) : Bool :=
  !aliasLimitEnforced && maxAliasCount < aliasCountInQuery

theorem alias_limit_enforced_safe (maxAlias queryAlias : Nat) :
    aliasAmplificationRisk maxAlias queryAlias true = false := by
  simp [aliasAmplificationRisk]

theorem query_within_alias_limit_safe (maxAlias : Nat) :
    aliasAmplificationRisk maxAlias maxAlias false = false := by
  simp [aliasAmplificationRisk]

theorem excess_aliases_no_limit_risky (maxAlias queryAlias : Nat)
    (h : maxAlias < queryAlias) :
    aliasAmplificationRisk maxAlias queryAlias false = true := by
  simp [aliasAmplificationRisk, h]

-- N+1 query pattern: nested object resolution triggers N database queries
def nPlusOneQueryRisk (resolverUsesDataLoader : Bool)
    (nestingDepth : Nat) (maxSafeNestingDepth : Nat) : Bool :=
  !resolverUsesDataLoader && maxSafeNestingDepth < nestingDepth

theorem dataloader_prevents_n_plus_one (depth maxDepth : Nat) :
    nPlusOneQueryRisk true depth maxDepth = false := by
  simp [nPlusOneQueryRisk]

theorem shallow_nesting_safe (useDataLoader : Bool) (depth maxDepth : Nat)
    (h : depth ≤ maxDepth) :
    nPlusOneQueryRisk useDataLoader depth maxDepth = false := by
  simp [nPlusOneQueryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem deep_nesting_without_dataloader_risky (depth maxDepth : Nat)
    (h : maxDepth < depth) :
    nPlusOneQueryRisk false depth maxDepth = true := by { simp [nPlusOneQueryRisk, h]

-- Field duplication: same field selected multiple times causes redundant resolves
def fieldDuplicationRisk (fieldDeduplicationEnforced : Bool)
    (duplicateFieldsInQuery : Bool) : Bool :=
  !fieldDeduplicationEnforced && duplicateFieldsInQuery

theorem deduplication_enforced_safe (duplicates : Bool) :
    fieldDuplicationRisk true duplicates = false := by
  simp [fieldDuplicationRisk]

theorem no_duplicate_fields_safe (dedup : Bool) :
    fieldDuplicationRisk dedup false = false := by
  simp [fieldDuplicationRisk]

theorem no_dedup_with_duplicates_risky :
    fieldDuplicationRisk false true = true := by
  simp [fieldDuplicationRisk]

-- Complexity budget: query cost not bounded at parse time
def complexityBudgetRisk (complexityLimitEnforced : Bool) (queryComplexity : Nat)
    (maxAllowedComplexity : Nat) : Bool :=
  !complexityLimitEnforced || maxAllowedComplexity < queryComplexity

theorem complexity_limit_within_budget_safe (complexity maxComplexity : Nat)
    (h : complexity ≤ maxComplexity) :
    complexityBudgetRisk true complexity maxComplexity = false := by
  simp [complexityBudgetRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem complexity_limit_not_enforced_risky (complexity maxComplexity : Nat) :
    complexityBudgetRisk false complexity maxComplexity = true := by { simp [complexityBudgetRisk]

theorem query_exceeds_complexity_budget_risky (complexity maxComplexity : Nat)
    (h : maxComplexity < complexity) :
    complexityBudgetRisk true complexity maxComplexity = true := by
  simp [complexityBudgetRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Aggregate GraphQL batching amplification risk count
def aggregateGraphQLBatchingRisk
    (batchingEnabled perReqLimit perOpLimit : Bool)
    (maxAlias queryAlias : Nat) (aliasLimitEnforced : Bool)
    (dataLoader : Bool) (nestingDepth maxNestingDepth : Nat)
    (dedupEnforced dupFields : Bool)
    (complexityEnforced : Bool) (queryComplexity maxComplexity : Nat) : Nat :=
  (if batchAmplificationRisk batchingEnabled perReqLimit perOpLimit then 1 else 0) +
  (if aliasAmplificationRisk maxAlias queryAlias aliasLimitEnforced then 1 else 0) +
  (if nPlusOneQueryRisk dataLoader nestingDepth maxNestingDepth then 1 else 0) +
  (if fieldDuplicationRisk dedupEnforced dupFields then 1 else 0) +
  (if complexityBudgetRisk complexityEnforced queryComplexity maxComplexity then 1 else 0)

theorem fully_hardened_zero_graphql_batching_risk :
    aggregateGraphQLBatchingRisk
      true false true
      10 5 true
      true 3 10
      true false
      true 100 1000 = 0 := by { simp [aggregateGraphQLBatchingRisk, batchAmplificationRisk, aliasAmplificationRisk,
        nPlusOneQueryRisk, fieldDuplicationRisk, complexityBudgetRisk]

theorem all_graphql_batching_vectors_max_risk :
    aggregateGraphQLBatchingRisk
      true true false
      10 100 false
      false 20 10
      false true
      false 1000 100 = 5 := by
  simp [aggregateGraphQLBatchingRisk, batchAmplificationRisk, aliasAmplificationRisk,
        nPlusOneQueryRisk, fieldDuplicationRisk, complexityBudgetRisk]

theorem graphql_batching_risk_bounded
    (batchingEnabled perReqLimit perOpLimit : Bool)
    (maxAlias queryAlias : Nat) (aliasLimitEnforced : Bool)
    (dataLoader : Bool) (nestingDepth maxNestingDepth : Nat)
    (dedupEnforced dupFields : Bool)
    (complexityEnforced : Bool) (queryComplexity maxComplexity : Nat) :
    aggregateGraphQLBatchingRisk
      batchingEnabled perReqLimit perOpLimit
      maxAlias queryAlias aliasLimitEnforced
      dataLoader nestingDepth maxNestingDepth
      dedupEnforced dupFields
      complexityEnforced queryComplexity maxComplexity ≤ 5 := by
  simp [aggregateGraphQLBatchingRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: GraphQL amplification detection prevents DoS-driven revenue loss
def graphqlAmplificationDetectionValueCents (dosImpactCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (dosImpactCostCents : Int) - (scannerCostCents : Int)

theorem graphql_amplification_scanner_profitable (dosImpact scan : Nat) (h : scan < dosImpact) :
    0 < graphqlAmplificationDetectionValueCents dosImpact scan := by
  simp [graphqlAmplificationDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem graphql_amplification_scanner_break_even (cost : Nat) :
    0 ≤ graphqlAmplificationDetectionValueCents cost cost := by
  simp [graphqlAmplificationDetectionValueCents]

-- Fleet ROI: GraphQL batching scan across all GraphQL APIs
def graphqlBatchingFleetROI (detectionValueCents : Nat) (graphqlAPIs : Nat) : Nat :=
  detectionValueCents * graphqlAPIs

theorem graphql_batching_fleet_roi_monotone (v a1 a2 : Nat) (h : a1 ≤ a2) :
    graphqlBatchingFleetROI v a1 ≤ graphqlBatchingFleetROI v a2 := by
  simp [graphqlBatchingFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_graphql_batching_fleet_roi (v a : Nat) (hv : 0 < v) (ha : 0 < a) :
    0 < graphqlBatchingFleetROI v a := by
  simp [graphqlBatchingFleetROI]
  exact Nat.mul_pos hv ha

end GraphQLBatchingAmplificationRisk
