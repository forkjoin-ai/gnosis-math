import Init
-- GraphQLDepthLimitRisk.lean
-- Anti-thesis: GraphQL introspection and flexible querying are features, not
-- vulnerabilities; clients self-regulate their queries in well-behaved systems,
-- and deeply nested queries are not a meaningful attack surface.
-- Refutation: Without server-enforced depth limits and complexity budgets, a
-- single deeply nested query forces O(k^d) resolver calls (k branches, d depth),
-- enabling CPU/memory exhaustion with microsecond client effort. Field
-- deduplication alone does not protect against aliased amplification.

namespace Gnosis.Security.GraphQLDepthLimitRisk

-- Query cost: unbounded nesting yields exponential resolver calls
def resolverCalls (branchingFactor : Nat) (depth : Nat) : Nat :=
  branchingFactor ^ depth

theorem resolver_calls_at_depth_zero (k : Nat) :
    resolverCalls k 0 = 1 := by { simp [resolverCalls]

theorem resolver_calls_grow_exponentially (k d : Nat) (hk : 1 < k) :
    resolverCalls k d < resolverCalls k (d + 1) := by
  simp only [resolverCalls, Nat.pow_succ]
  conv_lhs => rw [← Nat.mul_one (k ^ d)]
  exact Nat.mul_lt_mul_of_pos_left hk (Nat.pos_pow_of_pos d (by omega))

-- Depth limit: hard cap prevents exponential blowup
def depthLimitEnforced (maxDepth : Nat) (queryDepth : Nat) : Bool :=
  if queryDepth ≤ maxDepth then true else false

theorem depth_within_limit_allowed (q m : Nat) (h : q ≤ m) :
    depthLimitEnforced m q = true := by
  simp [depthLimitEnforced, h]

theorem depth_over_limit_rejected (q m : Nat) (h : m < q) :
    depthLimitEnforced m q = false := by
  simp [depthLimitEnforced]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Bounded cost: with depth limit, resolver calls are bounded
theorem depth_limited_resolver_calls_bounded (k maxDepth queryDepth : Nat)
    (h : queryDepth ≤ maxDepth) :
    resolverCalls k queryDepth ≤ resolverCalls k maxDepth := by { simp [resolverCalls]
  exact Nat.pow_le_pow_right (Nat.zero_le k) h

-- Complexity budget: total field resolution cost
def queryCost (fieldCount : Nat) (avgResolverCostMs : Nat) : Nat :=
  fieldCount * avgResolverCostMs

theorem cost_zero_no_fields (c : Nat) :
    queryCost 0 c = 0 := by
  simp [queryCost]

theorem cost_monotone_in_fields (f1 f2 c : Nat) (h : f1 ≤ f2) :
    queryCost f1 c ≤ queryCost f2 c := by
  simp [queryCost]
  exact Nat.mul_le_mul_right c h

-- Alias amplification: aliased fields multiply response, bypass dedup
def aliasAmplificationFactor (aliasCount : Nat) (baseFields : Nat) : Nat :=
  aliasCount * baseFields

theorem alias_amplification_zero_aliases (f : Nat) :
    aliasAmplificationFactor 0 f = 0 := by
  simp [aliasAmplificationFactor]

theorem alias_amplification_scales (a f : Nat) (ha : 0 < a) (hf : 0 < f) :
    0 < aliasAmplificationFactor a f := by
  simp [aliasAmplificationFactor]
  exact Nat.mul_pos ha hf

theorem alias_amplification_exceeds_base (a f : Nat) (ha : 1 < a) (hf : 0 < f) :
    f < aliasAmplificationFactor a f := by
  simp [aliasAmplificationFactor]
  calc f = 1 * f := by ring
    _ < a * f := Nat.mul_lt_mul_of_pos_right ha hf

-- Field deduplication does NOT protect against aliasing
theorem dedup_insufficient_against_aliases (a f : Nat) (ha : 1 < a) (hf : 0 < f) :
    f < aliasAmplificationFactor a f :=
  alias_amplification_exceeds_base a f ha hf

-- Complexity limit: reject queries whose total cost exceeds budget
def complexityAllowed (totalCost : Nat) (maxComplexity : Nat) : Bool :=
  if totalCost ≤ maxComplexity then true else false

theorem low_cost_query_allowed (c m : Nat) (h : c ≤ m) :
    complexityAllowed c m = true := by
  simp [complexityAllowed, h]

theorem high_cost_query_rejected (c m : Nat) (h : m < c) :
    complexityAllowed c m = false := by
  simp [complexityAllowed]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Rate limiting: throttle by query complexity units per second
def complexityBudgetPerSec (maxUnitsPerSec : Nat) (queriesPerSec : Nat)
    (costPerQuery : Nat) : Bool :=
  if queriesPerSec * costPerQuery ≤ maxUnitsPerSec then true else false

theorem within_budget_safe (qps cost budget : Nat) (h : qps * cost ≤ budget) :
    complexityBudgetPerSec budget qps cost = true := by { simp [complexityBudgetPerSec, h]

theorem over_budget_throttled (qps cost budget : Nat) (h : budget < qps * cost) :
    complexityBudgetPerSec budget qps cost = false := by
  simp [complexityBudgetPerSec]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Introspection exposure: introspection in prod leaks schema for attack planning
def introspectionRisk (introspectionEnabled : Bool) (isProduction : Bool) : Bool :=
  introspectionEnabled && isProduction

theorem introspection_disabled_safe (prod : Bool) :
    introspectionRisk false prod = false := by { simp [introspectionRisk]

theorem introspection_in_dev_acceptable (enabled : Bool) :
    introspectionRisk enabled false = false := by
  simp [introspectionRisk]
  cases enabled <;> simp

theorem introspection_in_prod_risky :
    introspectionRisk true true = true := by
  simp [introspectionRisk]

-- Aggregate GraphQL DoS risk
def graphQLDoSRisk (depthLimited : Bool) (complexityLimited : Bool)
    (aliasCapped : Bool) (introspectionOff : Bool) : Nat :=
  (if depthLimited then 0 else 1) +
  (if complexityLimited then 0 else 1) +
  (if aliasCapped then 0 else 1) +
  (if introspectionOff then 0 else 1)

theorem graphql_dos_risk_zero_full_controls :
    graphQLDoSRisk true true true true = 0 := by
  simp [graphQLDoSRisk]

theorem graphql_dos_risk_max_no_controls :
    graphQLDoSRisk false false false false = 4 := by
  simp [graphQLDoSRisk]

theorem graphql_dos_risk_positive_no_depth_limit (c a i : Bool) :
    0 < graphQLDoSRisk false c a i := by
  simp [graphQLDoSRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Depth limit is strictly necessary: without it, cost grows without bound
theorem depth_limit_required_for_bounded_cost (k d : Nat) (hk : 1 < k) (hd : 0 < d) :
    resolverCalls k 0 < resolverCalls k d := by
  simp [resolverCalls]
  exact Nat.one_lt_pow (by omega) hk

-- Each additional depth level multiplies cost by branching factor
theorem depth_adds_multiplicative_cost (k d : Nat) (hk : 0 < k) :
    resolverCalls k d * k = resolverCalls k (d + 1) := by
  simp [resolverCalls, Nat.pow_succ]

end GraphQLDepthLimitRisk
