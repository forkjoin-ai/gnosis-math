import Init
-- GraphQLQueryInjectionRisk.lean
-- Anti-thesis: GraphQL query construction from user-controlled strings via
-- string interpolation into query documents carries no injection risk.
-- Refutation: unparameterized GraphQL query documents with user input and
-- aliased field enumeration each yield a strictly positive vulnerability window.

namespace GraphQLQueryInjection

-- Query document injection: building GraphQL queries via string interpolation
def queryDocRisk (inputLen : Nat) (usesVariables : Bool) : Nat :=
  if usesVariables then 0 else inputLen + 1

-- GraphQL variables ($var) eliminate query document injection
theorem graphql_variables_safe (n : Nat) :
    queryDocRisk n true = 0 := by { simp [queryDocRisk]

-- String-interpolated GraphQL query document is strictly vulnerable
theorem graphql_string_interpolation_risk (n : Nat) :
    0 < queryDocRisk n false := by
  simp [queryDocRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Field argument injection: user-controlled argument value in query string
def fieldArgRisk (argLen : Nat) (usesVariables : Bool) : Nat :=
  if usesVariables then 0 else argLen + 1

theorem graphql_field_arg_variables_safe (n : Nat) :
    fieldArgRisk n true = 0 := by { simp [fieldArgRisk]

theorem graphql_field_arg_interpolation_risk (n : Nat) :
    0 < fieldArgRisk n false := by
  simp [fieldArgRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Directive injection: user-controlled directive in query document
def directiveRisk (directiveLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else directiveLen + 1

theorem graphql_directive_allowlisted_safe (n : Nat) :
    directiveRisk n true = 0 := by { simp [directiveRisk]

theorem graphql_directive_unvalidated_risk (n : Nat) :
    0 < directiveRisk n false := by
  simp [directiveRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Alias injection: user-controlled alias names enabling response shape manipulation
def aliasRisk (aliasLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else aliasLen + 1

theorem graphql_alias_validated_safe (n : Nat) :
    aliasRisk n true = 0 := by { simp [aliasRisk]

theorem graphql_alias_unvalidated_risk (n : Nat) :
    0 < aliasRisk n false := by
  simp [aliasRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Fragment injection: user-controlled fragment spread in query
def fragmentRisk (fragLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else fragLen + 1

theorem graphql_fragment_validated_safe (n : Nat) :
    fragmentRisk n true = 0 := by { simp [fragmentRisk]

theorem graphql_fragment_unvalidated_risk (n : Nat) :
    0 < fragmentRisk n false := by
  simp [fragmentRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in query document length
theorem graphql_query_risk_monotone (n m : Nat) (h : n ≤ m) :
    queryDocRisk n false ≤ queryDocRisk m false := by { simp [queryDocRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires variables AND allow-listed directives
def netGraphQLRisk (inputLen : Nat) (usesVariables : Bool) (dirAllowListed : Bool) : Nat :=
  queryDocRisk inputLen usesVariables + directiveRisk inputLen dirAllowListed

theorem graphql_net_risk_zero_fully_mitigated (n : Nat) :
    netGraphQLRisk n true true = 0 := by { simp [netGraphQLRisk, queryDocRisk, directiveRisk]

theorem graphql_net_risk_pos_unmitigated (n : Nat) :
    0 < netGraphQLRisk n false false := by
  simp [netGraphQLRisk, queryDocRisk, directiveRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end GraphQLQueryInjection
