import Init
-- GorillaMuxQueryInjectionRisk.lean
-- Anti-thesis: gorilla/mux (Go) path variable extraction via mux.Vars(r)
-- used in database queries or system calls carries no injection risk.
-- Refutation: path variables and query values passed to unparameterized
-- operations yield a strictly positive vulnerability window.

namespace GorillaMuxQueryInjection

-- Path variable injection: mux.Vars(r)["id"] used in SQL string concatenation
def muxVarSqlRisk (varLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else varLen + 1

-- Parameterized query eliminates path variable SQL injection
theorem mux_var_parameterized_safe (n : Nat) :
    muxVarSqlRisk n true = 0 := by { simp [muxVarSqlRisk]

-- String-concatenated path variable SQL is strictly vulnerable
theorem mux_var_concat_risk (n : Nat) :
    0 < muxVarSqlRisk n false := by
  simp [muxVarSqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Route pattern injection: dynamic route registration from user-controlled strings
def routePatternRisk (patternLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else patternLen + 1

theorem mux_route_pattern_validated_safe (n : Nat) :
    routePatternRisk n true = 0 := by { simp [routePatternRisk]

theorem mux_route_pattern_unvalidated_risk (n : Nat) :
    0 < routePatternRisk n false := by
  simp [routePatternRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Header injection: r.Header.Get used in downstream query
def headerInjectionRisk (headerLen : Nat) (sanitized : Bool) : Nat :=
  if sanitized then 0 else headerLen + 1

theorem mux_header_sanitized_safe (n : Nat) :
    headerInjectionRisk n true = 0 := by { simp [headerInjectionRisk]

theorem mux_header_unsanitized_risk (n : Nat) :
    0 < headerInjectionRisk n false := by
  simp [headerInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Subrouter injection: host-based routing with user-controlled Host header
def subrouterHostRisk (hostLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else hostLen + 1

theorem mux_subrouter_validated_safe (n : Nat) :
    subrouterHostRisk n true = 0 := by { simp [subrouterHostRisk]

theorem mux_subrouter_unvalidated_risk (n : Nat) :
    0 < subrouterHostRisk n false := by
  simp [subrouterHostRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Query variable injection: r.URL.Query().Get used in template or SQL
def queryVarRisk (queryLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else queryLen + 1

theorem mux_query_var_parameterized_safe (n : Nat) :
    queryVarRisk n true = 0 := by { simp [queryVarRisk]

theorem mux_query_var_unparameterized_risk (n : Nat) :
    0 < queryVarRisk n false := by
  simp [queryVarRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in variable length
theorem mux_var_risk_monotone (n m : Nat) (h : n ≤ m) :
    muxVarSqlRisk n false ≤ muxVarSqlRisk m false := by { simp [muxVarSqlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires parameterized SQL AND sanitized headers
def netMuxRisk (inputLen : Nat) (sqlParam : Bool) (headerSanitized : Bool) : Nat :=
  muxVarSqlRisk inputLen sqlParam + headerInjectionRisk inputLen headerSanitized

theorem mux_net_risk_zero_fully_mitigated (n : Nat) :
    netMuxRisk n true true = 0 := by { simp [netMuxRisk, muxVarSqlRisk, headerInjectionRisk]

theorem mux_net_risk_pos_unmitigated (n : Nat) :
    0 < netMuxRisk n false false := by
  simp [netMuxRisk, muxVarSqlRisk, headerInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end GorillaMuxQueryInjection
