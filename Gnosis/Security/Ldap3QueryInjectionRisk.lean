import Init
-- Ldap3QueryInjectionRisk.lean
-- Anti-thesis: LDAP search filter construction from user input via ldap3
-- (Python) cannot introduce LDAP injection vulnerabilities.
-- Refutation: unescaped user input in filter strings and unvalidated DN
-- components each yield a strictly positive vulnerability window.

namespace Ldap3QueryInjection

-- LDAP filter injection: search(filter="(uid=" + user_input + ")")
def ldapFilterRisk (inputLen : Nat) (escaped : Bool) : Nat :=
  if escaped then 0 else inputLen + 1

-- escape_filter_chars() eliminates filter injection
theorem ldap3_filter_escaped_safe (n : Nat) :
    ldapFilterRisk n true = 0 := by { simp [ldapFilterRisk]

-- Unescaped user input in LDAP filter is strictly vulnerable
theorem ldap3_filter_unescaped_risk (n : Nat) :
    0 < ldapFilterRisk n false := by
  simp [ldapFilterRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- DN injection: search base_dn assembled from user input
def dnComponentRisk (dnLen : Nat) (escaped : Bool) : Nat :=
  if escaped then 0 else dnLen + 1

theorem ldap3_dn_escaped_safe (n : Nat) :
    dnComponentRisk n true = 0 := by { simp [dnComponentRisk]

theorem ldap3_dn_unescaped_risk (n : Nat) :
    0 < dnComponentRisk n false := by
  simp [dnComponentRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Attribute value injection: modify() with user-controlled attribute value
def attrValueRisk (valueLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else valueLen + 1

theorem ldap3_attr_value_validated_safe (n : Nat) :
    attrValueRisk n true = 0 := by { simp [attrValueRisk]

theorem ldap3_attr_value_unvalidated_risk (n : Nat) :
    0 < attrValueRisk n false := by
  simp [attrValueRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Wildcard amplification: "*" in filter enables full enumeration
def wildcardRisk (filterLen : Nat) (escaped : Bool) : Nat :=
  if escaped then 0 else filterLen + 1

theorem ldap3_wildcard_escaped_safe (n : Nat) :
    wildcardRisk n true = 0 := by { simp [wildcardRisk]

theorem ldap3_wildcard_unescaped_risk (n : Nat) :
    0 < wildcardRisk n false := by
  simp [wildcardRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Bind DN injection: user-controlled bind credential (simple_bind_s)
def bindDnRisk (dnLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else dnLen + 1

theorem ldap3_bind_dn_allowlisted_safe (n : Nat) :
    bindDnRisk n true = 0 := by { simp [bindDnRisk]

theorem ldap3_bind_dn_unvalidated_risk (n : Nat) :
    0 < bindDnRisk n false := by
  simp [bindDnRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem ldap3_filter_risk_monotone (n m : Nat) (h : n ≤ m) :
    ldapFilterRisk n false ≤ ldapFilterRisk m false := by { simp [ldapFilterRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires escaped filter AND escaped DN components
def netLdap3Risk (inputLen : Nat) (filterEscaped : Bool) (dnEscaped : Bool) : Nat :=
  ldapFilterRisk inputLen filterEscaped + dnComponentRisk inputLen dnEscaped

theorem ldap3_net_risk_zero_fully_mitigated (n : Nat) :
    netLdap3Risk n true true = 0 := by { simp [netLdap3Risk, ldapFilterRisk, dnComponentRisk]

theorem ldap3_net_risk_pos_unmitigated (n : Nat) :
    0 < netLdap3Risk n false false := by
  simp [netLdap3Risk, ldapFilterRisk, dnComponentRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end Ldap3QueryInjection
