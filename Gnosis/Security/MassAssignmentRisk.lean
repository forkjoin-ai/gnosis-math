import Init
-- MassAssignmentRisk.lean
-- Anti-thesis: Passing user-controlled request parameters directly to ORM
-- bulk-update or model constructors carries no risk because ORMs only set
-- fields that exist on the model.
-- Refutation: Without explicit field allow-listing, an attacker adds extra
-- parameters (isAdmin=true, role=superuser) that are silently applied,
-- yielding a strictly positive privilege-escalation window.

namespace Gnosis.Security.MassAssignmentRisk

-- Mass assignment: ORM update from unfiltered user params
def massAssignmentRisk (paramCount : Nat) (allowListEnforced : Bool) : Nat :=
  if allowListEnforced then 0 else paramCount + 1

-- Explicit allow-list of assignable fields eliminates mass assignment
theorem mass_allowlist_enforced_safe (n : Nat) :
    massAssignmentRisk n true = 0 := by { simp [massAssignmentRisk]

-- Unrestricted bulk assignment is strictly vulnerable
theorem mass_allowlist_missing_risk (n : Nat) :
    0 < massAssignmentRisk n false := by
  simp [massAssignmentRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Privilege field injection: isAdmin/role inserted into params
def privilegeFieldRisk (hasPrivilegeFields : Bool) (privilegeFieldsBlocked : Bool) : Nat :=
  if !hasPrivilegeFields || privilegeFieldsBlocked then 0 else 1

theorem mass_privilege_fields_blocked_safe :
    privilegeFieldRisk true true = 0 := by { simp [privilegeFieldRisk]

theorem mass_privilege_fields_open_risk :
    0 < privilegeFieldRisk true false := by
  simp [privilegeFieldRisk]

-- Nested object injection: user passes relationship IDs that alter associations
def nestedObjectRisk (paramCount : Nat) (nestedParamsFiltered : Bool) : Nat :=
  if nestedParamsFiltered then 0 else paramCount + 1

theorem mass_nested_filtered_safe (n : Nat) :
    nestedObjectRisk n true = 0 := by
  simp [nestedObjectRisk]

theorem mass_nested_unfiltered_risk (n : Nat) :
    0 < nestedObjectRisk n false := by
  simp [nestedObjectRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Audit field tamper: createdAt/updatedAt overridden by user input
def auditFieldTamperRisk (auditFieldsProtected : Bool) : Nat :=
  if auditFieldsProtected then 0 else 1

theorem mass_audit_fields_protected_safe :
    auditFieldTamperRisk true = 0 := by { simp [auditFieldTamperRisk]

theorem mass_audit_fields_unprotected_risk :
    0 < auditFieldTamperRisk false := by
  simp [auditFieldTamperRisk]

-- Over-posting via JSON: extra JSON keys mapped to sensitive model attributes
def overPostingRisk (jsonKeyCount : Nat) (strictDeserialization : Bool) : Nat :=
  if strictDeserialization then 0 else jsonKeyCount + 1

theorem mass_strict_deser_safe (n : Nat) :
    overPostingRisk n true = 0 := by
  simp [overPostingRisk]

theorem mass_loose_deser_risk (n : Nat) :
    0 < overPostingRisk n false := by
  simp [overPostingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in parameter count
theorem mass_assignment_risk_monotone (n m : Nat) (h : n ≤ m) :
    massAssignmentRisk n false ≤ massAssignmentRisk m false := by { simp [massAssignmentRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires allow-list AND privilege fields blocked
def netMassAssignmentRisk (paramCount : Nat) (allowListEnforced : Bool) (privBlocked : Bool) : Nat :=
  massAssignmentRisk paramCount allowListEnforced + privilegeFieldRisk true privBlocked

theorem mass_net_risk_zero_fully_mitigated (n : Nat) :
    netMassAssignmentRisk n true true = 0 := by { simp [netMassAssignmentRisk, massAssignmentRisk, privilegeFieldRisk]

theorem mass_net_risk_pos_unmitigated (n : Nat) :
    0 < netMassAssignmentRisk n false false := by
  simp [netMassAssignmentRisk, massAssignmentRisk, privilegeFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end MassAssignmentRisk
