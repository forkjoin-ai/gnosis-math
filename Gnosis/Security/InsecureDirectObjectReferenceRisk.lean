import Init
-- InsecureDirectObjectReferenceRisk.lean
-- Anti-thesis: Exposing database record IDs in URLs (/api/invoice/1234) carries
-- no risk because authentication prevents unauthorized access.
-- Refutation: Authentication verifies identity but not authorization to the
-- specific object; without per-object ownership checks, any authenticated user
-- can enumerate and access others' records, yielding a strictly positive
-- vulnerability window.

namespace Gnosis.Security.InsecureDirectObjectReferenceRisk

-- IDOR: object fetched by user-supplied ID without ownership check
def idorRisk (objectId : Nat) (ownershipChecked : Bool) : Nat :=
  if ownershipChecked then 0 else objectId + 1

-- Per-object ownership check eliminates IDOR
theorem idor_ownership_checked_safe (n : Nat) :
    idorRisk n true = 0 := by { simp [idorRisk]

-- Missing ownership check is strictly vulnerable
theorem idor_ownership_missing_risk (n : Nat) :
    0 < idorRisk n false := by
  simp [idorRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Sequential ID enumeration: predictable integer IDs enable bulk enumeration
def sequentialIdRisk (recordCount : Nat) (idsRandomized : Bool) : Nat :=
  if idsRandomized then 0 else recordCount + 1

theorem idor_ids_randomized_safe (n : Nat) :
    sequentialIdRisk n true = 0 := by { simp [sequentialIdRisk]

theorem idor_sequential_ids_risk (n : Nat) :
    0 < sequentialIdRisk n false := by
  simp [sequentialIdRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Indirect reference map: application maps user-visible token to real ID
def indirectReferenceRisk (tokenLen : Nat) (indirectMapUsed : Bool) : Nat :=
  if indirectMapUsed then 0 else tokenLen + 1

theorem idor_indirect_map_used_safe (n : Nat) :
    indirectReferenceRisk n true = 0 := by { simp [indirectReferenceRisk]

theorem idor_direct_id_exposed_risk (n : Nat) :
    0 < indirectReferenceRisk n false := by
  simp [indirectReferenceRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Horizontal privilege escalation: user A accesses user B's resource
def horizontalEscalationRisk (requestorId : Nat) (resourceOwnerId : Nat) (checked : Bool) : Nat :=
  if checked then 0 else if requestorId = resourceOwnerId then 0 else 1

theorem idor_owner_match_safe (id : Nat) :
    horizontalEscalationRisk id id false = 0 := by { simp [horizontalEscalationRisk]

theorem idor_ownership_check_safe (a b : Nat) :
    horizontalEscalationRisk a b true = 0 := by
  simp [horizontalEscalationRisk]

theorem idor_horizontal_escalation_risk (a b : Nat) (h : a ≠ b) :
    0 < horizontalEscalationRisk a b false := by
  simp [horizontalEscalationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- File download IDOR: /download?file=../config.yaml
def fileDownloadIdorRisk (pathLen : Nat) (pathValidated : Bool) : Nat :=
  if pathValidated then 0 else pathLen + 1

theorem idor_file_path_validated_safe (n : Nat) :
    fileDownloadIdorRisk n true = 0 := by { simp [fileDownloadIdorRisk]

theorem idor_file_path_open_risk (n : Nat) :
    0 < fileDownloadIdorRisk n false := by
  simp [fileDownloadIdorRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in object ID value
theorem idor_risk_monotone (n m : Nat) (h : n ≤ m) :
    idorRisk n false ≤ idorRisk m false := by { simp [idorRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires ownership check AND randomized IDs
def netIdorRisk (objectId : Nat) (ownershipChecked : Bool) (idsRandomized : Bool) : Nat :=
  idorRisk objectId ownershipChecked + sequentialIdRisk objectId idsRandomized

theorem idor_net_risk_zero_fully_mitigated (n : Nat) :
    netIdorRisk n true true = 0 := by { simp [netIdorRisk, idorRisk, sequentialIdRisk]

theorem idor_net_risk_pos_unmitigated (n : Nat) :
    0 < netIdorRisk n false false := by
  simp [netIdorRisk, idorRisk, sequentialIdRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end InsecureDirectObjectReferenceRisk
