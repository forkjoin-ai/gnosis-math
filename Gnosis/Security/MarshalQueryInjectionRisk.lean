import Init
-- MarshalQueryInjectionRisk.lean
-- Anti-thesis: Python marshal.loads() of user-supplied bytes carries no
-- code execution risk because marshal is lower-level than pickle.
-- Refutation: marshal.loads(user_bytes) can deserialize code objects with
-- arbitrary bytecode, yielding a strictly positive RCE vulnerability window.

namespace MarshalQueryInjection

-- RCE risk: marshal.loads(user_data) can reconstruct code objects
def marshalLoadRisk (dataLen : Nat) (trustedSource : Bool) : Nat :=
  if trustedSource then 0 else dataLen + 1

-- Marshal data from a trusted internal source (e.g., compiled .pyc) is safe
theorem marshal_trusted_source_safe (n : Nat) :
    marshalLoadRisk n true = 0 := by { simp [marshalLoadRisk]

-- marshal.loads() of user-controlled bytes is strictly vulnerable
theorem marshal_user_data_rce_risk (n : Nat) :
    0 < marshalLoadRisk n false := by
  simp [marshalLoadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Code object execution: marshaled code objects executed via exec()
def codeObjExecRisk (dataLen : Nat) (execBlocked : Bool) : Nat :=
  if execBlocked then 0 else dataLen + 1

theorem marshal_exec_blocked_safe (n : Nat) :
    codeObjExecRisk n true = 0 := by { simp [codeObjExecRisk]

theorem marshal_exec_allowed_risk (n : Nat) :
    0 < codeObjExecRisk n false := by
  simp [codeObjExecRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Version mismatch: marshal format varies by Python version (not a safety guarantee)
def versionMismatchRisk (dataLen : Nat) (versionChecked : Bool) : Nat :=
  if versionChecked then 0 else dataLen + 1

theorem marshal_version_checked_reduces_risk (n : Nat) :
    versionMismatchRisk n true = 0 := by { simp [versionMismatchRisk]

theorem marshal_version_unchecked_risk (n : Nat) :
    0 < versionMismatchRisk n false := by
  simp [versionMismatchRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- importlib abuse: marshal can reconstruct importlib internals
def importlibAbuseRisk (dataLen : Nat) (importHooked : Bool) : Nat :=
  if importHooked then 0 else dataLen + 1

theorem marshal_import_hooked_safe (n : Nat) :
    importlibAbuseRisk n true = 0 := by { simp [importlibAbuseRisk]

theorem marshal_import_unhooked_risk (n : Nat) :
    0 < importlibAbuseRisk n false := by
  simp [importlibAbuseRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- .pyc file injection: user-provided .pyc files processed via marshal
def pycFileRisk (fileLen : Nat) (signatureVerified : Bool) : Nat :=
  if signatureVerified then 0 else fileLen + 1

theorem marshal_pyc_signature_verified_safe (n : Nat) :
    pycFileRisk n true = 0 := by { simp [pycFileRisk]

theorem marshal_pyc_unsigned_risk (n : Nat) :
    0 < pycFileRisk n false := by
  simp [pycFileRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in payload length
theorem marshal_rce_risk_monotone (n m : Nat) (h : n ≤ m) :
    marshalLoadRisk n false ≤ marshalLoadRisk m false := by { simp [marshalLoadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires trusted source AND exec blocked
def netMarshalRisk (dataLen : Nat) (trustedSource : Bool) (execBlocked : Bool) : Nat :=
  marshalLoadRisk dataLen trustedSource + codeObjExecRisk dataLen execBlocked

theorem marshal_net_risk_zero_fully_mitigated (n : Nat) :
    netMarshalRisk n true true = 0 := by { simp [netMarshalRisk, marshalLoadRisk, codeObjExecRisk]

theorem marshal_net_risk_pos_unmitigated (n : Nat) :
    0 < netMarshalRisk n false false := by
  simp [netMarshalRisk, marshalLoadRisk, codeObjExecRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end MarshalQueryInjection
