import Init
-- PickleQueryInjectionRisk.lean
-- Anti-thesis: Python pickle.loads() of user-supplied bytes carries no
-- code execution risk because pickle is just a serialization format.
-- Refutation: pickle.loads(user_bytes) executes arbitrary Python via __reduce__,
-- yielding a strictly positive remote code execution vulnerability window.

namespace PickleQueryInjection

-- RCE risk: pickle.loads(user_data) executes __reduce__ hooks
def pickleLoadRisk (dataLen : Nat) (trustedSource : Bool) : Nat :=
  if trustedSource then 0 else dataLen + 1

-- Pickle data from a trusted internal source is safe
theorem pickle_trusted_source_safe (n : Nat) :
    pickleLoadRisk n true = 0 := by { simp [pickleLoadRisk]

-- Pickle from user-controlled source is strictly vulnerable to RCE
theorem pickle_user_data_rce_risk (n : Nat) :
    0 < pickleLoadRisk n false := by
  simp [pickleLoadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- __reduce__ RCE: gadget constructs os.system() or subprocess call
def reduceGadgetRisk (dataLen : Nat) (trustedSource : Bool) : Nat :=
  if trustedSource then 0 else dataLen + 1

theorem pickle_reduce_trusted_safe (n : Nat) :
    reduceGadgetRisk n true = 0 := by { simp [reduceGadgetRisk]

theorem pickle_reduce_untrusted_risk (n : Nat) :
    0 < reduceGadgetRisk n false := by
  simp [reduceGadgetRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- pickletools.dis() does not prevent execution: analysis != safe load
def analyzeAndLoadRisk (dataLen : Nat) (blockedBeforeLoad : Bool) : Nat :=
  if blockedBeforeLoad then 0 else dataLen + 1

theorem pickle_blocked_before_load_safe (n : Nat) :
    analyzeAndLoadRisk n true = 0 := by { simp [analyzeAndLoadRisk]

theorem pickle_analyze_then_load_risk (n : Nat) :
    0 < analyzeAndLoadRisk n false := by
  simp [analyzeAndLoadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Restricted unpickler: custom Unpickler.find_class can whitelist allowed classes
def restrictedUnpicklerRisk (dataLen : Nat) (classAllowListed : Bool) : Nat :=
  if classAllowListed then 0 else dataLen + 1

theorem pickle_class_allowlisted_safe (n : Nat) :
    restrictedUnpicklerRisk n true = 0 := by { simp [restrictedUnpicklerRisk]

theorem pickle_class_unrestricted_risk (n : Nat) :
    0 < restrictedUnpicklerRisk n false := by
  simp [restrictedUnpicklerRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- shelve module: shelve.open() uses pickle, same RCE risk
def shelveRisk (keyLen : Nat) (trustedSource : Bool) : Nat :=
  if trustedSource then 0 else keyLen + 1

theorem shelve_trusted_safe (n : Nat) :
    shelveRisk n true = 0 := by { simp [shelveRisk]

theorem shelve_user_controlled_risk (n : Nat) :
    0 < shelveRisk n false := by
  simp [shelveRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in payload length
theorem pickle_rce_risk_monotone (n m : Nat) (h : n ≤ m) :
    pickleLoadRisk n false ≤ pickleLoadRisk m false := by { simp [pickleLoadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires trusted source OR restricted Unpickler with class allowlist
def netPickleRisk (dataLen : Nat) (trustedSource : Bool) (classAllowListed : Bool) : Nat :=
  pickleLoadRisk dataLen trustedSource + restrictedUnpicklerRisk dataLen classAllowListed

theorem pickle_net_risk_zero_both_mitigated (n : Nat) :
    netPickleRisk n true true = 0 := by { simp [netPickleRisk, pickleLoadRisk, restrictedUnpicklerRisk]

theorem pickle_net_risk_pos_unmitigated (n : Nat) :
    0 < netPickleRisk n false false := by
  simp [netPickleRisk, pickleLoadRisk, restrictedUnpicklerRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end PickleQueryInjection
