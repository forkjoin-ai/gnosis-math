import Init
-- PyYAMLQueryInjectionRisk.lean
-- Anti-thesis: PyYAML yaml.load() of user-supplied YAML strings carries
-- no code execution risk because YAML is a data format.
-- Refutation: yaml.load() with the default Loader (FullLoader or is_unsafe Loader)
-- executes Python constructors, yielding a strictly positive vulnerability window.

namespace PyYAMLQueryInjection

-- yaml.load() code execution: user YAML with !!python/object constructor
def yamlLoadRisk (inputLen : Nat) (safeLoader : Bool) : Nat :=
  if safeLoader then 0 else inputLen + 1

-- yaml.safe_load() uses SafeLoader and eliminates arbitrary code execution
theorem pyyaml_safe_load_safe (n : Nat) :
    yamlLoadRisk n true = 0 := by { simp [yamlLoadRisk]

-- yaml.load() with default or FullLoader is strictly vulnerable
theorem pyyaml_unsafe_load_risk (n : Nat) :
    0 < yamlLoadRisk n false := by
  simp [yamlLoadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- !!python/object/apply: gadget chain execution risk
def pythonObjectRisk (inputLen : Nat) (safeLoader : Bool) : Nat :=
  if safeLoader then 0 else inputLen + 1

theorem pyyaml_object_apply_safe_loader (n : Nat) :
    pythonObjectRisk n true = 0 := by { simp [pythonObjectRisk]

theorem pyyaml_object_apply_unsafe_risk (n : Nat) :
    0 < pythonObjectRisk n false := by
  simp [pythonObjectRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- yaml.load_all() (multi-document) has same risk as yaml.load()
def yamlLoadAllRisk (inputLen : Nat) (safeLoader : Bool) : Nat :=
  if safeLoader then 0 else inputLen + 1

theorem pyyaml_load_all_safe_loader (n : Nat) :
    yamlLoadAllRisk n true = 0 := by { simp [yamlLoadAllRisk]

theorem pyyaml_load_all_unsafe_risk (n : Nat) :
    0 < yamlLoadAllRisk n false := by
  simp [yamlLoadAllRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Anchor/alias bomb: deeply nested anchors cause DoS
def anchorBombRisk (depth : Nat) (depthLimited : Bool) : Nat :=
  if depthLimited then 0 else depth + 1

theorem pyyaml_anchor_depth_limited_safe (n : Nat) :
    anchorBombRisk n true = 0 := by { simp [anchorBombRisk]

theorem pyyaml_anchor_depth_unlimited_risk (n : Nat) :
    0 < anchorBombRisk n false := by
  simp [anchorBombRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Configuration file injection: yaml.load of config with user-controlled keys
def configKeyRisk (keyLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else keyLen + 1

theorem pyyaml_config_key_validated_safe (n : Nat) :
    configKeyRisk n true = 0 := by { simp [configKeyRisk]

theorem pyyaml_config_key_unvalidated_risk (n : Nat) :
    0 < configKeyRisk n false := by
  simp [configKeyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in input length
theorem pyyaml_load_risk_monotone (n m : Nat) (h : n ≤ m) :
    yamlLoadRisk n false ≤ yamlLoadRisk m false := by { simp [yamlLoadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires SafeLoader AND depth-limited parsing
def netPyYAMLRisk (inputLen : Nat) (safeLoader : Bool) (depthLimited : Bool) : Nat :=
  yamlLoadRisk inputLen safeLoader + anchorBombRisk inputLen depthLimited

theorem pyyaml_net_risk_zero_fully_mitigated (n : Nat) :
    netPyYAMLRisk n true true = 0 := by { simp [netPyYAMLRisk, yamlLoadRisk, anchorBombRisk]

theorem pyyaml_net_risk_pos_unmitigated (n : Nat) :
    0 < netPyYAMLRisk n false false := by
  simp [netPyYAMLRisk, yamlLoadRisk, anchorBombRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end PyYAMLQueryInjection
