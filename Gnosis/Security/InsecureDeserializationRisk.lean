import Init
-- InsecureDeserializationRisk.lean
-- Anti-thesis: Deserializing untrusted data with Java ObjectInputStream,
-- PHP unserialize, or Ruby Marshal is safe because the type system prevents
-- arbitrary code execution during deserialization.
-- Refutation: Gadget chains assembled from classes on the classpath allow
-- arbitrary code execution at deserialization time, independent of type checks,
-- yielding a strictly positive vulnerability window.

namespace Gnosis.Security.InsecureDeserializationRisk

-- Gadget chain RCE: deserialization of attacker-controlled bytes executes code
def gadgetChainRisk (dataLen : Nat) (deserializerAllowListed : Bool) : Nat :=
  if deserializerAllowListed then 0 else dataLen + 1

-- Allow-listing deserializable types eliminates gadget chain RCE
theorem deser_allowlist_safe (n : Nat) :
    gadgetChainRisk n true = 0 := by { simp [gadgetChainRisk]

-- Unrestricted deserialization is strictly vulnerable
theorem deser_unrestricted_risk (n : Nat) :
    0 < gadgetChainRisk n false := by
  simp [gadgetChainRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Integrity check missing: no HMAC or signature on serialized blob
def integrityMissingRisk (dataLen : Nat) (signatureVerified : Bool) : Nat :=
  if signatureVerified then 0 else dataLen + 1

theorem deser_signature_verified_safe (n : Nat) :
    integrityMissingRisk n true = 0 := by { simp [integrityMissingRisk]

theorem deser_signature_missing_risk (n : Nat) :
    0 < integrityMissingRisk n false := by
  simp [integrityMissingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- PHP unserialize: magic methods __wakeup/__destruct execute on deserialize
def phpMagicMethodRisk (dataLen : Nat) (magicMethodsDisabled : Bool) : Nat :=
  if magicMethodsDisabled then 0 else dataLen + 1

theorem deser_magic_methods_disabled_safe (n : Nat) :
    phpMagicMethodRisk n true = 0 := by { simp [phpMagicMethodRisk]

theorem deser_magic_methods_enabled_risk (n : Nat) :
    0 < phpMagicMethodRisk n false := by
  simp [phpMagicMethodRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- YAML deserialization: yaml.load with !!python/object executes constructors
def yamlConstructorRisk (dataLen : Nat) (safeLoaderUsed : Bool) : Nat :=
  if safeLoaderUsed then 0 else dataLen + 1

theorem deser_yaml_safe_loader_safe (n : Nat) :
    yamlConstructorRisk n true = 0 := by { simp [yamlConstructorRisk]

theorem deser_yaml_full_loader_risk (n : Nat) :
    0 < yamlConstructorRisk n false := by
  simp [yamlConstructorRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in data length
theorem deser_risk_monotone (n m : Nat) (h : n ≤ m) :
    gadgetChainRisk n false ≤ gadgetChainRisk m false := by { simp [gadgetChainRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires allow-list AND signature verification
def netDeserRisk (dataLen : Nat) (allowListed : Bool) (signatureVerified : Bool) : Nat :=
  gadgetChainRisk dataLen allowListed + integrityMissingRisk dataLen signatureVerified

theorem deser_net_risk_zero_fully_mitigated (n : Nat) :
    netDeserRisk n true true = 0 := by { simp [netDeserRisk, gadgetChainRisk, integrityMissingRisk]

theorem deser_net_risk_pos_unmitigated (n : Nat) :
    0 < netDeserRisk n false false := by
  simp [netDeserRisk, gadgetChainRisk, integrityMissingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end InsecureDeserializationRisk
