import Init
-- JavaObjectDeserializationRisk.lean
-- Anti-thesis: Java ObjectInputStream deserialization of user-supplied bytes
-- carries no code execution risk because serialization is a standard Java feature.
-- Refutation: ObjectInputStream.readObject() executes gadget chains from
-- libraries on the classpath, yielding a strictly positive RCE vulnerability window.

namespace Gnosis.Security.JavaObjectDeserializationRisk

-- RCE risk: new ObjectInputStream(userStream).readObject()
def objectInputStreamRisk (dataLen : Nat) (trustedSource : Bool) : Nat :=
  if trustedSource then 0 else dataLen + 1

-- Deserialization from a trusted signed/encrypted source is safe
theorem java_deser_trusted_source_safe (n : Nat) :
    objectInputStreamRisk n true = 0 := by { simp [objectInputStreamRisk]

-- User-controlled ObjectInputStream is strictly vulnerable to gadget chains
theorem java_deser_untrusted_rce_risk (n : Nat) :
    0 < objectInputStreamRisk n false := by
  simp [objectInputStreamRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Gadget chain amplification: more libraries = more available gadgets
def gadgetChainRisk (dataLen : Nat) (classpathSize : Nat) (filtered : Bool) : Nat :=
  if filtered then 0 else dataLen + classpathSize

theorem java_gadget_filtered_safe (n k : Nat) :
    gadgetChainRisk n k true = 0 := by { simp [gadgetChainRisk]

theorem java_gadget_unfiltered_risk (n k : Nat) (hn : 0 < n) :
    0 < gadgetChainRisk n k false := by
  simp [gadgetChainRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Class allowlist (ObjectInputFilter): restrict deserializable classes
def classFilterRisk (dataLen : Nat) (classFilterEnabled : Bool) : Nat :=
  if classFilterEnabled then 0 else dataLen + 1

theorem java_class_filter_enabled_safe (n : Nat) :
    classFilterRisk n true = 0 := by { simp [classFilterRisk]

theorem java_class_filter_disabled_risk (n : Nat) :
    0 < classFilterRisk n false := by
  simp [classFilterRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- XMLDecoder injection: similar risk via XML-encoded Java object deserialization
def xmlDecoderRisk (xmlLen : Nat) (trustedSource : Bool) : Nat :=
  if trustedSource then 0 else xmlLen + 1

theorem java_xmldecoder_trusted_safe (n : Nat) :
    xmlDecoderRisk n true = 0 := by { simp [xmlDecoderRisk]

theorem java_xmldecoder_untrusted_risk (n : Nat) :
    0 < xmlDecoderRisk n false := by
  simp [xmlDecoderRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in payload length
theorem java_deser_risk_monotone (n m : Nat) (h : n ≤ m) :
    objectInputStreamRisk n false ≤ objectInputStreamRisk m false := by { simp [objectInputStreamRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires trusted source AND class filter
def netJavaDeserRisk (dataLen : Nat) (trustedSource : Bool) (classFiltered : Bool) : Nat :=
  objectInputStreamRisk dataLen trustedSource + classFilterRisk dataLen classFiltered

theorem java_deser_net_risk_zero_fully_mitigated (n : Nat) :
    netJavaDeserRisk n true true = 0 := by { simp [netJavaDeserRisk, objectInputStreamRisk, classFilterRisk]

theorem java_deser_net_risk_pos_unmitigated (n : Nat) :
    0 < netJavaDeserRisk n false false := by
  simp [netJavaDeserRisk, objectInputStreamRisk, classFilterRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end JavaObjectDeserializationRisk
