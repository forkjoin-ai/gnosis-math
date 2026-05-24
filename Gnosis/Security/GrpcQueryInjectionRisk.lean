import Init
-- GrpcQueryInjectionRisk.lean
-- Anti-thesis: gRPC protobuf message fields containing user input cannot
-- introduce injection vulnerabilities because protobuf is strongly typed.
-- Refutation: string proto fields passed to backend systems (SQL, shell, eval)
-- without sanitization yield a strictly positive vulnerability window.

namespace GrpcQueryInjection

-- Proto string field injection: string field value passed to SQL backend
def protoStringFieldRisk (fieldLen : Nat) (backendSanitized : Bool) : Nat :=
  if backendSanitized then 0 else fieldLen + 1

-- Backend sanitization (parameterized SQL) eliminates injection
theorem grpc_backend_sanitized_safe (n : Nat) :
    protoStringFieldRisk n true = 0 := by { simp [protoStringFieldRisk]

-- Unsanitized proto string field at backend is strictly vulnerable
theorem grpc_backend_unsanitized_risk (n : Nat) :
    0 < protoStringFieldRisk n false := by
  simp [protoStringFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Metadata injection: gRPC metadata (header) value injection
def grpcMetadataRisk (metaLen : Nat) (validated : Bool) : Nat :=
  if validated then 0 else metaLen + 1

theorem grpc_metadata_validated_safe (n : Nat) :
    grpcMetadataRisk n true = 0 := by { simp [grpcMetadataRisk]

theorem grpc_metadata_unvalidated_risk (n : Nat) :
    0 < grpcMetadataRisk n false := by
  simp [grpcMetadataRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- oneof field injection: user-controlled oneof variant selection
def oneofVariantRisk (variantLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else variantLen + 1

theorem grpc_oneof_allowlisted_safe (n : Nat) :
    oneofVariantRisk n true = 0 := by { simp [oneofVariantRisk]

theorem grpc_oneof_unvalidated_risk (n : Nat) :
    0 < oneofVariantRisk n false := by
  simp [oneofVariantRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Streaming injection: server-streaming with user-controlled filter in request
def streamFilterRisk (filterLen : Nat) (parameterized : Bool) : Nat :=
  if parameterized then 0 else filterLen + 1

theorem grpc_stream_filter_parameterized_safe (n : Nat) :
    streamFilterRisk n true = 0 := by { simp [streamFilterRisk]

theorem grpc_stream_filter_unparameterized_risk (n : Nat) :
    0 < streamFilterRisk n false := by
  simp [streamFilterRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Service name injection: dynamic service discovery with user-controlled names
def serviceNameRisk (nameLen : Nat) (allowListed : Bool) : Nat :=
  if allowListed then 0 else nameLen + 1

theorem grpc_service_name_allowlisted_safe (n : Nat) :
    serviceNameRisk n true = 0 := by { simp [serviceNameRisk]

theorem grpc_service_name_unvalidated_risk (n : Nat) :
    0 < serviceNameRisk n false := by
  simp [serviceNameRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in field length
theorem grpc_field_risk_monotone (n m : Nat) (h : n ≤ m) :
    protoStringFieldRisk n false ≤ protoStringFieldRisk m false := by { simp [protoStringFieldRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires backend sanitization AND validated metadata
def netGrpcRisk (inputLen : Nat) (backendSanitized : Bool) (metaValidated : Bool) : Nat :=
  protoStringFieldRisk inputLen backendSanitized + grpcMetadataRisk inputLen metaValidated

theorem grpc_net_risk_zero_fully_mitigated (n : Nat) :
    netGrpcRisk n true true = 0 := by { simp [netGrpcRisk, protoStringFieldRisk, grpcMetadataRisk]

theorem grpc_net_risk_pos_unmitigated (n : Nat) :
    0 < netGrpcRisk n false false := by
  simp [netGrpcRisk, protoStringFieldRisk, grpcMetadataRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end GrpcQueryInjection
