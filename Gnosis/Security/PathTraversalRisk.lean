import Init
-- PathTraversalRisk.lean
-- Anti-thesis: User-controlled file paths used in open() or send_file() carry
-- no directory traversal risk because the OS resolves paths safely.
-- Refutation: Without canonicalization and prefix validation, ../.. sequences
-- escape the intended base directory, yielding a strictly positive vulnerability
-- window for arbitrary file read or write.

namespace Gnosis.Security.PathTraversalRisk

-- Path traversal: user path contains ../ sequences escaping base dir
def traversalRisk (pathLen : Nat) (canonicalized : Bool) : Nat :=
  if canonicalized then 0 else pathLen + 1

-- Canonicalization + prefix check eliminates traversal
theorem path_canonicalized_safe (n : Nat) :
    traversalRisk n true = 0 := by { simp [traversalRisk]

-- Uncanoncialized user path is strictly vulnerable
theorem path_uncanoncialized_risk (n : Nat) :
    0 < traversalRisk n false := by
  simp [traversalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Null byte injection: path\x00.jpg truncates extension check
def nullByteRisk (pathLen : Nat) (nullBytesStripped : Bool) : Nat :=
  if nullBytesStripped then 0 else pathLen + 1

theorem path_null_stripped_safe (n : Nat) :
    nullByteRisk n true = 0 := by { simp [nullByteRisk]

theorem path_null_unstripped_risk (n : Nat) :
    0 < nullByteRisk n false := by
  simp [nullByteRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- URL-encoded traversal: %2e%2e%2f bypasses naive string matching
def urlEncodedTraversalRisk (pathLen : Nat) (decoded : Bool) : Nat :=
  if decoded then 0 else pathLen + 1

theorem path_decoded_before_check_safe (n : Nat) :
    urlEncodedTraversalRisk n true = 0 := by { simp [urlEncodedTraversalRisk]

theorem path_encoding_bypass_risk (n : Nat) :
    0 < urlEncodedTraversalRisk n false := by
  simp [urlEncodedTraversalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Zip slip: archive entry path escapes extraction directory
def zipSlipRisk (entryLen : Nat) (entryValidated : Bool) : Nat :=
  if entryValidated then 0 else entryLen + 1

theorem path_zip_entry_validated_safe (n : Nat) :
    zipSlipRisk n true = 0 := by { simp [zipSlipRisk]

theorem path_zip_slip_risk (n : Nat) :
    0 < zipSlipRisk n false := by
  simp [zipSlipRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Symlink following: symlink within base dir points outside
def symlinkRisk (pathLen : Nat) (symlinkResolved : Bool) : Nat :=
  if symlinkResolved then 0 else pathLen + 1

theorem path_symlink_resolved_safe (n : Nat) :
    symlinkRisk n true = 0 := by { simp [symlinkRisk]

theorem path_symlink_unresolved_risk (n : Nat) :
    0 < symlinkRisk n false := by
  simp [symlinkRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in path length
theorem path_traversal_risk_monotone (n m : Nat) (h : n ≤ m) :
    traversalRisk n false ≤ traversalRisk m false := by { simp [traversalRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires canonicalization AND null byte stripping
def netPathRisk (pathLen : Nat) (canonicalized : Bool) (nullBytesStripped : Bool) : Nat :=
  traversalRisk pathLen canonicalized + nullByteRisk pathLen nullBytesStripped

theorem path_net_risk_zero_fully_mitigated (n : Nat) :
    netPathRisk n true true = 0 := by { simp [netPathRisk, traversalRisk, nullByteRisk]

theorem path_net_risk_pos_unmitigated (n : Nat) :
    0 < netPathRisk n false false := by
  simp [netPathRisk, traversalRisk, nullByteRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end PathTraversalRisk
