import Init
-- WeakHashingRisk.lean
-- Anti-thesis: Hashing passwords or sensitive data with MD5 or SHA-1 is safe
-- because the hash is a one-way function and cannot be reversed.
-- Refutation: MD5 and SHA-1 are preimage-fast; rainbow tables and GPU cracking
-- invert common passwords in seconds, yielding a strictly positive
-- exposure window whenever the hash database is compromised.

namespace Gnosis.Security.WeakHashingRisk

-- Weak hash: MD5/SHA-1 without salt is vulnerable to preimage + rainbow tables
def weakHashRisk (passwordLen : Nat) (algorithmStrong : Bool) : Nat :=
  if algorithmStrong then 0 else passwordLen + 1

-- Strong algorithm (bcrypt/argon2/scrypt) eliminates this attack vector
theorem hash_strong_algorithm_safe (n : Nat) :
    weakHashRisk n true = 0 := by { simp [weakHashRisk]

-- Weak algorithm is strictly vulnerable
theorem hash_weak_algorithm_risk (n : Nat) :
    0 < weakHashRisk n false := by
  simp [weakHashRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Missing salt: same password always produces same hash (enables rainbow tables)
def missingSaltRisk (passwordLen : Nat) (saltLen : Nat) : Nat :=
  if saltLen = 0 then passwordLen + 1 else 0

theorem hash_with_salt_safe (n s : Nat) (h : s ≠ 0) :
    missingSaltRisk n s = 0 := by { simp [missingSaltRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem hash_without_salt_risk (n : Nat) :
    0 < missingSaltRisk n 0 := by { simp [missingSaltRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Low iteration count: fast hashing function allows brute-force
def lowIterationRisk (iterations : Nat) (minIterations : Nat) : Nat :=
  if iterations ≥ minIterations then 0 else minIterations - iterations + 1

theorem hash_sufficient_iterations_safe (i m : Nat) (h : i ≥ m) :
    lowIterationRisk i m = 0 := by { simp [lowIterationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem hash_insufficient_iterations_risk (i m : Nat) (h : i < m) :
    0 < lowIterationRisk i m := by { simp [lowIterationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- MD5 collision: two different inputs produce identical MD5 hash
def md5CollisionRisk (usesMd5 : Bool) : Nat :=
  if usesMd5 then 1 else 0

theorem hash_no_md5_safe :
    md5CollisionRisk false = 0 := by { simp [md5CollisionRisk]

theorem hash_uses_md5_collision_risk :
    0 < md5CollisionRisk true := by
  simp [md5CollisionRisk]

-- Timing attack: non-constant-time comparison leaks hash bits
def timingAttackRisk (constTimeCompare : Bool) : Nat :=
  if constTimeCompare then 0 else 1

theorem hash_const_time_compare_safe :
    timingAttackRisk true = 0 := by
  simp [timingAttackRisk]

theorem hash_variable_time_compare_risk :
    0 < timingAttackRisk false := by
  simp [timingAttackRisk]

-- Risk monotone in password length for weak algorithm
theorem hash_weak_risk_monotone (n m : Nat) (h : n ≤ m) :
    weakHashRisk n false ≤ weakHashRisk m false := by
  simp [weakHashRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires strong algorithm AND sufficient salt
def netHashingRisk (passwordLen : Nat) (algorithmStrong : Bool) (saltLen : Nat) : Nat :=
  weakHashRisk passwordLen algorithmStrong + missingSaltRisk passwordLen saltLen

theorem hashing_net_risk_zero_fully_mitigated (n s : Nat) (h : s ≠ 0) :
    netHashingRisk n true s = 0 := by { simp [netHashingRisk, weakHashRisk, missingSaltRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem hashing_net_risk_pos_unmitigated (n : Nat) :
    0 < netHashingRisk n false 0 := by { simp [netHashingRisk, weakHashRisk, missingSaltRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end WeakHashingRisk
