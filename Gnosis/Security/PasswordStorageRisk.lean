import Init
-- PasswordStorageRisk.lean
-- Anti-thesis: Storing passwords with bcrypt is the industry standard and fully
-- sufficient; bcrypt handles salting automatically, so additional controls like
-- peppers or work-factor tuning are over-engineering for most applications.
-- Refutation: Insufficient bcrypt work factor (cost < 12) makes offline cracking
-- feasible on modern GPU hardware. Argon2 parameter misconfiguration (low memory,
-- low iterations) degrades the memory-hard guarantee to PBKDF2 equivalence.
-- Absent pepper (server-side secret) means a database dump alone is sufficient
-- for offline attack. Failure to rehash on successful login means users with
-- passwords hashed under old (weaker) parameters never get upgraded hashes.
-- Using MD5/SHA1 without a KDF is a critical failure regardless of whether
-- a salt is present, because GPUs can test billions of hashes per second.

namespace Gnosis.Security.PasswordStorageRisk

-- Insufficient bcrypt cost: work factor below safe minimum
def bcryptCostRisk (costFactor : Nat) (minSafeCostFactor : Nat) : Bool :=
  costFactor < minSafeCostFactor

theorem sufficient_bcrypt_cost_safe (cost minCost : Nat) (h : minCost ≤ cost) :
    bcryptCostRisk cost minCost = false := by { simp [bcryptCostRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem insufficient_bcrypt_cost_risky (cost minCost : Nat) (h : cost < minCost) :
    bcryptCostRisk cost minCost = true := by { simp [bcryptCostRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem bcrypt_at_minimum_safe (n : Nat) :
    bcryptCostRisk n n = false := by { simp [bcryptCostRisk]

theorem bcrypt_cost_10_below_12_risky :
    bcryptCostRisk 10 12 = true := by
  simp [bcryptCostRisk]

-- Argon2 parameters: insufficient memory or iterations degrades hardness
def argon2ParamRisk (memoryKiB : Nat) (iterations : Nat)
    (minMemoryKiB : Nat) (minIterations : Nat) : Bool :=
  memoryKiB < minMemoryKiB || iterations < minIterations

theorem argon2_sufficient_params_safe (mem iter minMem minIter : Nat)
    (hm : minMem ≤ mem) (hi : minIter ≤ iter) :
    argon2ParamRisk mem iter minMem minIter = false := by
  simp [argon2ParamRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem argon2_low_memory_risky (mem iter minMem minIter : Nat)
    (h : mem < minMem) :
    argon2ParamRisk mem iter minMem minIter = true := by { simp [argon2ParamRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem argon2_low_iterations_risky (mem iter minMem minIter : Nat)
    (h : iter < minIter) :
    argon2ParamRisk mem iter minMem minIter = true := by { simp [argon2ParamRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem argon2_at_minimums_safe (mem iter : Nat) :
    argon2ParamRisk mem iter mem iter = false := by { simp [argon2ParamRisk]

-- Pepper missing: no server-side secret means DB dump enables offline attack
def pepperMissingRisk (pepperPresent : Bool) (dbDumpAttackerControlled : Bool) : Bool :=
  !pepperPresent && dbDumpAttackerControlled

theorem pepper_present_safe (dbDump : Bool) :
    pepperMissingRisk true dbDump = false := by
  simp [pepperMissingRisk]

theorem db_not_compromised_safe (pepper : Bool) :
    pepperMissingRisk pepper false = false := by
  simp [pepperMissingRisk]

theorem no_pepper_with_db_dump_risky :
    pepperMissingRisk false true = true := by
  simp [pepperMissingRisk]

-- Rehash on login: stale hashes from weaker algorithms persist indefinitely
def rehashOnLoginRisk (rehashOnSuccessfulLogin : Bool) (legacyHashesExist : Bool) : Bool :=
  !rehashOnSuccessfulLogin && legacyHashesExist

theorem rehash_enabled_safe (legacyExists : Bool) :
    rehashOnLoginRisk true legacyExists = false := by
  simp [rehashOnLoginRisk]

theorem no_legacy_hashes_safe (rehash : Bool) :
    rehashOnLoginRisk rehash false = false := by
  simp [rehashOnLoginRisk]

theorem no_rehash_with_legacy_hashes_risky :
    rehashOnLoginRisk false true = true := by
  simp [rehashOnLoginRisk]

-- Bare hash (MD5/SHA1 without KDF): catastrophic failure regardless of salt
def bareHashRisk (usingKDF : Bool) (hashAlgorithm : Nat)
    (md5Id sha1Id : Nat) : Bool :=
  !usingKDF && (hashAlgorithm = md5Id || hashAlgorithm = sha1Id)

theorem kdf_in_use_safe (algo md5 sha1 : Nat) :
    bareHashRisk true algo md5 sha1 = false := by
  simp [bareHashRisk]

theorem safe_algo_without_kdf_not_bare_hash (algo md5 sha1 : Nat)
    (h1 : algo ≠ md5) (h2 : algo ≠ sha1) :
    bareHashRisk false algo md5 sha1 = false := by
  simp [bareHashRisk, h1, h2]

theorem md5_without_kdf_risky (md5 sha1 : Nat) :
    bareHashRisk false md5 md5 sha1 = true := by
  simp [bareHashRisk]

theorem sha1_without_kdf_risky (md5 sha1 : Nat) :
    bareHashRisk false sha1 md5 sha1 = true := by
  simp [bareHashRisk]

-- Aggregate password storage risk count
def aggregatePasswordStorageRisk
    (costFactor minCostFactor : Nat)
    (memKiB iters minMem minIter : Nat)
    (pepperPresent dbDump : Bool)
    (rehash legacyHashes : Bool)
    (usingKDF : Bool) (hashAlgo md5Id sha1Id : Nat) : Nat :=
  (if bcryptCostRisk costFactor minCostFactor then 1 else 0) +
  (if argon2ParamRisk memKiB iters minMem minIter then 1 else 0) +
  (if pepperMissingRisk pepperPresent dbDump then 1 else 0) +
  (if rehashOnLoginRisk rehash legacyHashes then 1 else 0) +
  (if bareHashRisk usingKDF hashAlgo md5Id sha1Id then 1 else 0)

theorem fully_hardened_zero_password_storage_risk :
    aggregatePasswordStorageRisk
      12 12
      65536 3 65536 3
      true false
      true false
      true 3 1 2 = 0 := by
  simp [aggregatePasswordStorageRisk, bcryptCostRisk, argon2ParamRisk,
        pepperMissingRisk, rehashOnLoginRisk, bareHashRisk]

theorem all_password_storage_vectors_risky :
    aggregatePasswordStorageRisk
      8 12
      1024 1 65536 3
      false true
      false true
      false 1 1 2 = 5 := by
  simp [aggregatePasswordStorageRisk, bcryptCostRisk, argon2ParamRisk,
        pepperMissingRisk, rehashOnLoginRisk, bareHashRisk]

theorem password_storage_risk_bounded
    (costFactor minCostFactor : Nat)
    (memKiB iters minMem minIter : Nat)
    (pepperPresent dbDump : Bool)
    (rehash legacyHashes : Bool)
    (usingKDF : Bool) (hashAlgo md5Id sha1Id : Nat) :
    aggregatePasswordStorageRisk
      costFactor minCostFactor
      memKiB iters minMem minIter
      pepperPresent dbDump
      rehash legacyHashes
      usingKDF hashAlgo md5Id sha1Id ≤ 5 := by
  simp [aggregatePasswordStorageRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Work factor upgrade pays exponential security dividend
theorem higher_cost_factor_safer (cost1 cost2 minCost : Nat)
    (h1 : minCost ≤ cost1) (h12 : cost1 ≤ cost2) :
    bcryptCostRisk cost1 minCost = false ∧ bcryptCostRisk cost2 minCost = false := by
  simp [bcryptCostRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Scanner ROI: detecting weak password storage prevents credential-breach cost
def passwordStorageDetectionValueCents (credBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (credBreachCostCents : Int) - (scannerCostCents : Int)

theorem password_storage_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < passwordStorageDetectionValueCents breach scan := by { simp [passwordStorageDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem password_storage_scanner_break_even (cost : Nat) :
    0 ≤ passwordStorageDetectionValueCents cost cost := by
  simp [passwordStorageDetectionValueCents]

-- Fleet ROI: password storage scan across all auth services
def passwordStorageFleetROI (detectionValueCents : Nat) (authServices : Nat) : Nat :=
  detectionValueCents * authServices

theorem password_storage_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    passwordStorageFleetROI v s1 ≤ passwordStorageFleetROI v s2 := by
  simp [passwordStorageFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_password_storage_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < passwordStorageFleetROI v s := by
  simp [passwordStorageFleetROI]
  exact Nat.mul_pos hv hs

end PasswordStorageRisk
