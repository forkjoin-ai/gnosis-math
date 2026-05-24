import Init
-- HardcodedCredentialsRisk.lean
-- Anti-thesis: Embedding API keys, passwords, or tokens directly in source code
-- is safe because source repositories are private and access is restricted.
-- Refutation: Repository history, CI logs, error messages, and accidental
-- exposure pathways make hardcoded secrets reachable by adversaries, yielding
-- a strictly positive vulnerability window proportional to secret sensitivity.

namespace Gnosis.Security.HardcodedCredentialsRisk

-- Hardcoded secret: credential embedded as string literal in source
def hardcodedSecretRisk (secretLen : Nat) (secretExternalized : Bool) : Nat :=
  if secretExternalized then 0 else secretLen + 1

-- Externalizing to env vars or secret manager eliminates static exposure
theorem cred_externalized_safe (n : Nat) :
    hardcodedSecretRisk n true = 0 := by { simp [hardcodedSecretRisk]

-- Hardcoded secret in source is strictly vulnerable
theorem cred_hardcoded_risk (n : Nat) :
    0 < hardcodedSecretRisk n false := by
  simp [hardcodedSecretRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Git history exposure: secret removed from HEAD but visible in git log
def gitHistoryRisk (secretLen : Nat) (historyRewritten : Bool) : Nat :=
  if historyRewritten then 0 else secretLen + 1

theorem cred_history_rewritten_safe (n : Nat) :
    gitHistoryRisk n true = 0 := by { simp [gitHistoryRisk]

theorem cred_history_unrewritten_risk (n : Nat) :
    0 < gitHistoryRisk n false := by
  simp [gitHistoryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- CI log exposure: secret printed in CI build output or test output
def ciLogExposureRisk (secretLen : Nat) (logsMasked : Bool) : Nat :=
  if logsMasked then 0 else secretLen + 1

theorem cred_ci_logs_masked_safe (n : Nat) :
    ciLogExposureRisk n true = 0 := by { simp [ciLogExposureRisk]

theorem cred_ci_logs_unmasked_risk (n : Nat) :
    0 < ciLogExposureRisk n false := by
  simp [ciLogExposureRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Default credential: vendor-supplied default unchanged (admin/admin)
def defaultCredentialRisk (isDefault : Bool) (credentialRotated : Bool) : Nat :=
  if !isDefault || credentialRotated then 0 else 1

theorem cred_default_rotated_safe :
    defaultCredentialRisk true true = 0 := by { simp [defaultCredentialRisk]

theorem cred_default_unchanged_risk :
    0 < defaultCredentialRisk true false := by
  simp [defaultCredentialRisk]

-- Secret entropy: low-entropy secret is guessable even if not hardcoded
def secretEntropyRisk (entropy : Nat) (minEntropy : Nat) : Nat :=
  if entropy ≥ minEntropy then 0 else minEntropy - entropy + 1

theorem cred_sufficient_entropy_safe (e m : Nat) (h : e ≥ m) :
    secretEntropyRisk e m = 0 := by
  simp [secretEntropyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem cred_insufficient_entropy_risk (e m : Nat) (h : e < m) :
    0 < secretEntropyRisk e m := by { simp [secretEntropyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in secret length
theorem cred_hardcoded_risk_monotone (n m : Nat) (h : n ≤ m) :
    hardcodedSecretRisk n false ≤ hardcodedSecretRisk m false := by { simp [hardcodedSecretRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires externalization AND git history clean
def netCredentialRisk (secretLen : Nat) (externalized : Bool) (historyRewritten : Bool) : Nat :=
  hardcodedSecretRisk secretLen externalized + gitHistoryRisk secretLen historyRewritten

theorem cred_net_risk_zero_fully_mitigated (n : Nat) :
    netCredentialRisk n true true = 0 := by { simp [netCredentialRisk, hardcodedSecretRisk, gitHistoryRisk]

theorem cred_net_risk_pos_unmitigated (n : Nat) :
    0 < netCredentialRisk n false false := by
  simp [netCredentialRisk, hardcodedSecretRisk, gitHistoryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end HardcodedCredentialsRisk
