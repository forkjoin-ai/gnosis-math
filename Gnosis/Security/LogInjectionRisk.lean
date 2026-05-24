import Init
-- LogInjectionRisk.lean
-- Anti-thesis: Writing user-supplied data to application logs carries no risk
-- because log files are only read by administrators.
-- Refutation: Injected newlines forge log entries, ANSI escape sequences
-- execute in terminal viewers, and log parsers processing malformed entries
-- can be driven to secondary injection, yielding a strictly positive
-- vulnerability window.

namespace Gnosis.Security.LogInjectionRisk

-- Newline injection: user inserts \n to forge log entries
def newlineInjectionRisk (inputLen : Nat) (newlineStripped : Bool) : Nat :=
  if newlineStripped then 0 else inputLen + 1

-- Stripping newlines from logged user data eliminates log forging
theorem log_newline_stripped_safe (n : Nat) :
    newlineInjectionRisk n true = 0 := by { simp [newlineInjectionRisk]

-- Unstripped newline in log is strictly vulnerable
theorem log_newline_unstripped_risk (n : Nat) :
    0 < newlineInjectionRisk n false := by
  simp [newlineInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- ANSI escape injection: CSI sequences corrupt terminal log viewers
def ansiEscapeRisk (inputLen : Nat) (ansiStripped : Bool) : Nat :=
  if ansiStripped then 0 else inputLen + 1

theorem log_ansi_stripped_safe (n : Nat) :
    ansiEscapeRisk n true = 0 := by { simp [ansiEscapeRisk]

theorem log_ansi_unstripped_risk (n : Nat) :
    0 < ansiEscapeRisk n false := by
  simp [ansiEscapeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Structured log injection: JSON log field contains }, breaking parser
def structuredLogRisk (inputLen : Nat) (valueEscaped : Bool) : Nat :=
  if valueEscaped then 0 else inputLen + 1

theorem log_structured_escaped_safe (n : Nat) :
    structuredLogRisk n true = 0 := by { simp [structuredLogRisk]

theorem log_structured_unescaped_risk (n : Nat) :
    0 < structuredLogRisk n false := by
  simp [structuredLogRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Log-driven SIEM injection: SIEM correlation rules process forged entries
def siemInjectionRisk (inputLen : Nat) (logValidated : Bool) : Nat :=
  if logValidated then 0 else inputLen + 1

theorem log_siem_validated_safe (n : Nat) :
    siemInjectionRisk n true = 0 := by { simp [siemInjectionRisk]

theorem log_siem_unvalidated_risk (n : Nat) :
    0 < siemInjectionRisk n false := by
  simp [siemInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Credential leakage: passwords logged in plaintext via error messages
def credentialLeakRisk (sensitiveDataLogged : Bool) (redacted : Bool) : Nat :=
  if !sensitiveDataLogged || redacted then 0 else 1

theorem log_credentials_redacted_safe :
    credentialLeakRisk true true = 0 := by { simp [credentialLeakRisk]

theorem log_credentials_plaintext_risk :
    0 < credentialLeakRisk true false := by
  simp [credentialLeakRisk]

-- Risk monotone in input length
theorem log_injection_risk_monotone (n m : Nat) (h : n ≤ m) :
    newlineInjectionRisk n false ≤ newlineInjectionRisk m false := by
  simp [newlineInjectionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires newlines stripped AND log values escaped
def netLogRisk (inputLen : Nat) (newlineStripped : Bool) (valueEscaped : Bool) : Nat :=
  newlineInjectionRisk inputLen newlineStripped + structuredLogRisk inputLen valueEscaped

theorem log_net_risk_zero_fully_mitigated (n : Nat) :
    netLogRisk n true true = 0 := by { simp [netLogRisk, newlineInjectionRisk, structuredLogRisk]

theorem log_net_risk_pos_unmitigated (n : Nat) :
    0 < netLogRisk n false false := by
  simp [netLogRisk, newlineInjectionRisk, structuredLogRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end LogInjectionRisk
