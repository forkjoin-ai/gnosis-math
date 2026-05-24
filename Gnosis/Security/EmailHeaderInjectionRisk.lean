import Init
-- EmailHeaderInjectionRisk.lean
-- Anti-thesis: email header injection is trivially prevented by any framework
-- that sanitizes newline characters from email input fields; modern mail
-- libraries strip \r\n from user-supplied values, making this a solved
-- problem that does not warrant dedicated scanner detection.
-- Refutation: Many applications construct raw SMTP commands or RFC 2822 headers
-- by string concatenation, bypassing library-level sanitization. Injecting \r\n
-- into the To: field adds arbitrary recipients (BCC amplification for spam).
-- Subject: header injection enables phishing via forged subject lines.
-- Reply-To: injection redirects responses to attacker-controlled addresses.
-- MIME injection enables polyglot email/HTML smuggling. The attack is
-- particularly dangerous in password-reset and contact-form flows where
-- user input is directly used in outgoing email construction.

namespace Gnosis.Security.EmailHeaderInjectionRisk

-- CRLF injection: \r\n in email field enables header injection
def crlfEmailInjectionRisk (crlfStrippedFromInput : Bool) (emailBuiltByConcat : Bool) : Bool :=
  !crlfStrippedFromInput && emailBuiltByConcat

theorem crlf_stripped_safe (concat : Bool) :
    crlfEmailInjectionRisk true concat = false := by { simp [crlfEmailInjectionRisk]

theorem not_built_by_concat_safe (stripped : Bool) :
    crlfEmailInjectionRisk stripped false = false := by
  simp [crlfEmailInjectionRisk]

theorem unstripped_concat_risky :
    crlfEmailInjectionRisk false true = true := by
  simp [crlfEmailInjectionRisk]

-- To: header injection: attacker adds additional recipients
def toHeaderInjectionRisk (toFieldSanitized : Bool) (additionalRecipientsAllowed : Bool) : Bool :=
  !toFieldSanitized && additionalRecipientsAllowed

theorem sanitized_to_field_safe (extra : Bool) :
    toHeaderInjectionRisk true extra = false := by
  simp [toHeaderInjectionRisk]

theorem no_additional_recipients_safe (sanitized : Bool) :
    toHeaderInjectionRisk sanitized false = false := by
  simp [toHeaderInjectionRisk]

theorem unsanitized_to_with_extra_risky :
    toHeaderInjectionRisk false true = true := by
  simp [toHeaderInjectionRisk]

-- Subject: header injection: forged subject enables phishing
def subjectHeaderInjectionRisk (subjectSanitized : Bool) (subjectFromUserInput : Bool) : Bool :=
  !subjectSanitized && subjectFromUserInput

theorem subject_sanitized_safe (userInput : Bool) :
    subjectHeaderInjectionRisk true userInput = false := by
  simp [subjectHeaderInjectionRisk]

theorem subject_not_from_user_input_safe (sanitized : Bool) :
    subjectHeaderInjectionRisk sanitized false = false := by
  simp [subjectHeaderInjectionRisk]

theorem unsanitized_user_subject_risky :
    subjectHeaderInjectionRisk false true = true := by
  simp [subjectHeaderInjectionRisk]

-- BCC injection: \r\nBcc: header adds hidden recipients for spam amplification
def bccInjectionRisk (bccHeaderBlocked : Bool) (crlfInInput : Bool) : Bool :=
  !bccHeaderBlocked && crlfInInput

theorem bcc_header_blocked_safe (crlf : Bool) :
    bccInjectionRisk true crlf = false := by
  simp [bccInjectionRisk]

theorem no_crlf_in_input_safe (blocked : Bool) :
    bccInjectionRisk blocked false = false := by
  simp [bccInjectionRisk]

theorem bcc_unblocked_with_crlf_risky :
    bccInjectionRisk false true = true := by
  simp [bccInjectionRisk]

-- Reply-To: injection: redirects email responses to attacker
def replyToInjectionRisk (replyToValidated : Bool) (replyToFromUserInput : Bool)
    (domainAllowlisted : Bool) : Bool :=
  !replyToValidated && replyToFromUserInput && !domainAllowlisted

theorem reply_to_validated_safe (user allowlist : Bool) :
    replyToInjectionRisk true user allowlist = false := by
  simp [replyToInjectionRisk]

theorem reply_to_not_from_user_safe (validated allowlist : Bool) :
    replyToInjectionRisk validated false allowlist = false := by
  simp [replyToInjectionRisk]

theorem domain_allowlisted_safe (validated user : Bool) :
    replyToInjectionRisk validated user true = false := by
  simp [replyToInjectionRisk]

theorem unvalidated_user_replyto_no_allowlist_risky :
    replyToInjectionRisk false true false = true := by
  simp [replyToInjectionRisk]

-- Aggregate email header injection risk
def aggregateEmailHeaderInjectionRisk
    (crlfStripped emailConcat : Bool)
    (toSanitized extraRecipients : Bool)
    (subjectSanitized subjectUserInput : Bool)
    (bccBlocked crlfPresent : Bool) : Nat :=
  (if crlfEmailInjectionRisk crlfStripped emailConcat then 1 else 0) +
  (if toHeaderInjectionRisk toSanitized extraRecipients then 1 else 0) +
  (if subjectHeaderInjectionRisk subjectSanitized subjectUserInput then 1 else 0) +
  (if bccInjectionRisk bccBlocked crlfPresent then 1 else 0)

theorem fully_hardened_zero_email_injection :
    aggregateEmailHeaderInjectionRisk true false true false true false true false = 0 := by
  simp [aggregateEmailHeaderInjectionRisk, crlfEmailInjectionRisk, toHeaderInjectionRisk,
        subjectHeaderInjectionRisk, bccInjectionRisk]

theorem all_email_vectors_max_risk :
    aggregateEmailHeaderInjectionRisk false true false true false true false true = 4 := by
  simp [aggregateEmailHeaderInjectionRisk, crlfEmailInjectionRisk, toHeaderInjectionRisk,
        subjectHeaderInjectionRisk, bccInjectionRisk]

-- Economic: email header injection scanner detection value
def emailInjectionDetectionValueCents (spamAbuseFineCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (spamAbuseFineCents : Int) - (scannerCostCents : Int)

theorem email_injection_detection_profitable (fine scan : Nat) (h : scan < fine) :
    0 < emailInjectionDetectionValueCents fine scan := by
  simp [emailInjectionDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem email_injection_break_even (cost : Nat) :
    0 ≤ emailInjectionDetectionValueCents cost cost := by
  simp [emailInjectionDetectionValueCents]

-- Fleet ROI: email injection scans across email-sending services
def emailInjectionFleetROI (detectionValue : Nat) (emailSendingServices : Nat) : Nat :=
  detectionValue * emailSendingServices

theorem email_injection_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    emailInjectionFleetROI v s1 ≤ emailInjectionFleetROI v s2 := by
  simp [emailInjectionFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_email_injection_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < emailInjectionFleetROI v s := by
  simp [emailInjectionFleetROI]
  exact Nat.mul_pos hv hs

end EmailHeaderInjectionRisk
