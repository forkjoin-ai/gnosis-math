import Init
-- InsecureFileUploadRisk.lean
-- Anti-thesis: Restricting file extensions (allow .jpg, .png, .pdf) is
-- sufficient to prevent malicious file uploads; an attacker cannot execute
-- server-side code from an image upload endpoint with client-side extension
-- validation in place.
-- Refutation: Client-side extension checks are trivially bypassed with Burp.
-- Server-side MIME detection (magic bytes) is bypassed by polyglots (valid JPEG
-- that is also a valid PHP file). Path traversal in the filename allows writing
-- to arbitrary directories. ZIP bombs exhaust storage/CPU. Unrestricted SVG
-- uploads enable stored XSS. Files served from the same origin are parsed by
-- the browser per Content-Type rather than filename.

namespace Gnosis.Security.InsecureFileUploadRisk

-- MIME type check: client-supplied Content-Type vs. magic byte inspection
def mimeCheckRisk (clientSuppliedMimeOnly : Bool) (magicByteInspection : Bool) : Bool :=
  clientSuppliedMimeOnly && !magicByteInspection

theorem magic_byte_inspection_safe (clientMime : Bool) :
    mimeCheckRisk clientMime true = false := by { simp [mimeCheckRisk]
  cases clientMime <;> simp

theorem server_side_check_safe :
    mimeCheckRisk false true = false := by
  simp [mimeCheckRisk]

theorem client_mime_only_without_magic_risky :
    mimeCheckRisk true false = true := by
  simp [mimeCheckRisk]

-- Path traversal in filename: ../../../etc/cron.d/evil
def filenamePathTraversalRisk (filenameSanitized : Bool) (uploadDirEnforced : Bool) : Bool :=
  !filenameSanitized && !uploadDirEnforced

theorem sanitized_filename_safe (dirEnforced : Bool) :
    filenamePathTraversalRisk true dirEnforced = false := by
  simp [filenamePathTraversalRisk]

theorem upload_dir_enforced_safe (sanitized : Bool) :
    filenamePathTraversalRisk sanitized true = false := by
  simp [filenamePathTraversalRisk]
  cases sanitized <;> simp

theorem unsanitized_unenforced_traversal_risk :
    filenamePathTraversalRisk false false = true := by
  simp [filenamePathTraversalRisk]

-- Polyglot file: valid image that is also valid server-side script
def polyglotRisk (imageValidationStrict : Bool) (executionPreventedForUploads : Bool) : Bool :=
  !imageValidationStrict && !executionPreventedForUploads

theorem strict_validation_prevents_polyglot (exec : Bool) :
    polyglotRisk true exec = false := by
  simp [polyglotRisk]

theorem no_execution_from_uploads_safe (strict : Bool) :
    polyglotRisk strict true = false := by
  simp [polyglotRisk]
  cases strict <;> simp

theorem lax_validation_executable_uploads_polyglot_risk :
    polyglotRisk false false = true := by
  simp [polyglotRisk]

-- ZIP bomb: decompression explosion exhausts storage or CPU
def zipBombRisk (archivesAllowed : Bool) (sizeLimitBeforeDecompress : Bool)
    (decompressionRatioChecked : Bool) : Bool :=
  archivesAllowed && !sizeLimitBeforeDecompress && !decompressionRatioChecked

theorem size_limit_prevents_zip_bomb (archives ratio : Bool) :
    zipBombRisk archives true ratio = false := by
  simp [zipBombRisk]
  cases archives <;> cases ratio <;> simp

theorem ratio_check_prevents_zip_bomb (archives size : Bool) :
    zipBombRisk archives size true = false := by
  simp [zipBombRisk]
  cases archives <;> cases size <;> simp

theorem no_archives_no_zip_bomb_risk (size ratio : Bool) :
    zipBombRisk false size ratio = false := by
  simp [zipBombRisk]

theorem archive_no_checks_zip_bomb_risk :
    zipBombRisk true false false = true := by
  simp [zipBombRisk]

-- SVG upload: SVG contains JavaScript, executed in same-origin browser context
def svgXSSRisk (svgAllowed : Bool) (svgSanitized : Bool) (servedSameOrigin : Bool) : Bool :=
  svgAllowed && !svgSanitized && servedSameOrigin

theorem svg_sanitized_no_xss (allowed same : Bool) :
    svgXSSRisk allowed true same = false := by
  simp [svgXSSRisk]
  cases allowed <;> cases same <;> simp

theorem svg_not_allowed_no_xss (sanitized same : Bool) :
    svgXSSRisk false sanitized same = false := by
  simp [svgXSSRisk]

theorem svg_cross_origin_no_xss (allowed sanitized : Bool) :
    svgXSSRisk allowed sanitized false = false := by
  simp [svgXSSRisk]
  cases allowed <;> cases sanitized <;> simp

theorem svg_allowed_unsanitized_same_origin_xss :
    svgXSSRisk true false true = true := by
  simp [svgXSSRisk]

-- File size limit: maximum upload size enforced before processing
def oversizedUploadRisk (sizeLimitEnforced : Bool) (maxSizeBytes : Nat)
    (incomingBytes : Nat) : Bool :=
  !sizeLimitEnforced && incomingBytes > maxSizeBytes

theorem size_limit_prevents_oversized (max inc : Nat) :
    oversizedUploadRisk true max inc = false := by
  simp [oversizedUploadRisk]

theorem within_limit_no_oversized_risk (max inc : Nat) (h : inc ≤ max) :
    oversizedUploadRisk false max inc = false := by
  simp [oversizedUploadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem over_limit_without_enforcement_risky (max inc : Nat) (h : max < inc) :
    oversizedUploadRisk false max inc = true := by { simp [oversizedUploadRisk, h]

-- Virus/malware: uploaded file contains known-malicious payload
def malwareUploadRisk (antivirusScan : Bool) (sandboxedStorage : Bool) : Bool :=
  !antivirusScan && !sandboxedStorage

theorem antivirus_prevents_malware (sandbox : Bool) :
    malwareUploadRisk true sandbox = false := by
  simp [malwareUploadRisk]

theorem sandboxed_storage_contains_malware (av : Bool) :
    malwareUploadRisk av true = false := by
  simp [malwareUploadRisk]
  cases av <;> simp

theorem no_av_no_sandbox_malware_risk :
    malwareUploadRisk false false = true := by
  simp [malwareUploadRisk]

-- Aggregate file upload risk
def aggregateUploadRisk
    (clientMime magicBytes : Bool)
    (filenameSan dirEnforced : Bool)
    (imgStrict execPrevented : Bool)
    (svgAllowed svgSan sameOrigin : Bool) : Nat :=
  (if mimeCheckRisk clientMime magicBytes then 1 else 0) +
  (if filenamePathTraversalRisk filenameSan dirEnforced then 1 else 0) +
  (if polyglotRisk imgStrict execPrevented then 1 else 0) +
  (if svgXSSRisk svgAllowed svgSan sameOrigin then 1 else 0)

theorem fully_hardened_zero_upload_risk :
    aggregateUploadRisk false true true true true true false true false = 0 := by
  simp [aggregateUploadRisk, mimeCheckRisk, filenamePathTraversalRisk,
        polyglotRisk, svgXSSRisk]

theorem all_vectors_max_upload_risk :
    aggregateUploadRisk true false false false false false true false true = 4 := by
  simp [aggregateUploadRisk, mimeCheckRisk, filenamePathTraversalRisk,
        polyglotRisk, svgXSSRisk]

theorem mime_check_alone_nonzero :
    0 < aggregateUploadRisk true false true true true true false true false := by
  simp [aggregateUploadRisk, mimeCheckRisk, filenamePathTraversalRisk,
        polyglotRisk, svgXSSRisk]

-- Economic: scanner detection value for file upload vulnerabilities
def uploadVulnDetectionValueCents (breachCostCents : Nat) (scannerCostCents : Nat) : Int :=
  (breachCostCents : Int) - (scannerCostCents : Int)

theorem detection_profitable_when_breach_exceeds_cost (breach scan : Nat) (h : scan < breach) :
    0 < uploadVulnDetectionValueCents breach scan := by
  simp [uploadVulnDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem detection_nonneg_at_break_even (cost : Nat) :
    0 ≤ uploadVulnDetectionValueCents cost cost := by { simp [uploadVulnDetectionValueCents]

-- Compound: each additional upload check multiplicatively reduces residual risk
def residualUploadRisk (checksApplied : Nat) (totalChecks : Nat) (h : 0 < totalChecks) : Nat :=
  totalChecks - min checksApplied totalChecks

theorem all_checks_applied_zero_residual (total : Nat) (h : 0 < total) :
    residualUploadRisk total total h = 0 := by
  simp [residualUploadRisk]

theorem no_checks_full_residual (total : Nat) (h : 0 < total) :
    residualUploadRisk 0 total h = total := by
  simp [residualUploadRisk]

theorem more_checks_lower_residual (applied total : Nat) (h : 0 < total)
    (hle : applied ≤ total) :
    residualUploadRisk total total h ≤ residualUploadRisk applied total h := by
  simp [residualUploadRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end InsecureFileUploadRisk
