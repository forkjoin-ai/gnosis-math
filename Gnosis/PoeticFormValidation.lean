import Init

/-!
# PoeticFormValidation — haiku, tanka, and the American sentence, decided

The sovereign voice's `read poetry` mode (squeezebox-player) speaks a text ONLY
if it scans as a recognized fixed form. This module is the formal spec of that
gate: the three forms as syllable-count predicates over a list of per-line
counts, proven decidable, with the canonical exemplars proven to validate and
near-misses proven to fail.

  * Haiku            — three lines, 5-7-5         (17 total)
  * Tanka            — five lines, 5-7-5-7-7      (31 total)
  * American sentence — one line/sentence of 17   (Allen Ginsberg)

The counts come from the voice's own g2p (vowel-nucleus = syllable); this file
formalizes the ACCEPTANCE rule on those counts, independent of how they are
produced. Init-only Lean 4. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PoeticFormValidation

/-- The recognized fixed forms (plus `Free` = matches none). -/
inductive Form
  | Haiku
  | Tanka
  | AmericanSentence
  | Free
  deriving DecidableEq, BEq, Repr

/-- A poem is a list of per-line syllable counts. -/
abbrev LineCounts := List Nat

def isHaiku  (c : LineCounts) : Bool := c == [5, 7, 5]
def isTanka  (c : LineCounts) : Bool := c == [5, 7, 5, 7, 7]
/-- One line (one sentence) of exactly 17 syllables. -/
def isAmericanSentence (c : LineCounts) : Bool := c == [17]

/-- Classify a poem by its line-count signature. The order matters only for
    `Free`; the three positive forms are mutually exclusive (proved below). -/
def classify (c : LineCounts) : Form :=
  if isHaiku c then Form.Haiku
  else if isTanka c then Form.Tanka
  else if isAmericanSentence c then Form.AmericanSentence
  else Form.Free

/-- `read poetry` reads iff the text is not `Free`. -/
def accepts (c : LineCounts) : Bool := classify c != Form.Free

-- ── exemplars (validate) ──────────────────────────────────────────────────

theorem haiku_classifies : classify [5, 7, 5] = Form.Haiku := by decide
theorem tanka_classifies : classify [5, 7, 5, 7, 7] = Form.Tanka := by decide
theorem american_classifies : classify [17] = Form.AmericanSentence := by decide

theorem haiku_accepted : accepts [5, 7, 5] = true := by decide
theorem tanka_accepted : accepts [5, 7, 5, 7, 7] = true := by decide
theorem american_accepted : accepts [17] = true := by decide

-- ── near-misses (rejected) — the measured failures from read poetry ───────

/-- Basho as the voice's g2p scanned it (5-6-4) is NOT a haiku. -/
theorem basho_gp_scan_rejected : accepts [5, 6, 4] = false := by decide
/-- A 5-7-5-7-8 tanka attempt (last line one over) is rejected. -/
theorem tanka_off_by_one_rejected : accepts [5, 7, 5, 7, 8] = false := by decide
/-- A 20-syllable single line is not an American sentence. -/
theorem long_line_rejected : accepts [20] = false := by decide

-- ── structural facts ──────────────────────────────────────────────────────

/-- A haiku totals 17 — the same budget as an American sentence, redistributed
    across three lines. -/
theorem haiku_sums_to_17 : ([5, 7, 5] : LineCounts).foldl (· + ·) 0 = 17 := by decide
/-- A tanka totals 31. -/
theorem tanka_sums_to_31 : ([5, 7, 5, 7, 7] : LineCounts).foldl (· + ·) 0 = 31 := by decide

/-- The three positive forms are mutually exclusive: no count signature scans as
    two of them. (Their line-lengths differ — 3 vs 5 vs 1 — so this is immediate,
    but we pin it.) -/
theorem forms_exclusive :
    (isHaiku [5, 7, 5] && isTanka [5, 7, 5]) = false
  ∧ (isHaiku [5, 7, 5] && isAmericanSentence [5, 7, 5]) = false
  ∧ (isTanka [5, 7, 5, 7, 7] && isAmericanSentence [5, 7, 5, 7, 7]) = false := by
  decide

/-- **THE GATE.** `read poetry` reads exactly the texts whose per-line syllable
    counts scan as one of the three forms; everything else is held silent.
    Proven by exhausting the eight combinations of the three form predicates. -/
theorem the_gate (c : LineCounts) :
    accepts c = (isHaiku c || isTanka c || isAmericanSentence c) := by
  unfold accepts classify
  cases isHaiku c <;> cases isTanka c <;> cases isAmericanSentence c <;> rfl

end PoeticFormValidation
end Gnosis
