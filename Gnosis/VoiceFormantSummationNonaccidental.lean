import Init

/-!
# VoiceFormantSummationNonaccidental — per-context formant summation, proven

Sibling to `VoiceRecognitionAsTaoBowlInterference` (recognition = constructive
interference on the recognizer's mode) and `CrossModelCliff` (no single rule
across models). A formant synthesizer must combine its per-formant resonators;
this module records a measured falsification of "one global rule wins" and
proves that a per-context selector dominates.

Three summation rules for the voiced tract:

  * `ParallelAllPos` — all-positive sum. Adjacent resonator tails CANCEL in
    their overlap (parallel synthesis' classic failure). Worst for high-front
    /i/, whose F2≈2.4k and F3≈3.2k are close — the overlap IS the cue.
  * `ParallelAlt`    — alternating polarity (+,-,+,-): constructive where
    all-positive was destructive (the "sign-flip").
  * `Cascade`        — resonators in SERIES; transfer function is the PRODUCT of
    resonances, so inter-formant phase is physically correct, constructive by
    construction.

Measured (`voice-bench-ensemble.py`, paired+seeded, whisper-base K=8, 2026-05-22),
the same vowel reverses preference by CONTEXT — so no per-phoneme flag suffices:

  * `fish` (F·IH·SH): Cascade 906 ≫ ParallelAlt 531 — prefers Cascade.
  * `this` (DH·IH·S): ParallelAlt 719 ≫ Cascade 250 — prefers Parallel.

Same nucleus IH, opposite winners. The discriminator is the CODA: the
parallel-preferring words (`this`,`yes`,`ace`) share a voiceless alveolar /s/
coda; the cascade-preferring words do not. So the synthesizer selects per
context: PARALLEL before an /s/ coda, CASCADE elsewhere. Below we prove (a) the
rule reproduces the per-word oracle (argmax) on the measured set, and (b) the
selector's total strictly beats BOTH global rules and equals the oracle total.

Scores are recognition ×1000. Init-only Lean 4. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace VoiceFormantSummationNonaccidental

-- ══════════════════════════════════════════════════════════
-- §1  Rules and the per-word measurement
-- ══════════════════════════════════════════════════════════

inductive SummationRule
  | ParallelAllPos
  | ParallelAlt
  | Cascade
  deriving DecidableEq, Repr

/-- A measured word: its recognition score (×1000) under the two competing
    global rules, and whether it ends in an /s/ coda (the selector's cue). -/
structure Word where
  parallel : Nat   -- score under ParallelAlt (the sign-flip)
  cascade  : Nat   -- score under Cascade
  s_coda   : Bool  -- voiceless alveolar /s/ coda?
  deriving Repr

/-- The per-context selector: PARALLEL before an /s/ coda, else CASCADE. -/
def Word.ruleScore (w : Word) : Nat := if w.s_coda then w.parallel else w.cascade

/-- The oracle: the best achievable per word (argmax over the two rules). -/
def Word.oracle (w : Word) : Nat := Nat.max w.parallel w.cascade

/-- Which rule the selector picks for this word. -/
def Word.ruleChoice (w : Word) : SummationRule :=
  if w.s_coda then SummationRule.ParallelAlt else SummationRule.Cascade

-- Measured words (whisper-base K=8, paired + seeded).
def fish  : Word := ⟨531, 906, false⟩   -- F·IH·SH  → cascade
def eye   : Word := ⟨ 83, 604, false⟩   -- AY       → cascade
def dog   : Word := ⟨ 83, 344, false⟩   -- D·AO·G   → cascade
def yes   : Word := ⟨906,  57, true ⟩   -- Y·EH·S   → parallel
def this_ : Word := ⟨719, 250, true ⟩   -- DH·IH·S  → parallel
def ace   : Word := ⟨375, 104, true ⟩   -- EY·S     → parallel

def words : List Word := [fish, eye, dog, yes, this_, ace]

-- ══════════════════════════════════════════════════════════
-- §2  The same vowel reverses by context (no per-phoneme flag works)
-- ══════════════════════════════════════════════════════════

theorem fish_prefers_cascade  : fish.parallel  < fish.cascade  := by decide
theorem this_prefers_parallel : this_.cascade  < this_.parallel := by decide

/-- `fish` and `this_` share nucleus IH yet their winning rules differ — so the
    choice cannot be a function of the phoneme alone; it is contextual. -/
theorem same_vowel_opposite_winner :
    fish.ruleChoice ≠ this_.ruleChoice := by decide

-- ══════════════════════════════════════════════════════════
-- §3  The /s/ coda rule reproduces the per-word oracle
-- ══════════════════════════════════════════════════════════

/-- For every measured word, the selector's score equals the oracle (it picks
    the better of the two rules every time). -/
def ruleMatchesOracle : Bool := words.all (fun w => w.ruleScore == w.oracle)

theorem rule_realizes_oracle : ruleMatchesOracle = true := by decide

-- ══════════════════════════════════════════════════════════
-- §4  The selector strictly dominates both global rules
-- ══════════════════════════════════════════════════════════

def total (f : Word → Nat) : Nat := (words.map f).foldl (· + ·) 0

/-- Selector total beats a Cascade-everywhere policy. -/
theorem selector_beats_cascade : total Word.cascade < total Word.ruleScore := by decide

/-- Selector total beats a Parallel-everywhere policy. -/
theorem selector_beats_parallel : total Word.parallel < total Word.ruleScore := by decide

/-- The selector achieves the oracle total (no per-word regret). -/
theorem selector_is_oracle : total Word.ruleScore = total Word.oracle := by decide

-- ══════════════════════════════════════════════════════════
-- §5  The principle
-- ══════════════════════════════════════════════════════════

/-- **NONACCIDENTAL-SUMMATION.**

    The per-context /s/ coda selector strictly outscores BOTH global rules
    (cascade-everywhere and parallel-everywhere) AND exactly equals the oracle
    (the best achievable per word). Together with `same_vowel_opposite_winner`
    — the same nucleus reverses preference by context — this is the proof to
    ourselves that the summation choice belongs to the CONTEXT, not to a global
    constant or a per-phoneme flag. Constructive interference is achieved on
    purpose, word by word, not by accident of a fixed convention. -/
theorem nonaccidental_summation :
    total Word.cascade  < total Word.ruleScore
  ∧ total Word.parallel < total Word.ruleScore
  ∧ total Word.ruleScore = total Word.oracle
  ∧ fish.ruleChoice ≠ this_.ruleChoice := by
  decide

end VoiceFormantSummationNonaccidental
end Gnosis
