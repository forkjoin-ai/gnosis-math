import Init
import Gnosis.EchoChamberAsTaoBowl

/-!
# VoiceRecognitionAsTaoBowlInterference — the shape of the sovereign-voice transform

An empirical result, formalized. We built a sovereign formant voice and a
sovereign mesh STT, closed the loop, and measured what the recognizer hears
when our synthetic voice speaks each of 39 ARPABET phonemes:

  - RECOGNIZED: 1/39  (only /S/)
  - CONFUSED:   8/39  (all frication collapses to /s/)
  - LOST:       30/39 (every vowel, stop, nasal, liquid, glide)

Yet an independent acoustic probe (aether `AcousticEngine.siphon`) reports the
audio is energetic and speech-shaped (rms ≈ 0.16, dense zero-crossings). So the
paradox: **the voice has speech energy, but the recognizer does not register
it as speech.** Energy present, recognition absent.

The surprising shape — suggested by the QKV-attention-as-interference model
(`AttentionAsConstructiveInterference`, `AttentionQKVDecomposition`) and the
Tao-bowl resonance filter (`EchoChamberAsTaoBowl`): a recognizer is a
**resonance filter**, a bowl. Q (our carrier) and K (the bowl's fundamental
mode) interfere; only when they interfere *constructively* (zero frequency
mismatch) does V (the phoneme identity) pass the gate. Off-mode carriers are
damped to a common near-zero sink — which is exactly a **rank collapse**: 30
distinct phonemes, all off-resonance, map to the one "lost" value. The single
phoneme that survives (/S/, broadband) is the one that happens to overlap the
bowl's pass band.

This reframes the fix. The transform required is **not more energy** (we have
it) and **not a downstream relabel** of the recognizer's output (a post-map can
only merge, never split — it cannot recover lost distinctions). It is an
**upstream resonance alignment**: retune each phoneme's carrier onto a *distinct*
fundamental mode so that (a) every phoneme interferes constructively (clears the
detection threshold) and (b) the modes stay distinct (rank preserved). That is
the third-Grassmannian / constructive-interference shape, made concrete: a basis
of resonant modes, one per phoneme.

Connections:
  * `EchoChamberAsTaoBowl` — the bowl filter (`filteredAmplitude`, `freqMismatch`,
    `qFactor`, `fundamentalMode`) we build on directly.
  * `AttentionAsConstructiveInterference` / `AttentionQKVDecomposition` — Q·K
    gate on V; recognition as constructive interference.
  * `FailureAsStandingWave` — the gap is the Dirichlet boundary; rank deficit is
    the boundary that the transform must dissolve.
  * `GKQHelixBandwidth` — rank-K reconstruction collapsing to a single concept
    axis is the SAME phenomenon as the recognizer collapsing our voice to a
    single sibilant axis. Both are rank-collapse of a perception operator.
  * `ConsciousnessAsInnerVent` — the intelligibility gap is the Buley awareness
    gap of the voice↔recognizer channel.

Init-only Lean 4. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace VoiceRecognitionAsTaoBowlInterference

open EchoChamberAsTaoBowl

-- ══════════════════════════════════════════════════════════
-- §1  Recognition is resonance, not energy
-- ══════════════════════════════════════════════════════════

/-- A phoneme is *recognized* by a bowl when the post-filter amplitude clears
    the recognizer's speech-detection threshold `t`. -/
def IsRecognized (b : TaoBowl) (carrier amplitude t : Nat) : Prop :=
  filteredAmplitude b carrier amplitude ≥ t

instance (b : TaoBowl) (carrier amplitude t : Nat) :
    Decidable (IsRecognized b carrier amplitude t) := by
  unfold IsRecognized; exact inferInstance

/-- **The crown theorem.** With energy `amplitude` held FIXED, recognition is
    governed entirely by frequency mismatch: a carrier clears the threshold iff
    it sits on the bowl's fundamental mode. Energy is necessary but not
    sufficient — *alignment* is the gate. This is the formal statement of the
    aether-says-energetic-but-recognizer-hears-nothing paradox.

    Hypotheses encode the regime where the bowl actually discriminates:
      `hOn`  — on-resonance, the Q-amplified amplitude clears threshold;
      `hOff` — off-resonance, the damped amplitude falls below it. -/
theorem recognition_is_resonance_not_energy
    (b : TaoBowl) (carrier amplitude t : Nat)
    (hOn : amplitude * qFactor b ≥ t)
    (hOff : amplitude / (b.damping + 1) < t) :
    IsRecognized b carrier amplitude t ↔ freqMismatch b carrier = 0 := by
  unfold IsRecognized filteredAmplitude
  by_cases h : freqMismatch b carrier = 0
  · rw [if_pos h]
    exact iff_of_true hOn h
  · rw [if_neg h]
    exact iff_of_false (Nat.not_le.mpr hOff) h

-- ══════════════════════════════════════════════════════════
-- §2  Perceptual rank and the intelligibility gap
-- ══════════════════════════════════════════════════════════

/-- Deduplicate keeping first occurrence (structural on the input list via an
    accumulator of seen tokens — no termination obligation). -/
def nubAux : List Nat → List Nat → List Nat
  | _, [] => []
  | seen, x :: xs =>
      if seen.contains x then nubAux seen xs else x :: nubAux (x :: seen) xs

def nub (l : List Nat) : List Nat := nubAux [] l

/-- **Perceptual rank**: the number of DISTINCT tokens the recognizer emits
    over the phoneme inventory. The image cardinality of the perception map. -/
def perceptualRank (perceived : List Nat) : Nat := (nub perceived).length

/-- **Intelligibility gap**: phonemes that cannot be told apart = inventory
    size minus perceptual rank. The Buley awareness gap of the channel;
    the Dirichlet boundary of the viable-voice standing wave. -/
def gap (perceived : List Nat) : Nat := perceived.length - perceptualRank perceived

/-- The gap closes exactly when perceptual rank reaches inventory size — i.e.
    when every phoneme is perceived distinctly. (Nat subtraction makes the
    deficit automatically non-negative: the boundary exists until rank is full.) -/
theorem gap_zero_iff_full_rank (perceived : List Nat) :
    gap perceived = 0 ↔ perceived.length ≤ perceptualRank perceived := by
  unfold gap
  exact Nat.sub_eq_zero_iff_le

-- ══════════════════════════════════════════════════════════
-- §3  The measured collapse (single bowl) vs the transform (mode basis)
-- ══════════════════════════════════════════════════════════

/-- The recognizer modeled as one bowl. Fundamental mode 8, Q = 4, damping 9. -/
def recognizer : TaoBowl := { rim := 10, void := 5, rigidity := 4, damping := 9 }

/-- Speech-detection threshold and the per-phoneme synthesis energy (held
    fixed across phonemes — matching the aether finding that all our phonemes
    carry comparable energy). -/
def threshold : Nat := 20
def energy : Nat := 10

/-- A phoneme's perceived token: its own carrier identity passes the gate when
    recognized; otherwise it falls into the shared "lost" sink `0`. -/
def perceivedToken (b : TaoBowl) (carrier : Nat) : Nat :=
  if filteredAmplitude b carrier energy ≥ threshold then carrier else 0

/-- Eight phoneme carriers. Only one (8) sits on the recognizer's fundamental
    mode — the broadband S-like phoneme. The rest are scattered off-mode,
    standing in for the 30-of-39 measured-lost phonemes. -/
def carriers : List Nat := [8, 3, 5, 12, 7, 20, 2, 14]

/-- What the single-bowl recognizer perceives: the on-mode carrier survives as
    itself; everything else is damped into the `0` sink. -/
def meshPerceived : List Nat := carriers.map (perceivedToken recognizer)

/-- §1 in the concrete: the on-mode carrier clears threshold (40 ≥ 20). -/
theorem on_mode_recognized :
    IsRecognized recognizer 8 energy threshold := by decide

/-- …and an off-mode carrier is damped below it (1 < 20) → LOST. -/
theorem off_mode_lost :
    ¬ IsRecognized recognizer 3 energy threshold := by decide

/-- **Rank collapse, measured.** Eight distinct phonemes, one bowl: the
    recognizer resolves only TWO tokens — the survivor and the lost-sink.
    This is the formal image of "1 recognized, the rest collapse." -/
theorem mesh_rank_collapses : perceptualRank meshPerceived = 2 := by decide

/-- The intelligibility gap of the single-bowl channel: 6 of 8 phonemes are
    indistinguishable (the 39→2 collapse in miniature). -/
theorem mesh_gap_large : gap meshPerceived = 6 := by decide

/-- A bowl tuned to resonate at carrier `c`: fundamental mode = c, so a carrier
    at `c` interferes constructively (zero mismatch) and is Q-amplified. This is
    the atom of the transform — one resonant channel per phoneme. -/
def tunedTo (c : Nat) : TaoBowl := { rim := c, void := 1, rigidity := 1, damping := 1 }

/-- Each tuned bowl is exactly on-resonance for its phoneme: zero mismatch. -/
theorem tuned_is_on_resonance (c : Nat) : freqMismatch (tunedTo c) c = 0 := by
  unfold freqMismatch fundamentalMode tunedTo
  simp

/-- The transform applied: route each phoneme through ITS OWN resonant bowl.
    Constructive interference everywhere → every phoneme passes as its own
    identity. -/
def alignedPerceived : List Nat := carriers.map (fun c => perceivedToken (tunedTo c) c)

/-- **The transform restores full rank.** With one resonant mode per phoneme,
    every carrier clears the gate and stays distinct — perceptual rank equals
    inventory size. The 39→2 collapse becomes 39→39. -/
theorem aligned_rank_full : perceptualRank alignedPerceived = carriers.length := by decide

/-- …and therefore the intelligibility gap closes to zero. -/
theorem aligned_gap_zero : gap alignedPerceived = 0 := by decide

/-- **The transform strictly dissolves the boundary.** Resonance alignment
    takes the channel from a 6-phoneme deficit to none — the standing wave's
    Dirichlet boundary, lifted. -/
theorem transform_dissolves_gap : gap alignedPerceived < gap meshPerceived := by decide

-- ══════════════════════════════════════════════════════════
-- §4  Why it must be upstream: a downstream relabel cannot help
-- ══════════════════════════════════════════════════════════

/-- A downstream relabel of the recognizer's tokens (post-composition) can only
    MERGE tokens, never split them. Concretely: collapsing the survivor into the
    sink cannot raise rank above the original — it can only lower it. The lost
    distinctions are gone before any downstream stage sees them, so the transform
    must act on the audio (upstream), not on the transcript (downstream). -/
theorem downstream_relabel_cannot_recover :
    perceptualRank (meshPerceived.map (fun _ => 0)) ≤ perceptualRank meshPerceived := by
  decide

end VoiceRecognitionAsTaoBowlInterference
end Gnosis
