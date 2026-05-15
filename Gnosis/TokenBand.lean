/-!
# Token Band Soundness

A token band is a runtime lead block: instead of sampling from the whole
finite vocabulary, the sampler is only allowed to choose from a finite,
nonempty subset. This file formalizes the discrete boundary used by the
Moonshine/Foil `candidateTokens` hot path.

The theorem here is intentionally narrow. It does not claim that a band makes a
model more correct. It certifies the part the runtime can honestly enforce:

* if the band is nonempty, there is always an admissible token to select;
* if the band is proper, the admissible choice width strictly decreases;
* the discrete "void entropy" proxy `vocabSize - bandSize` is positive exactly
  for a proper band.
-/

namespace Gnosis
namespace TokenBand

/-- A finite positive token band inside a finite positive vocabulary. -/
structure TokenBand where
  vocabSize : Nat
  bandSize : Nat
  vocabPositive : 0 < vocabSize
  bandPositive : 0 < bandSize
  bandWithinVocab : bandSize ≤ vocabSize

/-- Discrete width removed by constraining the sampler to the band. -/
def voidEntropyDrop (band : TokenBand) : Nat :=
  band.vocabSize - band.bandSize

/-- A nonempty band always contains at least one candidate position. -/
theorem admissible_candidate_exists (band : TokenBand) :
    ∃ candidate : Nat, candidate < band.bandSize := by
  exact ⟨0, band.bandPositive⟩

/-- Every band candidate is addressable inside the full vocabulary. -/
theorem candidate_is_vocab_addressable
    (band : TokenBand) (candidate : Nat) (hCandidate : candidate < band.bandSize) :
    candidate < band.vocabSize := by
  exact Nat.lt_of_lt_of_le hCandidate band.bandWithinVocab

/-- A proper band strictly reduces the admissible choice width. -/
theorem proper_band_strictly_reduces_width
    (band : TokenBand) (hProper : band.bandSize < band.vocabSize) :
    band.bandSize < band.vocabSize := by
  exact hProper

/-- A proper band has positive discrete void-entropy drop. -/
theorem proper_band_positive_void_entropy_drop
    (band : TokenBand) (hProper : band.bandSize < band.vocabSize) :
    0 < voidEntropyDrop band := by
  unfold voidEntropyDrop
  exact Nat.sub_pos_of_lt hProper

/--
If a runtime reports no entropy drop, the band was not a proper narrowing.
This is the certificate boundary for avoiding fake speed/quality claims:
zero-width reduction means no semantic lead block was actually applied.
-/
theorem zero_drop_implies_full_width
    (band : TokenBand) (hDrop : voidEntropyDrop band = 0) :
    band.vocabSize = band.bandSize := by
  unfold voidEntropyDrop at hDrop
  exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hDrop) band.bandWithinVocab

/--
Concrete certificate shape for the current Gemma lead block: any single-token
band of size `k` inside a 256k vocabulary is sound when `0 < k ≤ 256000`.
-/
theorem gemma_vocab_band_sound
    (k : Nat) (hPos : 0 < k) (hWithin : k ≤ 256000) :
    ∃ band : TokenBand, band.vocabSize = 256000 ∧ band.bandSize = k := by
  exact
    ⟨{ vocabSize := 256000
       bandSize := k
       vocabPositive := by decide
       bandPositive := hPos
       bandWithinVocab := hWithin },
      rfl,
      rfl⟩

/-!
## Argmax Agreement

The runtime fast path computes scores only for candidate rows. That is
extensionally equivalent to full-vocabulary argmax when the full argmax token
is inside the candidate predicate.
-/

/-- `token` is a full-vocabulary argmax for a discrete score function. -/
def IsVocabArgmax (vocabSize : Nat) (score : Nat → Int) (token : Nat) : Prop :=
  token < vocabSize ∧ ∀ other : Nat, other < vocabSize → score other ≤ score token

/-- `token` is a candidate-band argmax for a discrete score function. -/
def IsBandArgmax
    (vocabSize : Nat) (contains : Nat → Prop) (score : Nat → Int) (token : Nat) : Prop :=
  token < vocabSize ∧ contains token ∧
    ∀ other : Nat, other < vocabSize → contains other → score other ≤ score token

/--
If the full-vocabulary argmax is inside the band, candidate-row argmax agrees
with the full projection on that token. This is the formal boundary for the
Gemma/Native row-skip: it is a speed shortcut, not a different selection rule,
whenever the winning token lies in the band.
-/
theorem token_band_argmax_agrees_when_global_winner_in_band
    (vocabSize : Nat) (contains : Nat → Prop) (score : Nat → Int) (token : Nat)
    (hArgmax : IsVocabArgmax vocabSize score token)
    (hContains : contains token) :
    IsBandArgmax vocabSize contains score token := by
  refine ⟨hArgmax.left, hContains, ?_⟩
  intro other hOther _hContainsOther
  exact hArgmax.right other hOther

/--
If a token is band-argmax and also dominates every out-of-band vocabulary
token, then it is a full-vocabulary argmax. This is the converse certificate
the runtime can use for validation probes.
-/
theorem band_argmax_lifts_to_vocab_argmax
    (vocabSize : Nat) (contains : Nat → Prop) (score : Nat → Int) (token : Nat)
    (hBand : IsBandArgmax vocabSize contains score token)
    (hOutOfBand :
      ∀ other : Nat, other < vocabSize → ¬ contains other → score other ≤ score token) :
    IsVocabArgmax vocabSize score token := by
  refine ⟨hBand.left, ?_⟩
  intro other hOther
  by_cases hContainsOther : contains other
  · exact hBand.right.right other hOther hContainsOther
  · exact hOutOfBand other hOther hContainsOther

end TokenBand
end Gnosis
