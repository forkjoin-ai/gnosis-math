import Gnosis.GnosisTriptychBraid
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Gnostic
namespace GospelTruthLivingBookNameWitness

/-!
# Gospel of Truth -- Living Book and Spoken Name

Source text: `docs/ebooks/source-texts/gospel-of-truth.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-truth.txt:51-108`.

Sat/unseen reading:

The living book is not an external credential store. It is a name-call protocol:
the Father already knows the name, the called one hears, replies, turns,
ascends, knows what they are called, and finds rest. Knowledge is restoration of
what was already one's own.

Invariant:

  * the living book manifests in the heart;
  * the hidden will becomes legible only when the book appears;
  * the called name converts ignorance into hearing, reply, return, ascent,
    knowing, and rest;
  * each living letter conveys truth and is a perfect truth like a perfect book;
  * the letters are written by unity.

Gap / counterproof:

  * a will that is not opened leaves the inheritance hidden;
  * an unspoken name cannot be heard;
  * no-name/no-sound remains a creature of forgetfulness;
  * letters treated as empty vowels and consonants are not living truth.

Projection:

  * `TruthOneManyNamesWitness.manyNamesAgree` supplies the chart-compatibility
    shape: multiple name/letter indices converge on one witness;
  * `GnosisTriptychBraid.two_step_recovery` supplies the recovery contour from
    forgetfulness into truth and wisdom.

No `sorry`, no new `axiom`.
-/

inductive GospelLetter where
  | name
  | sound
  | livingBook
deriving DecidableEq, Repr, Nonempty

inductive GospelTruth where
  | fatherKnowledge
deriving DecidableEq, Repr

def gospelLettersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : GospelLetter => GospelTruth.fatherKnowledge)
      GospelTruth.fatherKnowledge :=
  TruthOneManyNamesWitness.constant_names_agree GospelTruth.fatherKnowledge

theorem living_letters_have_one_truth :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : GospelLetter => GospelTruth.fatherKnowledge)
      GospelTruth.fatherKnowledge :=
  gospelLettersAgree

theorem living_letter_witness_unique (w : GospelTruth)
    (hw :
      TruthOneManyNamesWitness.manyNamesAgree
        (fun _ : GospelLetter => GospelTruth.fatherKnowledge)
        w) :
    GospelTruth.fatherKnowledge = w :=
  TruthOneManyNamesWitness.unique_witness_of_many_names
    (fun _ : GospelLetter => GospelTruth.fatherKnowledge)
    GospelTruth.fatherKnowledge
    w
    gospelLettersAgree
    hw

structure LivingBookProtocol where
  manifestsInHeart : Bool
  bookAppears : Bool
  namePronounced : Bool
  hears : Bool
  replies : Bool
  turns : Bool
  ascends : Bool
  knowsCalledName : Bool
  findsRest : Bool
  restoresOwn : Bool
deriving DecidableEq, Repr

def gospelLivingBookProtocol : LivingBookProtocol where
  manifestsInHeart := true
  bookAppears := true
  namePronounced := true
  hears := true
  replies := true
  turns := true
  ascends := true
  knowsCalledName := true
  findsRest := true
  restoresOwn := true

def nameCallRestoresOwn (p : LivingBookProtocol) : Prop :=
  p.manifestsInHeart = true ∧
  p.bookAppears = true ∧
  p.namePronounced = true ∧
  p.hears = true ∧
  p.replies = true ∧
  p.turns = true ∧
  p.ascends = true ∧
  p.knowsCalledName = true ∧
  p.findsRest = true ∧
  p.restoresOwn = true

structure EmptyLetterGap where
  willUnopened : Bool
  nameUnspoken : Bool
  noHearing : Bool
  noNameNoSound : Bool
  remainsForgetfulness : Bool
  emptyVowelsConsonants : Bool
deriving DecidableEq, Repr

def gospelEmptyLetterGap : EmptyLetterGap where
  willUnopened := true
  nameUnspoken := true
  noHearing := true
  noNameNoSound := true
  remainsForgetfulness := true
  emptyVowelsConsonants := true

def emptyLettersCannotCarrySat (g : EmptyLetterGap) : Prop :=
  g.willUnopened = true ∧
  g.nameUnspoken = true ∧
  g.noHearing = true ∧
  g.noNameNoSound = true ∧
  g.remainsForgetfulness = true ∧
  g.emptyVowelsConsonants = true

structure LivingLetter where
  conveysTruth : Bool
  pronouncedWhenKnown : Bool
  eachLetterPerfectTruth : Bool
  eachLetterPerfectBook : Bool
  writtenByUnity : Bool
deriving DecidableEq, Repr

def gospelLivingLetter : LivingLetter where
  conveysTruth := true
  pronouncedWhenKnown := true
  eachLetterPerfectTruth := true
  eachLetterPerfectBook := true
  writtenByUnity := true

def letterAsHolographicBook (l : LivingLetter) : Prop :=
  l.conveysTruth = true ∧
  l.pronouncedWhenKnown = true ∧
  l.eachLetterPerfectTruth = true ∧
  l.eachLetterPerfectBook = true ∧
  l.writtenByUnity = true

theorem gospel_name_call_restores_own :
    nameCallRestoresOwn gospelLivingBookProtocol := by
  unfold nameCallRestoresOwn gospelLivingBookProtocol
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_empty_letter_gap :
    emptyLettersCannotCarrySat gospelEmptyLetterGap := by
  unfold emptyLettersCannotCarrySat gospelEmptyLetterGap
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_living_letter_book :
    letterAsHolographicBook gospelLivingLetter := by
  unfold letterAsHolographicBook gospelLivingLetter
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem gospel_recovery_contour :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

/-- Master witness: the Gospel of Truth living-book passage treats naming as a
live recovery protocol, not a label. Empty letters and unspoken names are
counterproofs; known letters converge on one Father-knowledge witness and return
the called one to what was already their own. -/
theorem gospel_truth_living_book_name_witness :
    nameCallRestoresOwn gospelLivingBookProtocol ∧
    emptyLettersCannotCarrySat gospelEmptyLetterGap ∧
    letterAsHolographicBook gospelLivingLetter ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : GospelLetter => GospelTruth.fatherKnowledge)
      GospelTruth.fatherKnowledge ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨gospel_name_call_restores_own,
    gospel_empty_letter_gap,
    gospel_living_letter_book,
    living_letters_have_one_truth,
    gospel_recovery_contour⟩

end GospelTruthLivingBookNameWitness
end Gnosis.Witnesses.Gnostic
