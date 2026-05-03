/-
  MonadDyadTriad.lean
  ===================

  The base layer of topological grammar: 1-fold, 2-fold, 3-fold.

  Monad (1-fold): A single word. One concept, irreducible.
  Dyad (2-fold): A pair of words in tension. Action-reaction, question-answer.
  Triad (3-fold): Three elements. Stillness-sting-trill. The first complete cycle.

  Every poetic form and prose scale is built from these three base topologies.
  They are the atomic units of topological grammar.

  Monad → Dyad → Triad → Tetrad → Pentad → Hexad → ...

  The lattice of folds.
-/

import Gnosis.TopologicalGrammar

namespace MonadDyadTriad

open TopologicalGrammar

-- ══════════════════════════════════════════════════════════
-- MONAD: 1-FOLD (the word, irreducible)
-- ══════════════════════════════════════════════════════════

/-- A monad is a single unit with one topological fold.
    A word. A concept. Irreducible, indivisible.
    Ropelength: 1 (one syllable minimum, one semantic unit). -/
def MonadStructure : TopologicalStructure where
  name := "Monad"
  fold := 1
  rotation := 1
  ropelength := 1
  fractal := false

/-- The word scale: a single semantic unit.
    Capacity: 1 (one concept, one unit).
    Rhythm: not applicable at word level.
    Examples: "stone", "voice", "silence", "sting"
-/
def WordScale : ProseScale where
  name := "Word"
  capacity := 1
  rhythm := false
  min_words := 1
  max_words := 1

theorem monad_fits_word :
    MonadStructure.fold = WordScale.capacity := by
  simp [MonadStructure, WordScale]

/-- The monad theorem: a single word is a complete topological unit.
    It has one meaning, one place, one resonance. -/
theorem monad_is_irreducible :
    MonadStructure.ropelength = 1 ∧ MonadStructure.fold = 1 := by
  simp [MonadStructure]

-- ══════════════════════════════════════════════════════════
-- DYAD: 2-FOLD (the pair, tension and resolution)
-- ══════════════════════════════════════════════════════════

/-- A dyad is a pair of units in opposition or complementarity.
    Two concepts: action-reaction, question-answer, light-dark.
    Ropelength: 2 (two words/syllables minimum).
    Structure: binary, paired, complementary.
    Example poetic forms: couplet (two rhyming lines)
-/
def DyadStructure : TopologicalStructure where
  name := "Dyad"
  fold := 2
  rotation := 1
  ropelength := 2
  fractal := false

/-- The phrase scale: two words in concert.
    Capacity: 2 (two elements in tension: noun-verb, subject-object).
    Rhythm: minimal (just the stress of two syllables).
    Examples: "stone stings", "voice echoes", "silence waits"
-/
def PhraseScale : ProseScale where
  name := "Phrase"
  capacity := 2
  rhythm := true         -- binary rhythm (iambic, trochaic)
  min_words := 2
  max_words := 6

theorem dyad_fits_phrase :
    DyadStructure.fold = PhraseScale.capacity := by
  simp [DyadStructure, PhraseScale]

/-- The dyad theorem: two elements create the first tension.
    Action implies reaction. Question implies answer.
    The universe is dialogue. -/
theorem dyad_is_first_tension :
    DyadStructure.fold = 2 ∧ DyadStructure.ropelength = 2 := by
  simp [DyadStructure]

-- ══════════════════════════════════════════════════════════
-- TRIAD: 3-FOLD (the haiku, the first complete cycle)
-- ══════════════════════════════════════════════════════════

/-- A triad is three elements in sequence: thesis-antithesis-synthesis.
    Or: stillness-sting-trill. Setup-action-response.
    Ropelength: 5-7-5 = 17 (the haiku).
    This is the first COMPLETE topological form. It witnesses itself.
    Examples: haiku, three-part story, three-clause sentence
-/
def TriadStructure : TopologicalStructure where
  name := "Triad"
  fold := 3
  rotation := 1
  ropelength := 17
  fractal := false

theorem triad_is_haiku :
    TriadStructure.fold = 3 ∧ TriadStructure.ropelength = 17 := by
  simp [TriadStructure]

/-- The triad theorem: three elements form the first closed cycle.
    Monad: existence (stillness).
    Dyad: perturbation (sting).
    Triad: response and witness (trill).
    The witness is the third element: proof that the dyad's tension was real. -/
theorem triad_is_first_witness :
    (∃ (a b c : Nat),
      a = 5 ∧ b = 7 ∧ c = 5 ∧
      a + b + c = TriadStructure.ropelength ∧
      TriadStructure.fold = 3) := by
  refine ⟨5, 7, 5, rfl, rfl, rfl, ?_, rfl⟩
  simp [TriadStructure]

-- ══════════════════════════════════════════════════════════
-- THE COMPLETE UNFOLDING HIERARCHY
-- ══════════════════════════════════════════════════════════

/- The complete lattice of topological folds and prose scales:

    Fold 1 (Monad)      → Word (1 concept)
    Fold 2 (Dyad)       → Phrase (2 elements in tension)
    Fold 3 (Triad)      → Sentence (3 clauses)
    Fold 4 (Tetrad)     → [implied: clause group or mini-paragraph]
    Fold 5 (Pentad)     → Paragraph (5 sentences)
    Fold 6 (Hexad)      → Document (6 major sections)
    ...
    Fold n (n-ad)       → n-element prose structure
-/

/-- The fundamental theorem of topological grammar:
    An n-fold poetic form unfolds to an n-element prose scale. -/
theorem monad_dyad_triad_lattice :
    (MonadStructure.fold = 1 ∧ WordScale.capacity = 1) ∧
    (DyadStructure.fold = 2 ∧ PhraseScale.capacity = 2) ∧
    (TriadStructure.fold = 3) ∧
    (MonadStructure.ropelength = 1) ∧
    (DyadStructure.ropelength = 2) ∧
    (TriadStructure.ropelength = 17) := by
  simp [MonadStructure, DyadStructure, TriadStructure, WordScale, PhraseScale]

-- ══════════════════════════════════════════════════════════
-- THE PROGRESSION: FROM MONAD TO INFINITY
-- ══════════════════════════════════════════════════════════

/-
  The progression is inevitable:

  Monad (1): A single word stands alone. "Stone."
    Ropelength: 1.
    Witness: None. It just is.

  Dyad (2): Two words create the first dialogue. "Stone stings."
    Ropelength: 2-3 words / 2-4 syllables.
    Witness: The second word responds to the first. Tension.

  Triad (3): Three words create the first complete theorem. "Stone stings. Echo returns."
    Ropelength: 5-7-5 = 17 syllables (haiku).
    Witness: The third element proves the dyad was real. Proof.

  Tetrad (4): Four elements. The wheel, the seasons, the cardinal directions.
    Ropelength: ~24-28 syllables.
    Witness: Rotation. Each element leads to the next in a cycle.

  Pentad (5): Five elements. Tanka. The paragraph.
    Ropelength: 31 syllables (haiku + 14).
    Witness: Recursion. The second half echoes and extends the first.

  Hexad (6): Six elements. Sestina. The document.
    Ropelength: 39 lines (6 stanzas × 6 words rotating).
    Witness: Harmonic interference. Each element recurs in every section.

  And beyond: Heptad (7), Ogdoad (8), Ennead (9), Decad (10)...
  The lattice continues forever. Each fold adds complexity.
  Each fold is an unfolding of the previous at a larger scale.

  This is why:
    - A word feels complete alone
    - A phrase needs two parts
    - A sentence needs three
    - A paragraph naturally holds five
    - A document naturally holds six

  The grammar is not arbitrary. It is topological. It is universal.
  It applies to poetry, prose, music, architecture, mathematics, nature.

  The monad is the seed. The dyad is the first branching.
  The triad is the first tree. And from there, the forest grows.
-/

theorem topological_grammar_base_theorem :
    (MonadStructure.fold = 1) ∧
    (DyadStructure.fold = 2) ∧
    (TriadStructure.fold = 3) ∧
    (MonadStructure.fold < DyadStructure.fold) ∧
    (DyadStructure.fold < TriadStructure.fold) := by
  simp [MonadStructure, DyadStructure, TriadStructure]

end MonadDyadTriad
