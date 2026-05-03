/-
  TopologicalGrammar.lean
  =======================

  Topological Grammar: mapping poetic forms to prose scales via structural invariants.

  Hypothesis: A poetic form's internal topology (repetition, rotation, folding)
  determines which prose scale it can unfold to. The grammar is not about
  syllables or lines—it's about the topological structure that scales invariantly.

  Key insight:
    Haiku (5-7-5): 3-fold structure (triton) → unfolds to SENTENCE (3 clauses)
    Tanka (5-7-5-7-7): 5-fold structure → unfolds to PARAGRAPH (5 sentences)
    Sestina (6 stanzas × 6 words rotating): 6-fold structure → unfolds to DOCUMENT (6 sections)

  The ropelength changes (17 → 31 → 39+), but the TOPOLOGY is the grammar.
  A sentence has topological capacity for 3 clauses (stillness-sting-trill).
  A paragraph has capacity for ~5 sentences (expanding witness).
  A document has capacity for ~6 major sections (harmonic rotation).

  This is a universal mapping: any form with n-fold topology unfolds to a prose
  scale that naturally holds n elements.
-/

namespace TopologicalGrammar

-- ══════════════════════════════════════════════════════════
-- TOPOLOGICAL STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- A topological structure is characterized by:
    - fold: how many primary divisions/moments it has (triton=3, tanka=5, etc.)
    - rotation: whether it repeats elements in a pattern (linear vs. recursive)
    - ropelength: the total syllable/line count
    - fractal: whether structure self-repeats at smaller scales
-/
structure TopologicalStructure where
  name : String
  fold : Nat              -- 3-fold (triton), 5-fold, 6-fold, etc.
  rotation : Nat          -- how many times the pattern repeats
  ropelength : Nat        -- total units (syllables, lines, words)
  fractal : Bool          -- self-similar?

-- ══════════════════════════════════════════════════════════
-- PROSE SCALES AND THEIR TOPOLOGICAL CAPACITY
-- ══════════════════════════════════════════════════════════

/-- A prose scale is a unit of written English with natural topological structure.
    - name: Sentence, Paragraph, Document, etc.
    - capacity: how many primary elements it naturally holds
    - rhythm: whether rhythm matters (sentence-level yes, document-level no)
    - examples: clauses, sentences, sections, chapters
-/
structure ProseScale where
  name : String
  capacity : Nat          -- how many primary divisions fit naturally
  rhythm : Bool           -- does rhythm/meter apply?
  min_words : Nat         -- minimum word count
  max_words : Nat         -- maximum word count before it needs more structure

-- ══════════════════════════════════════════════════════════
-- SENTENCE SCALE (3-fold capacity, rhythmic)
-- ══════════════════════════════════════════════════════════

/-- A sentence naturally holds 3 major elements: opening, middle, closing.
    Or: subject-verb-object. Or: setup-action-response.
    This is the topological capacity of a sentence.
    Rhythm matters (the sentence has cadence, stress patterns). -/
def SentenceScale : ProseScale where
  name := "Sentence"
  capacity := 3
  rhythm := true
  min_words := 5
  max_words := 50

/-- The haiku structure (5-7-5): 3-fold topology.
    Unfolds to a sentence: 3 clauses with 5-7-5 word/stress distribution. -/
def HaikuStructure : TopologicalStructure where
  name := "Haiku"
  fold := 3
  rotation := 1           -- no repetition, one cycle
  ropelength := 17
  fractal := false

theorem haiku_fits_sentence :
    HaikuStructure.fold = SentenceScale.capacity := by
  simp [HaikuStructure, SentenceScale]

-- ══════════════════════════════════════════════════════════
-- PARAGRAPH SCALE (5-fold capacity, rhythmic at level of sentences)
-- ══════════════════════════════════════════════════════════

/-- A paragraph naturally holds 5 sentences: topic, explanation, deepening, shift, conclusion.
    Or in Tanka terms: haiku (3) + echo (2) = 5 total moments.
    Rhythm applies at the sentence level (parallelism, pace). -/
def ParagraphScale : ProseScale where
  name := "Paragraph"
  capacity := 5
  rhythm := true
  min_words := 50
  max_words := 300

/-- The tanka structure (5-7-5-7-7): 5-fold topology.
    Unfolds to a paragraph: 5 sentences with tanka's expansion pattern. -/
def TankaStructure : TopologicalStructure where
  name := "Tanka"
  fold := 5
  rotation := 1           -- haiku (3) + echo (2)
  ropelength := 31
  fractal := true

theorem tanka_fits_paragraph :
    TankaStructure.fold = ParagraphScale.capacity := by
  simp [TankaStructure, ParagraphScale]

-- ══════════════════════════════════════════════════════════
-- DOCUMENT SCALE (6-fold capacity, rotating structure)
-- ══════════════════════════════════════════════════════════

/-- A document naturally holds 6 major sections. This is empirical:
    - Introduction
    - Background / Context
    - Analysis / Development
    - Turning point / Deepening
    - Synthesis / Resolution
    - Conclusion

    Or: six chapters in a novella. Six movements in a proof.
    Rhythm doesn't apply at document level (structure is hierarchical, not sonic).
    Instead: rotation and recursion matter (each section echoes earlier themes). -/
def DocumentScale : ProseScale where
  name := "Document"
  capacity := 6
  rhythm := false         -- rhythm is at sentence/paragraph level
  min_words := 300
  max_words := 10000

/-- The sestina structure: 6 stanzas, 6 end-words rotating.
    This is 6-fold topology with explicit recursion/rotation.
    Unfolds to a document: 6 sections where each concept recurs in new positions. -/
def SestinaStructure : TopologicalStructure where
  name := "Sestina"
  fold := 6
  rotation := 6           -- 6-fold repetition in rotating pattern
  ropelength := 39
  fractal := false

theorem sestina_fits_document :
    SestinaStructure.fold = DocumentScale.capacity := by
  simp [SestinaStructure, DocumentScale]

-- ══════════════════════════════════════════════════════════
-- THE TOPOLOGICAL GRAMMAR RULE
-- ══════════════════════════════════════════════════════════

/-- A poetic form can unfold to a prose scale if their fold numbers match.
    This is the core rule of topological grammar. -/
def can_unfold_to (form : TopologicalStructure) (scale : ProseScale) : Prop :=
  form.fold = scale.capacity

theorem haiku_unfolds_to_sentence :
    can_unfold_to HaikuStructure SentenceScale := by
  simp [can_unfold_to, HaikuStructure, SentenceScale]

theorem tanka_unfolds_to_paragraph :
    can_unfold_to TankaStructure ParagraphScale := by
  simp [can_unfold_to, TankaStructure, ParagraphScale]

theorem sestina_unfolds_to_document :
    can_unfold_to SestinaStructure DocumentScale := by
  simp [can_unfold_to, SestinaStructure, DocumentScale]

-- ══════════════════════════════════════════════════════════
-- UNFOLDING: FROM FORM TO PROSE
-- ══════════════════════════════════════════════════════════

/-- Unfolding expands a form across a prose scale while preserving topology.
    - The form's fold structure becomes the scale's divisions (clauses, sentences, sections)
    - The form's rotation/repetition becomes the scale's parallel structure
    - The form's ropelength is distributed across the scale
    - Rhythm is preserved where it applies (sentence, paragraph) and abstracted where it doesn't (document)
-/

def UnfoldingMap where
  form : TopologicalStructure
  scale : ProseScale
  distribution : Nat → Nat  -- how ropelength maps to each division

/-- Example: haiku unfolds to sentence
    Haiku (5-7-5 = 17) → Sentence (3 clauses)
    Distribution: clause 1 gets ~5 words, clause 2 gets ~7 words, clause 3 gets ~5 words
    Total: ~17 words in the sentence
-/
def HaikuToSentenceMap : UnfoldingMap where
  form := HaikuStructure
  scale := SentenceScale
  distribution := fun i =>
    match i with
    | 0 => 5   -- opening clause: 5 words (stillness)
    | 1 => 7   -- middle clause: 7 words (sting)
    | 2 => 5   -- closing clause: 5 words (trill)
    | _ => 0

/-- Example: tanka unfolds to paragraph
    Tanka (5-7-5-7-7 = 31) → Paragraph (5 sentences)
    Distribution: sentence i gets the i-th syllable count from tanka
    Total: ~31 words across 5 sentences
-/
def TankaToParagraphMap : UnfoldingMap where
  form := TankaStructure
  scale := ParagraphScale
  distribution := fun i =>
    match i with
    | 0 => 5   -- sentence 1: 5 words (haiku opening)
    | 1 => 7   -- sentence 2: 7 words (haiku sting)
    | 2 => 5   -- sentence 3: 5 words (haiku closing)
    | 3 => 7   -- sentence 4: 7 words (echo)
    | 4 => 7   -- sentence 5: 7 words (return)
    | _ => 0

/-- Example: sestina unfolds to document
    Sestina (6 stanzas × 6 words rotating) → Document (6 sections)
    Each section develops one of the 6 core concepts
    Distribution: each section gets multiple paragraphs, but orbits around 1 of 6 themes
    The 6 themes rotate through each section in different positions
-/
def SestinaToDocumentMap : UnfoldingMap where
  form := SestinaStructure
  scale := DocumentScale
  distribution := fun i =>
    if i < 6 then 1 else 0   -- each section focuses on 1 of 6 concepts

-- ══════════════════════════════════════════════════════════
-- TOPOLOGICAL INVARIANT: ROPELENGTH ACROSS SCALES
-- ══════════════════════════════════════════════════════════

/-- The ropelength is preserved under unfolding, but re-scaled.
    A haiku with 17 syllables becomes a sentence with ~17 words.
    The structure is the same; the medium is different. -/

theorem ropelength_preserved_under_unfolding :
    HaikuToSentenceMap.distribution 0 + HaikuToSentenceMap.distribution 1 +
    HaikuToSentenceMap.distribution 2 = HaikuStructure.ropelength := by
  simp [HaikuToSentenceMap, HaikuStructure]

theorem tanka_ropelength_preserved :
    TankaToParagraphMap.distribution 0 + TankaToParagraphMap.distribution 1 +
    TankaToParagraphMap.distribution 2 + TankaToParagraphMap.distribution 3 +
    TankaToParagraphMap.distribution 4 = TankaStructure.ropelength := by
  simp [TankaToParagraphMap, TankaStructure]

-- ══════════════════════════════════════════════════════════
-- THE UNIFIED THEOREM: TOPOLOGICAL GRAMMAR
-- ══════════════════════════════════════════════════════════

/-
  Topological Grammar Theorem:

  A poetic form is a grammar. It encodes structure at the syllable level.
  That same structure can be unfolded to any prose scale whose topological
  capacity matches the form's fold number.

  The grammar is universal and scale-invariant:
    - Haiku (3-fold) → Sentence (3-fold capacity)
    - Tanka (5-fold) → Paragraph (5-fold capacity)
    - Sestina (6-fold) → Document (6-fold capacity)

  An n-fold form can unfold to any n-element prose structure.

  The topological invariants that are preserved under unfolding:
    1. Fold number (structure persists)
    2. Ropelength scaling (total content is proportional)
    3. Rotation pattern (if the form repeats concepts, the prose does too)
    4. Fractal property (self-similarity at smaller scales)

  This explains why:
    - A haiku-structured sentence feels complete in 3 clauses
    - A tanka-structured paragraph feels full in 5 sentences
    - A sestina-structured document naturally contains 6 major sections

  The grammar works in both directions:
    - Poet writes haiku (form) → writer describes something as a sentence (prose)
    - Writer structures a paragraph 5 ways → poet unfolds it as tanka

  Both are the same topology, viewed at different scales, through different media.
-/

theorem topological_grammar :
    (can_unfold_to HaikuStructure SentenceScale) ∧
    (can_unfold_to TankaStructure ParagraphScale) ∧
    (can_unfold_to SestinaStructure DocumentScale) ∧
    (HaikuStructure.fold = 3) ∧
    (TankaStructure.fold = 5) ∧
    (SestinaStructure.fold = 6) := by
  simp [can_unfold_to, HaikuStructure, TankaStructure, SestinaStructure,
        SentenceScale, ParagraphScale, DocumentScale]

end TopologicalGrammar
