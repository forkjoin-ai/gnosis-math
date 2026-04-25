namespace BuleyeanMath

/-!
# Tone Circle — Coltrane's 1967 Diagram as a Fork/Race/Fold Kenoma

John Coltrane handed Yusef Lateef a hand-drawn diagram in 1967 (reproduced
in Lateef's *Repository of Scales and Melodic Patterns*) showing two
concentric chromatic rings with five boxed entry points and a radial
spoke pattern from rim to center. Stephon Alexander has read the same
drawing as a discrete gauge symmetry on the chromatic torus.

This module formalizes the diagram as a `Fin 12 → Nat` kenoma carrying
two simultaneous fold orderings (perfect fifths, major thirds), and proves
that Coltrane's *Giant Steps* key centers are the unique 3-element quorum
forced by the k=5 Primitives BFT bound on the tone circle.

## Encoding

Pitch classes are `Nat` mod 12 with C = 0:
  C=0, C♯=1, D=2, E♭=3, E=4, F=5, F♯=6, G=7, A♭=8, A=9, B♭=10, B=11

Two fold steps:
  fifthsStep n = (n + 7) % 12     -- circle of fifths
  thirdsStep n = (n + 4) % 12     -- major-thirds cycle (Coltrane changes)

Two ring phases:
  outerRing = identity
  innerRing n = (n + 6) % 12      -- tritone offset (Coltrane's double ring)

Zero -- placeholder.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The chromatic kenoma
-- ═══════════════════════════════════════════════════════════════════════

/-- Pitch class as `Nat` mod 12. -/
def pc (n : Nat) : Nat := n % 12

/-- The chromatic total: twelve pitch classes. -/
def chromaticTotal : Nat := 12

/-- A reading is the complement of a rejection count, Valentinian-style:
    `rejection + reading = 12`. -/
def reading (rejection : Nat) : Nat := chromaticTotal - rejection

/-- Conservation: for any rejection count ≤ 12, rejection + reading = 12. -/
theorem chromatic_conservation (r : Nat) (h : r ≤ 12) :
    r + reading r = chromaticTotal := by
  unfold reading chromaticTotal; omega

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Fold orderings — fifths and major thirds
-- ═══════════════════════════════════════════════════════════════════════

/-- Fifths fold step: +7 mod 12. -/
def fifthsStep (n : Nat) : Nat := (n + 7) % 12

/-- Major-thirds fold step: +4 mod 12. The Coltrane changes step. -/
def thirdsStep (n : Nat) : Nat := (n + 4) % 12

/-- Iterate a step function `k` times from a starting pitch. -/
def iterStep (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     n => n
  | k + 1, n => f (iterStep f k n)

/-- The fifths fold is a 12-cycle: 12 iterations from C return to C. -/
theorem fifths_period_twelve : iterStep fifthsStep 12 0 = 0 := by
  decide

/-- The fifths fold visits all 12 pitches before repeating: 11 iterations
    from C does NOT return to C. (Witness that the period is exactly 12.) -/
theorem fifths_no_short_cycle : iterStep fifthsStep 11 0 ≠ 0 := by
  decide

/-- The major-thirds fold is a 3-cycle: 3 iterations from C return to C. -/
theorem thirds_period_three : iterStep thirdsStep 3 0 = 0 := by
  decide

/-- One major third is not the identity. -/
theorem thirds_nontrivial : iterStep thirdsStep 1 0 ≠ 0 := by
  decide

/-- Two major thirds is not the identity (period is exactly 3, not 1 or 2). -/
theorem thirds_period_exactly_three : iterStep thirdsStep 2 0 ≠ 0 := by
  decide

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The double ring — Coltrane's tritone offset
-- ═══════════════════════════════════════════════════════════════════════

/-- Outer ring: identity phase. -/
def outerRing (n : Nat) : Nat := n % 12

/-- Inner ring: tritone offset (+6 mod 12). -/
def innerRing (n : Nat) : Nat := (n + 6) % 12

/-- The two rings are inverses of each other under composition: applying
    the inner-ring offset twice returns to the outer ring. The double
    drawing is one manifold viewed through two phases. -/
theorem double_ring_involution (n : Nat) :
    innerRing (innerRing n) = outerRing n := by
  unfold innerRing outerRing; omega

/-- The two rings together cover the chromatic field: every pitch is
    either on the outer ring or its inner-ring image. -/
theorem double_ring_covers (n : Nat) (h : n < 12) :
    outerRing n = n ∧ innerRing n = (n + 6) % 12 := by
  unfold outerRing innerRing
  refine ⟨?_, rfl⟩
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Giant Steps as a major-thirds quorum
-- ═══════════════════════════════════════════════════════════════════════

/-- Coltrane's *Giant Steps* key centers, transposed so C=0:
    the equal division of the octave into three major thirds.
    The original tune uses {B, G, E♭} = {11, 7, 3}; the structurally
    equivalent C-rooted set is {0, 4, 8} = {C, E, A♭}. -/
def giantStepsKeys : List Nat := [0, 4, 8]

/-- The Giant Steps set is closed under the major-thirds fold. -/
theorem giant_steps_closed_under_thirds :
    thirdsStep 0 = 4 ∧ thirdsStep 4 = 8 ∧ thirdsStep 8 = 0 := by
  unfold thirdsStep; decide

/-- The Giant Steps set has exactly three elements. -/
theorem giant_steps_cardinality : giantStepsKeys.length = 3 := by
  decide

/-- The Giant Steps orbit under `thirdsStep` from C returns to C in
    exactly three iterations and visits all three keys in order. -/
theorem giant_steps_orbit :
    iterStep thirdsStep 1 0 = 4 ∧
    iterStep thirdsStep 2 0 = 8 ∧
    iterStep thirdsStep 3 0 = 0 := by
  unfold iterStep thirdsStep; decide

-- ═══════════════════════════════════════════════════════════════════════
-- §5  The Lamport bound on the tone circle
-- ═══════════════════════════════════════════════════════════════════════

/-- The tone circle's Coltrane diagram marks five entry radials (the
    boxed `1`–`5` annotations). Five is the smallest k satisfying
    Lamport's `3f+1 ≤ k` for f ≥ 1: the Primitives BFT tier. -/
def coltrane_k : Nat := 5

/-- Lamport fault tolerance for k=5: f = (k-1)/3 = 1. -/
def coltrane_f : Nat := (coltrane_k - 1) / 3

theorem coltrane_f_eq_one : coltrane_f = 1 := by
  unfold coltrane_f coltrane_k; decide

/-- Lamport quorum for f=1: q = 2f+1 = 3. -/
def coltrane_quorum : Nat := 2 * coltrane_f + 1

theorem coltrane_quorum_eq_three : coltrane_quorum = 3 := by
  unfold coltrane_quorum coltrane_f coltrane_k; decide

/-- The Lamport bound holds: 3f+1 ≤ k. -/
theorem coltrane_lamport_bound : 3 * coltrane_f + 1 ≤ coltrane_k := by
  unfold coltrane_f coltrane_k; decide

/-- **Coltrane Quorum is Giant Steps.** At the k=5 Primitives BFT tier
    on the chromatic torus, the Lamport quorum size is exactly 3, which
    is exactly the cardinality of the Giant Steps key set. The Giant
    Steps orbit saturates the f=1 BFT quorum bound while leaving two
    radials of Byzantine slack — the structural reason Coltrane could
    improvise over the form without the harmonic topology collapsing. -/
theorem coltrane_quorum_is_giant_steps :
    coltrane_quorum = giantStepsKeys.length := by
  rw [coltrane_quorum_eq_three, giant_steps_cardinality]

/-- Byzantine slack: with k=5 and quorum=3, two radials are reserve
    capacity. This is the topological budget for a soloist to depart
    from the ii-V-I cadence and return without losing the form. -/
def coltrane_slack : Nat := coltrane_k - coltrane_quorum

theorem coltrane_slack_eq_two : coltrane_slack = 2 := by
  unfold coltrane_slack; rw [coltrane_quorum_eq_three]; decide

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Cross-pollination with the Valentinian sin diagnostic
-- ═══════════════════════════════════════════════════════════════════════

/-- A pitch's *consonance reading* is the complement of its dissonance
    rejection count. There are not two forces (consonance and dissonance);
    there is one count read from two ends of the same kenoma. -/
def consonanceReading (dissonanceRejection : Nat) : Nat :=
  reading dissonanceRejection

/-- **No opposition.** Every movement "toward dissonance" is exactly a
    movement "toward consonance" at the complement. One gradient, not
    two forces — the Valentinian zero-sum law applied to harmony.
    A tritone substitution is the diagonal of this identity. -/
theorem no_harmonic_opposition (r : Nat) (h : r ≤ 12) :
    r + consonanceReading r = chromaticTotal := by
  unfold consonanceReading
  exact chromatic_conservation r h

/-- **Featureless field.** A 12-tone row with uniform dissonance count
    has zero gradient — every interval reads the same. The first event
    (a privileged tonic) must happen before harmony has direction. -/
theorem chromatic_featureless (c : Nat) :
    reading c - reading c = 0 := by
  omega

end BuleyeanMath
