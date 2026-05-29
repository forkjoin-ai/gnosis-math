/-
  ResolutionLadder.lean
  =====================

  Up-resolution and down-resolution: the swerve as a zoom. Init-only, zero sorry.

  The clinamen swerve `n ↦ n+1` (ClinamenInfrathin.lean) is, read as a RESOLUTION
  operator, "up-res": add one unit of detail. Its inverse `declinamen` is "down-res".
  One ladder, three readings:

    * MUSIC  — chord extension: triad → 7th → 9th → 11th → 13th. Each up-res stacks
               one more third (one more voice). Down-res back to the triad.
    * POETRY — the lattice level (PoetryLattice.lean): up-res grows the form,
               ropelength 17·(n+1), parts 3·(n+1); strictly monotone in resolution.
    * WORDS  — the cummings splice: fold "a leaf falls" inside "l(a…)oneliness".
               Up-res inserts a stream INTO a host; the matter inside the frame
               grows by exactly the inserted length (charge is added, never faked).

  So a song can be rendered at any resolution and refined or coarsened in place —
  the mechanism behind "distributed music": ship the low-res seed, up-res per node.
-/

namespace ResolutionLadder

/-- Up-resolution: the swerve, +1 unit of detail. -/
def upres (n : Nat) : Nat := n + 1

/-- Down-resolution: the declinamen, −1 (saturating at the void). -/
def downres (n : Nat) : Nat := n - 1

/-- Down-res inverts up-res everywhere: refine then coarsen returns the level. -/
theorem downres_upres (n : Nat) : downres (upres n) = n := by
  simp [downres, upres]

/-- Up-res strictly raises the level (a swerve always adds). -/
theorem upres_strictly_increases (n : Nat) : n < upres n := by
  simp [upres]

-- ── music: the chord-extension ladder ────────────────────────────────────────

/-- Voices in the tertian chord at resolution `lvl`: triad(3) → 7th(4) → … . -/
def chordVoices (lvl : Nat) : Nat := 3 + lvl

/-- Up-res adds exactly one voice — one more stacked third. -/
theorem upres_adds_one_voice (lvl : Nat) :
    chordVoices (upres lvl) = chordVoices lvl + 1 := by
  simp only [chordVoices, upres]; omega

/-- The named rungs: triad, seventh, ninth, eleventh, thirteenth. -/
theorem extension_ladder :
    (chordVoices 0, chordVoices 1, chordVoices 2, chordVoices 3, chordVoices 4)
      = (3, 4, 5, 6, 7) := by decide

-- ── poetry: the lattice as resolution ────────────────────────────────────────

def ropelength (lvl : Nat) : Nat := 17 * (lvl + 1)
def parts (lvl : Nat) : Nat := 3 * (lvl + 1)

/-- Up-res grows the poem's ropelength strictly — more rope, more form. -/
theorem upres_grows_ropelength (lvl : Nat) :
    ropelength lvl < ropelength (upres lvl) := by
  simp only [ropelength, upres]
  omega

/-- Resolution 0 is the triton/haiku anchor: ropelength 17, three parts. -/
theorem anchor_is_seventeen :
    ropelength 0 = 17 ∧ parts 0 = 3 := by decide

-- ── words: the cummings splice (up-res of a word) ────────────────────────────

/-- Splice `ins` into `host` at position `pos` — fold one stream inside another. -/
def splice (host ins : List α) (pos : Nat) : List α :=
  host.take pos ++ ins ++ host.drop pos

/-- Up-resolving a word adds exactly the spliced length: charge is added, the
    host preserved around it. ("l(a…)oneliness" carries all of "loneliness" plus
    all of "a leaf falls".) -/
theorem splice_adds_length (host ins : List α) (pos : Nat) :
    (splice host ins pos).length = host.length + ins.length := by
  simp only [splice, List.length_append, List.length_take, List.length_drop]
  omega

/-- cummings' "l(a": "loneliness" (10) with "aleaffalls" (10) folded inside →
    twenty units of matter inside the one frame. -/
theorem la_splice_doubles :
    (splice (List.replicate 10 (0 : Nat)) (List.replicate 10 1) 1).length = 20 := by
  decide

end ResolutionLadder
