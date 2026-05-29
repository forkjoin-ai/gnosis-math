/-
  EuclideanRhythm.lean
  ====================

  Rhythm as the even sharing of k onsets across n steps — the temporal twin of
  ScalesModes.lean (which shares pitches across the octave). Init-only, zero sorry.

  Place an onset at step i exactly when `(i·k) mod n < k`. This is the closed-form
  Euclidean rhythm: it spreads k beats as evenly as the integers allow, so the
  famous world rhythms fall straight out — E(3,8) is the Cuban tresillo, E(5,8) the
  cinquillo. "Maximally even" means every gap between consecutive onsets differs
  from every other by at most one step; we witness this on the named rhythms.

  Like a scale's mode-necklace, a rhythm is read cyclically — rotating the onset
  pattern is the same cyclic action that inverts chords and spins words.
-/

namespace EuclideanRhythm

/-- Onset at step i of the rhythm E(k,n): the closed-form Euclidean test. -/
def isOnset (k n i : Nat) : Bool := (i * k) % n < k

/-- The rhythm E(k,n) as a list of n booleans (true = a beat). -/
def pattern (k n : Nat) : List Bool :=
  (List.range n).map (fun i => isOnset k n i)

/-- The onset step-indices of E(k,n). -/
def onsets (k n : Nat) : List Nat :=
  (List.range n).filter (fun i => isOnset k n i)

/-- Number of beats actually placed. -/
def beats (k n : Nat) : Nat :=
  (pattern k n).foldl (fun a b => if b then a + 1 else a) 0

/-- E(3,8) is the tresillo: beats on 0, 3, 6 — x..x..x. -/
theorem tresillo :
    pattern 3 8 = [true, false, false, true, false, false, true, false] := by decide

/-- E(5,8) is the cinquillo: x.x.xx.x (a clave of five, beats on 0 2 4 5 7). -/
theorem cinquillo :
    pattern 5 8 = [true, false, true, false, true, true, false, true] := by decide

/-- E(2,5) — the additive five (a sub-Saharan / Balkan cell). -/
theorem two_in_five : onsets 2 5 = [0, 3] := by decide

/-- Each Euclidean rhythm places exactly k beats. -/
theorem beat_counts :
    beats 3 8 = 3 ∧ beats 5 8 = 5 ∧ beats 4 16 = 4 ∧ beats 7 16 = 7 := by decide

-- ── maximal evenness: the cyclic gaps between onsets ─────────────────────────

def gapsFrom (first n : Nat) : List Nat → Nat → List Nat
  | [], prev => [n - prev + first]
  | x :: xs, prev => (x - prev) :: gapsFrom first n xs x

/-- Cyclic gaps between consecutive onsets (the last wraps to the first). -/
def cyclicGaps (os : List Nat) (n : Nat) : List Nat :=
  match os with
  | [] => []
  | a :: rest => gapsFrom a n rest a

/-- The tresillo's gaps are 3, 3, 2 — maximally even: every gap is 2 or 3. -/
theorem tresillo_maximally_even : cyclicGaps (onsets 3 8) 8 = [3, 3, 2] := by decide

/-- The cinquillo's gaps are 2, 2, 1, 2, 1 — again only two adjacent values. -/
theorem cinquillo_maximally_even : cyclicGaps (onsets 5 8) 8 = [2, 2, 1, 2, 1] := by decide

/-- All gaps of a Euclidean rhythm sum to the bar length (they tile the cycle). -/
theorem tresillo_gaps_tile_the_bar :
    (cyclicGaps (onsets 3 8) 8).foldl (· + ·) 0 = 8 := by decide

-- ── a rhythm is a necklace: read it from any rotation ────────────────────────

def rotate1 : List Bool → List Bool
  | [] => []
  | a :: r => r ++ [a]

/-- Rotating the tresillo once gives a son-clave-style displacement — same beats,
    new downbeat (the cyclic action of WordInversion / ScalesModes on a rhythm). -/
theorem rotated_tresillo :
    rotate1 (pattern 3 8) = [false, false, true, false, false, true, false, true] := by decide

end EuclideanRhythm
