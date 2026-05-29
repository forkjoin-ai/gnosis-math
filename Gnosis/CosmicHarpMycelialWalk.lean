import Init

/-!
# The Cosmic Harp — a Mycelial Physarum Walk over the Pitch Topology

The song used to walk the SAME walk every time: the fixed Coltrane +4 (mod 12)
march. The cosmic harp replaces that march with a slime-mould forager that grows
tubes across the twelve pitch classes, reinforcing the flux it travels and pruning
what it does not. This module is the substrate witness for that forager
(`wasm-modules/aeon-poetry/src/mycelial.rs`).

Three formalized atoms braid here:

1. **Taylor's Sequence** (`Gnosis/TaylorsSequence.lean`, the Phyle Tripod numbers)
   reduced mod 12 → the harp's interval palette. Coltrane's major third (4)
   survives but no longer rules.
2. **Physarum flux routing** (`Gnosis/PhysarumFluxRouting.lean::updateTube`) → the
   pheromone field is memristive tube memory: active flux thickens a tube, idleness
   prunes it.
3. **The Golden Duality** (`Gnosis/ImplementationWisdom.lean`: WEYL == FIBONACCI_HASH)
   → the step selector is the additive 2^32/φ Weyl sequence, the optimal
   low-discrepancy generator, so the walk is deterministic and reproducible yet
   varied — no RNG, no clock.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis.CosmicHarpMycelialWalk

/-- Total list indexing with a 0 default (avoids `List.get!`, absent from `Init`). -/
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nth xs n

-- Section 1: the interval palette is Taylor's Sequence mod 12

/-- Taylor's Sequence, first 14 terms (the Phyle Tripod numbers). -/
def taylorRaw : List Nat := [6, 7, 8, 11, 14, 15, 18, 21, 22, 29, 47, 76, 123, 199]

/-- The harp's interval palette: the distinct residues of Taylor's Sequence mod 12,
in first-seen order. -/
def palette : List Nat := [6, 7, 8, 11, 2, 3, 9, 10, 5, 4]

/-- Every palette interval is the mod-12 residue of some Taylor term. -/
theorem palette_drawn_from_taylor :
    palette.all (fun s => taylorRaw.any (fun t => t % 12 == s)) = true := by native_decide

/-- Conversely, every Taylor term's residue is in the palette (nothing dropped). -/
theorem palette_covers_taylor :
    (taylorRaw.map (· % 12)).all (fun s => palette.contains s) = true := by native_decide

/-- Coltrane's major third survives in the palette (from 76 % 12 = 4) — present,
not king. -/
theorem coltrane_third_survives : palette.contains 4 = true := by native_decide

/-- The tritone (199 % 12 = 7? no — 6, from 6/18) is in the palette: the standing
wave aeon's interval. -/
theorem tritone_in_palette : palette.contains 6 = true := by native_decide

/-- Every palette step is a real interval: 1 ≤ s ≤ 11 (never a unison/octave). -/
theorem palette_real_intervals :
    palette.all (fun s => 1 ≤ s && s ≤ 11) = true := by native_decide

theorem palette_length : palette.length = 10 := by native_decide

-- Section 2: memristive pheromone (mirrors PhysarumFluxRouting.updateTube)

structure Tube where
  thickness : Nat
  flow : Nat
deriving Repr, DecidableEq

/-- Active flux thickens the tube; an idle tube prunes by one. -/
def updateTube (t : Tube) : Tube :=
  if t.flow = 0 then { t with thickness := t.thickness - 1 }
  else { t with thickness := t.thickness + t.flow }

/-- A travelled tube (flow = FLOW = 3) thickens. -/
theorem flux_thickens_tube :
    (updateTube { thickness := 3, flow := 3 }).thickness = 6 := by native_decide

/-- An untravelled tube prunes toward zero. -/
theorem idle_tube_prunes :
    (updateTube { thickness := 3, flow := 0 }).thickness = 2 := by native_decide

/-- The update is memristive: the same starting tube ends differently depending on
whether flux flowed — the network REMEMBERS where the harp walked. -/
theorem pheromone_is_memristive :
    (updateTube { thickness := 3, flow := 3 }).thickness ≠
      (updateTube { thickness := 3, flow := 0 }).thickness := by native_decide

-- Section 3: the Golden-Weyl step selector (low-discrepancy, RNG-free)

/-- 2^32 / φ, Knuth's golden multiplier — the optimal low-discrepancy additive step
(it is also the optimal hash multiplier: the Golden Duality). -/
def gold : Nat := 2654435769

theorem gold_is_knuth_golden : gold = 0x9E3779B9 := by native_decide

def twoPow32 : Nat := 4294967296

/-- The additive Weyl state after k steps from a seed, kept in 32 bits. -/
def weylState (seed k : Nat) : Nat := (seed + gold * k) % twoPow32

/-- The palette index chosen at step k: the high 8 bits of the Weyl state (the
well-distributed bits of an additive sequence), folded into the palette. -/
def pick (seed k : Nat) : Nat := (weylState seed k / 16777216) % palette.length

/-- The Taylor interval the harp steps by at step k. -/
def step (seed k : Nat) : Nat := nth palette (pick seed k)

/-- `nth palette i` lands on a genuine palette element for every valid index — so
whatever the selector picks, the harp steps by a real Taylor interval. -/
theorem all_palette_indices_valid :
    (List.range palette.length).all (fun i => palette.contains (nth palette i)) = true := by
  native_decide

/-- A concrete chosen step is a palette interval (the selector wired end to end). -/
theorem sample_step_in_palette : palette.contains (step 0 1) = true := by native_decide

-- Section 4: the harp breaks the Coltrane march

def centers : List Nat := [0, 4, 8] -- Stillness / Sting / Trill (the seed's entry)

/-- The ascend-contour walk: from the seed's entry, each step adds a Taylor interval
chosen by the Golden-Weyl selector. -/
def ascendWalk (seed : Nat) : Nat → Nat
  | 0 => nth centers (seed % 3)
  | k + 1 => (ascendWalk seed k + step seed (k + 1)) % 12

/-- The old fixed walk: a constant +4 (mod 12) march from the same entry. -/
def coltraneMarch (seed k : Nat) : Nat := (nth centers (seed % 3) + 4 * k) % 12

def takeWalk (f : Nat → Nat) (n : Nat) : List Nat := (List.range n).map f

/-- The cosmic harp does NOT reproduce the fixed Coltrane march: over the first
eight notes (seed 0) the two walks differ. The variation is real. -/
theorem harp_breaks_coltrane_march :
    takeWalk (ascendWalk 0) 8 ≠ takeWalk (coltraneMarch 0) 8 := by native_decide

/-- And the harp's walk is itself non-constant — it moves off the entry. -/
theorem harp_walk_moves : ascendWalk 0 1 ≠ ascendWalk 0 0 := by native_decide

end Gnosis.CosmicHarpMycelialWalk
