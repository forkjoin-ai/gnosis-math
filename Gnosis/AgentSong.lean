/-
  AgentSong.lean
  ==============

  Living things make music while they live. Init-only, zero sorry.

  Every organism in the ecosystem is a 55-dimensional knot (KnotEcosystem.lean);
  its identity collapses to one number (the knot hash). That number seeds a walk on
  the tone circle (MarkovSong.lean) — the creature's idle hum. Because the walk is
  deterministic, a creature sings the SAME phrase whenever it is the same creature,
  and two creatures with the same tonic hum alike.

  The Kingdom only sets the VOICE — its register (mirrors aeon-poetry's
  `register_for`): plants and fungi drone low, animals sing in the middle, the very
  small chirp high. The brains formalized elsewhere (BirdBrain k=7, FishBrain k=3,
  …) say how rich the sensorium is; here we only need that each carries a tonic and
  hums.
-/

import Gnosis.MarkovSong

namespace AgentSong

/-- A creature's tonic: which Giant Steps station its knot lands on. -/
def tonicOf (knot : Nat) : Nat :=
  match knot % 3 with
  | 0 => 0
  | 1 => 4
  | _ => 8

/-- The idle hum: a three-step walk from the creature's tonic (returns home). -/
def idleHum (knot : Nat) : List Nat := MarkovSong.walk 3 (tonicOf knot)

/-- Every idle hum is four notes long — the closed triadic cycle, whatever the
    creature. (Music has a definite shape grown from identity alone.) -/
theorem idle_hum_has_four_notes (knot : Nat) : (idleHum knot).length = 4 := by
  simp [idleHum, MarkovSong.walk]

/-- Creatures that share a tonic hum the same phrase. -/
theorem same_tonic_same_hum (a b : Nat) (h : tonicOf a = tonicOf b) :
    idleHum a = idleHum b := by
  simp [idleHum, h]

/-- A creature with a tonic of C hums C E A♭ C. -/
theorem a_creature_on_C_hums_giant_steps :
    idleHum 0 = [0, 4, 8, 0] := by decide

/-- A whistled phrase has one note per swerve, plus the opening tonic. So a tick
    of `k` of the creature's state-bits is a phrase of `k + 1` notes. -/
theorem creature_phrase_length (knot : Nat) (bits : List Bool) :
    (MarkovSong.whistle (tonicOf knot) bits).length = bits.length + 1 := by
  simpa using MarkovSong.whistle_length (tonicOf knot) bits

/-- The Kingdom voice register (0 Animalia … 5 Bacteria), matching aeon-poetry. -/
def registerOf : Nat → Nat
  | 1 => 2
  | 2 => 2
  | 0 => 4
  | 3 => 5
  | 4 => 5
  | _ => 6

/-- A fungus drones below a bacterium's chirp. -/
theorem fungus_drones_below_bacterium : registerOf 2 < registerOf 5 := by decide

/-- An animal sings between the rooted kingdoms and the very small. -/
theorem animal_is_the_middle_voice :
    registerOf 2 < registerOf 0 ∧ registerOf 0 < registerOf 5 := by decide

end AgentSong
