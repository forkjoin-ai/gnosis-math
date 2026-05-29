/-
  MarkovSong.lean
  ===============

  A song is a walk. Init-only, zero sorry.

  Every living thing in the world (the aeon-solarium bodies, the animals of the
  bioecology, the mechanized brains) carries a tonic — its seed — and idles by
  walking the tone circle from it. That walk IS its song: at each step the clinamen
  swerve chooses a third (a bit: major +4 or minor +3 — the trit lifted to pitch),
  and the agent whistles the pitch it lands on. No randomness is needed; the agent's
  own state-bits drive the Markov choice deterministically, so the same creature in
  the same mood sings the same phrase, and the mesh can replay it from the seed.

  Two kernels:
    * the closed Coltrane kernel (+4 mod 12), whose orbit is the period-3 Giant
      Steps cycle — the simplest hum, returning home every three notes;
    * the seeded kernel (+3 or +4 by a bit), a genuine two-branch Markov walk —
      the creature's song, its melody chosen note by note by its own swerves.
-/

namespace MarkovSong

abbrev PC := Nat

-- ── the closed kernel: the idle hum ──────────────────────────────────────────

/-- The Coltrane Markov kernel: ascend a major third (deterministic successor). -/
def step (p : PC) : PC := (p + 4) % 12

/-- Walk `n` notes from a tonic. -/
def walk : Nat → PC → List PC
  | 0, p => [p]
  | (n + 1), p => p :: walk n (step p)

/-- The kernel never leaves the chromatic ring. -/
theorem step_in_ring (p : PC) : step p < 12 := by
  simp only [step]; exact Nat.mod_lt _ (by decide)

/-- The idle hum from C closes after three notes: C E A♭ C — period 3. -/
theorem hum_returns_home : walk 3 0 = [0, 4, 8, 0] := by decide

/-- The orbit is exactly the three Giant Steps stations, whatever the tonic. -/
theorem hum_visits_three_stations :
    walk 3 0 = [0, 4, 8, 0] ∧ walk 3 4 = [4, 8, 0, 4] ∧ walk 3 8 = [8, 0, 4, 8] := by
  decide

-- ── the seeded kernel: the creature's own melody ─────────────────────────────

/-- A swerve at a note: `true` takes the minor third (+3), `false` the major (+4).
    The bit comes from the agent's own state — its mood, its knot, its tick. -/
def stepBit (p : PC) (b : Bool) : PC := if b then (p + 3) % 12 else (p + 4) % 12

/-- A walk driven by a stream of the creature's swerve-bits → its melody. -/
def whistle : PC → List Bool → List PC
  | p, [] => [p]
  | p, b :: bs => p :: whistle (stepBit p b) bs

/-- Every note of a whistled melody lands in the chromatic ring. -/
theorem stepBit_in_ring (p : PC) (b : Bool) : stepBit p b < 12 := by
  cases b <;> (simp only [stepBit]; exact Nat.mod_lt _ (by decide))

/-- A creature whose swerves read major, major, minor, major from tonic C sings a
    specific, replayable phrase — the same every time from the same seed-bits. -/
theorem a_creatures_song :
    whistle 0 [false, false, true, false] = [0, 4, 8, 11, 3] := by decide

/-- The empty swerve-stream is a single sustained tonic — the held note of rest. -/
theorem rest_is_one_note (p : PC) : whistle p [] = [p] := by rfl

/-- Length law: a creature with `k` swerves sings `k + 1` notes (it always
    sounds its tonic first). So a whole tick of `k` bits is a phrase of `k+1`. -/
theorem whistle_length (p : PC) (bs : List Bool) :
    (whistle p bs).length = bs.length + 1 := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih => simp [whistle, ih, Nat.add_comm, Nat.add_left_comm]

end MarkovSong
