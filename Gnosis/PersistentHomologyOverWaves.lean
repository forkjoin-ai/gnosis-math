/-
  PersistentHomologyOverWaves.lean
  ================================

  PERSISTENT HOMOLOGY OVER THE WAVE FILTRATION.

  Persistent homology tracks topological features (Betti holes) across
  a filtration parameter. Here, the filtration parameter is the WAVE
  NUMBER of the falsification ledger. A hole that appears in wave 4
  and persists through wave 8 is LOAD-BEARING; a hole that appears
  in wave 5 and disappears by wave 6 is EPHEMERAL.

  Persistent homology over the wave filtration extracts the
  load-bearing holes from the noise of recursive falsification. The
  runtime should treat load-bearing holes as OPERATIONAL WALLS: e.g.,
  "do not attempt PCA-only at K=5 above hidden=3584" is a wall named
  by F1's persistence across waves 4..8. Ephemeral holes (like
  wave-5 H3) are WARNINGS — a refinement claim that did not survive
  one more wave of measurement.

  The session's persistence diagram has THREE points at infinity
  (F1, F2, F3 — the durable falsifications) and ONE point at (5, 6)
  (the H3 ephemeral refinement). The diagram IS the topology of what
  we know.

  Companion to:
    * `Gnosis.FalsificationLedger`  — the live append-only ledger
    * `Gnosis.AntiTheory`           — the live conjecture/experiment
                                      register
    * `Gnosis.BettiHoleStructure`   — (parallel; structures inlined
                                      below to keep this module
                                      independently buildable)

  Init-only Lean. No Mathlib. All proofs are `decide`. Zero sorries,
  zero axioms.
-/

namespace Gnosis.PersistentHomologyOverWaves

/-! ## 1. Wave stamps as the filtration index -/

/-- A `WaveStamp` is the index into the falsification filtration.
    Waves 1..8 are the session's recorded waves of measurement. -/
abbrev WaveStamp : Type := Nat

/-- Sentinel for "still present in the latest wave we have measured"
    (i.e., the persistence interval is unbounded above on the right
    in the persistence diagram).  In init-only Lean we cap with a
    finite literal rather than introduce a `WithTop` wrapper. -/
def waveInfinity : Nat := 999

/-! ## 2. The Hole record -/

/-- A topological feature in the wave filtration.  `persistence` is
    `last_present_in_wave - first_appeared_in_wave + 1` (in waves).
    A hole present in waves 4..8 has persistence 5. -/
structure Hole where
  hole_id                : Nat
  description            : String
  first_appeared_in_wave : WaveStamp
  last_present_in_wave   : WaveStamp
  persistence            : Nat
  deriving Repr, DecidableEq

/-! ## 3. The session's holes (per-instances) -/

/-- F1: cross-model PCA failure across Qwen family.  Born in
    wave 4, still present in wave 8.  Persistence = 5. -/
def f1_hole : Hole :=
  { hole_id                := 1
  , description            :=
      "F1: cross-model PCA-only at K=5 fails to generalize across Qwen family"
  , first_appeared_in_wave := 4
  , last_present_in_wave   := 8
  , persistence            := 5
  }

/-- F2: strict K=1 spec-decode does not preserve argmax under PCA-only.
    Born in wave 4, still present in wave 8.  Persistence = 5. -/
def f2_hole : Hole :=
  { hole_id                := 2
  , description            :=
      "F2: strict K=1 spec-decode does not preserve argmax under PCA-only"
  , first_appeared_in_wave := 4
  , last_present_in_wave   := 8
  , persistence            := 5
  }

/-- F3: rank density k/hidden_dim is methodology-CONTINGENT, not a
    methodology-independent invariant.  Born in wave 6, still present
    in wave 8.  Persistence = 3. -/
def f3_hole : Hole :=
  { hole_id                := 3
  , description            :=
      "F3: rank density k/hidden_dim is methodology-contingent"
  , first_appeared_in_wave := 6
  , last_present_in_wave   := 8
  , persistence            := 3
  }

/-- Wave 5's H3 hypothesis — a "positive hole": the claim that there
    is a methodology-independent rank-density fix.  It appeared in
    wave 5 and was REFUTED in wave 6 by recursive falsification.
    Persistence = 2 (waves 5..6).  This is the canonical EPHEMERAL
    hole of the session. -/
def wave_5_h3_hypothesis : Hole :=
  { hole_id                := 5
  , description            :=
      "Wave-5 H3: rank density k/hidden_dim is the methodology-independent fix"
  , first_appeared_in_wave := 5
  , last_present_in_wave   := 6
  , persistence            := 2
  }

/-! ## 4. The load-bearing predicate -/

/-- A hole is LOAD-BEARING if it has persisted across at least three
    waves of measurement.  Three waves is the threshold beyond which
    a hole stops looking like a measurement artifact and starts
    looking like a feature of the operational regime. -/
def is_load_bearing (h : Hole) : Bool :=
  decide (h.persistence ≥ 3)

/-! ## 5. Theorems on the session's holes (decide) -/

/-- F1 is load-bearing: persistence 5 ≥ 3. -/
theorem f1_is_load_bearing : is_load_bearing f1_hole = true := by decide

/-- F2 is load-bearing: persistence 5 ≥ 3. -/
theorem f2_is_load_bearing : is_load_bearing f2_hole = true := by decide

/-- F3 is load-bearing: persistence 3 ≥ 3. -/
theorem f3_is_load_bearing : is_load_bearing f3_hole = true := by decide

/-- Wave 5's H3 hypothesis is NOT load-bearing: persistence 2 < 3.
    Treating it as load-bearing would have misled the runtime into
    encoding a wall that does not exist. -/
theorem wave_5_h3_is_NOT_load_bearing :
    is_load_bearing wave_5_h3_hypothesis = false := by decide

/-! ## 6. Aggregate persistence -/

/-- Sum of persistences over a list of holes.  In persistent homology
    this is the L1 length of the persistence vector. -/
def total_persistence : List Hole → Nat
  | []      => 0
  | h :: hs => h.persistence + total_persistence hs

/-- The session's current four holes. -/
def current_holes : List Hole :=
  [f1_hole, f2_hole, f3_hole, wave_5_h3_hypothesis]

/-- The current total persistence across the session is
    `5 + 5 + 3 + 2 = 15`. -/
def current_total_persistence : Nat :=
  total_persistence current_holes

theorem current_total_persistence_eq_15 :
    current_total_persistence = 15 := by decide

/-! ## 7. The persistence diagram -/

/-- The persistence diagram as a list of `(birth, death)` pairs in
    wave-number coordinates.  We use `waveInfinity = 999` as a
    finite sentinel for the three unresolved (still-present) holes,
    since init-only Lean lacks `WithTop`. -/
def persistence_diagram : List (Nat × Nat) :=
  [ (4, waveInfinity)   -- F1: born wave 4, still present
  , (4, waveInfinity)   -- F2: born wave 4, still present
  , (6, waveInfinity)   -- F3: born wave 6, still present
  , (5, 6)              -- Wave-5 H3: born wave 5, died wave 6
  ]

/-- The persistence diagram has exactly four points. -/
theorem persistence_diagram_has_four_points :
    persistence_diagram.length = 4 := by decide

/-- Three of the four points are at "infinity" (the sentinel
    `waveInfinity`): F1, F2, F3 are durable falsifications. -/
def points_at_infinity : List (Nat × Nat) :=
  persistence_diagram.filter (fun p => decide (p.2 = waveInfinity))

theorem three_points_at_infinity :
    points_at_infinity.length = 3 := by decide

/-- Exactly one point is finite — the ephemeral H3 refinement at
    `(5, 6)`. -/
def finite_points : List (Nat × Nat) :=
  persistence_diagram.filter (fun p => decide (p.2 ≠ waveInfinity))

theorem one_finite_point :
    finite_points.length = 1 := by decide

theorem the_finite_point_is_the_h3_refinement :
    finite_points = [(5, 6)] := by decide

/-! ## 8. Ephemeral refinements predict recursive falsification -/

/-- A hole is EPHEMERAL if its persistence is at most 2 waves.  An
    ephemeral hole is a methodology-dependent or itself-contingent
    refinement: it lived for a wave or two and was knocked down by
    the next round of measurement. -/
def is_ephemeral (h : Hole) : Bool :=
  decide (h.persistence ≤ 2)

/-- The session's wave-5 H3 hypothesis is ephemeral. -/
theorem wave_5_h3_is_ephemeral :
    is_ephemeral wave_5_h3_hypothesis = true := by decide

/-- An ephemeral hole is exactly NOT a load-bearing hole, on the
    session's holes (the threshold is 3, the ephemeral cutoff is 2,
    so they partition the session's persistence values). -/
theorem ephemeral_iff_not_load_bearing_on_h3 :
    is_ephemeral wave_5_h3_hypothesis
      = !(is_load_bearing wave_5_h3_hypothesis) := by decide

/-- The "ephemeral refinements predict recursive falsification"
    theorem: the wave-5 H3 hypothesis is ephemeral, and ephemerality
    is the topological signature of recursive falsification.  In the
    session's record, H3 was proposed as a "fix" in wave 5 and was
    refuted in wave 6 — exactly a 2-wave persistence interval.
    This is the WITNESS pattern the runtime should watch for: any
    refinement claim with persistence ≤ 2 is methodology-dependent
    or itself contingent, and should not be treated as durable. -/
theorem ephemeral_refinement_predicts_recursive_falsification :
    is_ephemeral wave_5_h3_hypothesis = true
      ∧ wave_5_h3_hypothesis.first_appeared_in_wave = 5
      ∧ wave_5_h3_hypothesis.last_present_in_wave   = 6 := by decide

/-! ## 9. Load-bearing holes are the durable theory content -/

/-- The list of load-bearing holes on a wave's worth of holes. -/
def load_bearing_holes (hs : List Hole) : List Hole :=
  hs.filter is_load_bearing

/-- The session's load-bearing holes are exactly F1, F2, F3. -/
theorem session_load_bearing_holes :
    load_bearing_holes current_holes = [f1_hole, f2_hole, f3_hole] := by
  decide

/-- Exactly three holes in the session are load-bearing. -/
theorem three_load_bearing_holes :
    (load_bearing_holes current_holes).length = 3 := by decide

/-- The "load-bearing holes are the durable theory" theorem.  The
    durable scientific content of the falsification ledger is the
    set of load-bearing holes.  Conjectures and even refinements
    are ephemeral.  The load-bearing holes name the EDGES of the
    operational regime — the places where the runtime is known not
    to work.

    Witness: on the session's four recorded holes, the load-bearing
    set is exactly `[F1, F2, F3]` (length 3) and the ephemeral
    remainder is exactly `[wave_5_h3_hypothesis]`. -/
theorem theory_content_is_load_bearing_holes :
    load_bearing_holes current_holes = [f1_hole, f2_hole, f3_hole]
      ∧ (current_holes.filter is_ephemeral) = [wave_5_h3_hypothesis]
      ∧ (load_bearing_holes current_holes).length
          + (current_holes.filter is_ephemeral).length
        = current_holes.length := by
  decide

/-! ## 10. Operational walls named by load-bearing holes -/

/-- An OPERATIONAL WALL is a (description, since-wave) pair extracted
    from a load-bearing hole.  The runtime should refuse to attempt
    operations that fall on the wrong side of any such wall. -/
structure OperationalWall where
  description : String
  since_wave  : WaveStamp
  deriving Repr

/-- Map a load-bearing hole to the wall it names. -/
def hole_to_wall (h : Hole) : OperationalWall :=
  { description := h.description
  , since_wave  := h.first_appeared_in_wave
  }

/-- The session's operational walls — one per load-bearing hole. -/
def session_walls : List OperationalWall :=
  (load_bearing_holes current_holes).map hole_to_wall

theorem three_session_walls :
    session_walls.length = 3 := by decide

/-- The runtime knows three walls, born in waves 4, 4, and 6
    respectively. -/
theorem session_wall_birth_waves :
    session_walls.map (fun w => w.since_wave) = [4, 4, 6] := by decide

end Gnosis.PersistentHomologyOverWaves
