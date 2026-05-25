/-
  ChickieRunSwerveGame.lean
  =========================

  The game of Chicken, and the "Chickie Run" from *Rebel Without a Cause* (1955),
  formalized as a SWERVE game — because the chicken move literally *is* the
  clinamen.

  Lucretius' atoms fall straight down forever and never meet; only the
  *clinamen*, the swerve, the minimal `+1` declination off the deterministic
  line, lets anything happen at all. In `Gnosis/ClinamenInfrathin.lean` that is
  exactly `def swerve (n) := n + 1`, the first successor of the null.

  In the film, two cars race STRAIGHT toward a cliff. The deterministic line is
  the fall. To live you must SWERVE — jump out of the car — before the edge.
  The "chicken" is whoever swerves first; the brave one swerves last and lowest.
  Jim swerves in time and lives. Buzz's jacket sleeve catches on the door
  handle: his clinamen is BLOCKED, the swerve never fires, the car follows the
  pure straight fall, and he goes over the edge. So the theorem this module
  proves, under all its game theory, is:

      the clinamen (the swerve) is survival; a blocked swerve is the cliff.

  Two layers:
    PART I    classic Chicken / Hawk-Dove: payoff matrix, the chicken-vs-PD
              signature, no dominant strategy, the two anti-coordinated Nash
              equilibria. (Companion to `Gnosis/NashEquilibrium.lean`.)
    PART II   the Chickie Run as a swerve-TIMING game over the run to the edge:
              jump-time strategies, jump-at-the-edge optimality, the mutual
              catastrophe, and Buzz's obstruction tragedy.
    PART III  the physical layer (velocity / distance / frame count at 24 fps)
              as finite certificates, plus the four narrative segments.

  Init-only. No Mathlib, no `omega`, no `simp`/`decide` on open-variable goals;
  `decide` / `native_decide` only on closed numerics.
-/
import Init

namespace GnosisMath
namespace ChickieRunSwerveGame

-- ══════════════════════════════════════════════════════════
-- PART I.  THE GAME OF CHICKEN  (Hawk-Dove)
-- ══════════════════════════════════════════════════════════

/-- The two moves. `swerve` is the clinamen — the `+1` declination off the
    deadly straight line (chicken out / jump). `stay` holds the line. -/
inductive Move
  | swerve
  | stay
  deriving DecidableEq

/-
  Chicken's payoff ordering is `T > R > S > P`, and the defining feature that
  separates it from the Prisoner's Dilemma is `S > P`: being the chicken
  (swerving while the other stays) is BETTER than the mutual crash. There is
  therefore no dominant strategy and two pure equilibria.

    T = Temptation : you stay, they swerve — you win the dare.
    R = Reward     : both swerve — mutual face-saving.
    S = Sucker     : you swerve, they stay — "chicken", but alive.
    P = Punishment : both stay — the crash. Death. The worst.
-/

def payoffT : Nat := 4
def payoffR : Nat := 3
def payoffS : Nat := 2
def payoffP : Nat := 0

/-- Row player's payoff given (my move, opponent's move). -/
def myPayoff : Move → Move → Nat
  | Move.stay,   Move.swerve => payoffT   -- I hold, they flinch: I win
  | Move.swerve, Move.swerve => payoffR   -- both flinch
  | Move.swerve, Move.stay   => payoffS   -- I flinch: chicken, but alive
  | Move.stay,   Move.stay   => payoffP   -- both hold: the crash

/-- The chicken payoff ordering `T > R > S > P`. -/
theorem chicken_ordering :
    payoffR < payoffT ∧ payoffS < payoffR ∧ payoffP < payoffS := by decide

/-- **The chicken signature** (this is NOT a Prisoner's Dilemma): the mutual
    crash is strictly worse than being the chicken. In a Dilemma, mutual
    defection beats the sucker (`P > S`); in Chicken it is reversed (`S > P`),
    which is why staying is not dominant. -/
theorem crash_is_worst_not_pd :
    myPayoff Move.stay Move.stay < myPayoff Move.swerve Move.stay := by decide

/-- **No dominant strategy.** Against a swerver you should stay (4 > 3); against
    a stayer you should swerve (2 > 0). The best move depends on the opponent. -/
theorem no_dominant_strategy :
    (myPayoff Move.swerve Move.swerve < myPayoff Move.stay Move.swerve) ∧
    (myPayoff Move.stay Move.stay < myPayoff Move.swerve Move.stay) := by decide

/-- A profile `(m₁, m₂)` is a (pure) Nash equilibrium: neither player can
    improve by a unilateral deviation. The game is symmetric, so player 1's
    payoff is `myPayoff m₁ m₂` and player 2's is `myPayoff m₂ m₁`. -/
def isNash (m1 m2 : Move) : Prop :=
  (∀ m, myPayoff m m2 ≤ myPayoff m1 m2) ∧
  (∀ m, myPayoff m m1 ≤ myPayoff m2 m1)

/-- `(stay, swerve)` is a Nash equilibrium: the stayer wins and won't move; the
    swerver, facing a stayer, prefers chicken (2) to crash (0). -/
theorem nash_stay_swerve : isNash Move.stay Move.swerve := by
  refine ⟨?_, ?_⟩ <;> (intro m; cases m <;> decide)

/-- `(swerve, stay)` is the mirror Nash equilibrium. -/
theorem nash_swerve_stay : isNash Move.swerve Move.stay := by
  refine ⟨?_, ?_⟩ <;> (intro m; cases m <;> decide)

/-- Mutual stay (the crash) is NOT an equilibrium: each driver would rather
    swerve (2) than die (0). -/
theorem not_nash_both_stay : ¬ isNash Move.stay Move.stay := by
  intro h
  exact absurd (h.1 Move.swerve) (by decide)

/-- Mutual swerve is NOT an equilibrium either: each would rather stay (4) and
    win than mutually flinch (3). The macho instability of Chicken. -/
theorem not_nash_both_swerve : ¬ isNash Move.swerve Move.swerve := by
  intro h
  exact absurd (h.1 Move.stay) (by decide)

-- ══════════════════════════════════════════════════════════
-- PART II.  THE CHICKIE RUN  (a swerve-timing game)
-- ══════════════════════════════════════════════════════════

/-
  The film's actual game is not the one-shot matrix above but a TIMING game (a
  war of attrition) played over the run to the cliff. Time is measured in frames
  from the moment the engines fire. The edge is reached at frame `cliff`. Each
  driver chooses a `jumpTime` — the frame at which they swerve out of the car.

    survive  ⇔  jumpTime ≤ cliff        (you got out before the edge)
    braver   ⇔  larger jumpTime          (you stayed in longer)
    winner   = the braver survivor; whoever goes over the edge loses absolutely.

  The chicken matrix payoffs `T, R, S, P` reappear as the outcomes of the timing
  game, so the timing game *refines* the matrix.
-/

/-- Payoff to a driver who swerves at `jSelf` when the opponent swerves at
    `jOpp`, with the edge at frame `cliff`. -/
def chickiePayoff (cliff jSelf jOpp : Nat) : Nat :=
  if jSelf > cliff then payoffP            -- you went over the edge: death
  else if jOpp > cliff then payoffT        -- you survived, opponent went over: total win
  else if jOpp < jSelf then payoffT        -- both survived, you swerved later (braver): win
  else if jOpp = jSelf then payoffR        -- both survived, dead heat
  else payoffS                             -- both survived, you swerved first: chicken

/-- Going over the edge is death — the worst payoff — whatever the opponent
    does. -/
theorem over_the_edge_is_death (cliff jSelf jOpp : Nat) (h : jSelf > cliff) :
    chickiePayoff cliff jSelf jOpp = payoffP := by
  unfold chickiePayoff
  rw [if_pos h]

/-- **Jump at the edge.** Swerving at the very last safe frame (`jSelf = cliff`)
    is never the chicken: you survive and you are at least as brave as anyone who
    also survived, so your payoff is at least `R` — you never collect the
    sucker payoff `S`. This is the rational frontier of the war of attrition. -/
theorem jump_at_edge_never_chicken (cliff jOpp : Nat) :
    payoffR ≤ chickiePayoff cliff cliff jOpp := by
  unfold chickiePayoff
  rw [if_neg (Nat.lt_irrefl cliff)]
  by_cases h1 : jOpp > cliff
  · rw [if_pos h1]; decide
  · rw [if_neg h1]
    by_cases h2 : jOpp < cliff
    · rw [if_pos h2]; decide
    · rw [if_neg h2]
      have hEq : jOpp = cliff :=
        Nat.le_antisymm (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h2)
      rw [if_pos hEq]
      decide

/-- **Mutual catastrophe.** If both drivers stay in past the edge, both die:
    the war of attrition's tragic absorbing state. -/
theorem mutual_overshoot_is_mutual_death (cliff jSelf jOpp : Nat)
    (hS : jSelf > cliff) (hO : jOpp > cliff) :
    chickiePayoff cliff jSelf jOpp = payoffP ∧
    chickiePayoff cliff jOpp jSelf = payoffP := by
  refine ⟨?_, ?_⟩
  · exact over_the_edge_is_death cliff jSelf jOpp hS
  · exact over_the_edge_is_death cliff jOpp jSelf hO

-- ── The clinamen reading: swerve = survival, blocked swerve = the fall. ──

/-- The deterministic fall: a trajectory that never swerves before the edge.
    The car holds the straight Lucretian line and goes over. -/
def deterministicFall (jumpTime cliff : Nat) : Prop := jumpTime > cliff

/-- The clinamen executed: a swerve at or before the edge. The declination off
    the deadly line, in time. -/
def executesClinamen (jumpTime cliff : Nat) : Prop := jumpTime ≤ cliff

/-- **The clinamen is survival.** If the swerve fires in time, the car does not
    take the deterministic fall. -/
theorem clinamen_is_survival (jumpTime cliff : Nat)
    (h : executesClinamen jumpTime cliff) : ¬ deterministicFall jumpTime cliff := by
  unfold executesClinamen at h
  unfold deterministicFall
  exact Nat.not_lt_of_le h

-- ── Buzz's tragedy: the obstruction that blocks the clinamen. ──

/-- The realized jump time. With the swerve free, the driver jumps at their
    intended frame. With the swerve OBSTRUCTED (the sleeve caught on the
    handle), the jump never fires before the edge — modeled as `cliff + 1`,
    one frame past the point of no return. -/
def realizedJump : Bool → Nat → Nat → Nat
  | true,  _intended, cliff => cliff + 1   -- clinamen blocked: never escapes
  | false, intended,  _cliff => intended   -- clinamen free: jumps as intended

/-- A free swerve realizes the intended jump. -/
theorem free_swerve_realizes_intent (intended cliff : Nat) :
    realizedJump false intended cliff = intended := rfl

/-- **A blocked clinamen is the deterministic fall.** When the swerve is
    obstructed, the realized trajectory overshoots the edge — exactly the
    straight Lucretian line. No swerve, no escape. -/
theorem blocked_clinamen_is_fall (intended cliff : Nat) :
    deterministicFall (realizedJump true intended cliff) cliff := by
  unfold deterministicFall
  show cliff + 1 > cliff
  exact Nat.lt_succ_self cliff

/-- **Buzz's tragedy.** Take the bravest *survivable* plan: swerve at the very
    edge (`jSelf = cliff`). With the clinamen free it earns at least a draw
    (`≥ R`). With the clinamen blocked — the sleeve caught — the identical plan
    becomes death (`= P`), and death is strictly worse. The gap between the
    intended and the realized swerve is the whole tragedy. -/
theorem buzz_tragedy (cliff jOpp : Nat) :
    payoffR ≤ chickiePayoff cliff (realizedJump false cliff cliff) jOpp ∧
    chickiePayoff cliff (realizedJump true cliff cliff) jOpp = payoffP ∧
    payoffP < payoffR := by
  refine ⟨?_, ?_, ?_⟩
  · show payoffR ≤ chickiePayoff cliff cliff jOpp
    exact jump_at_edge_never_chicken cliff jOpp
  · show chickiePayoff cliff (cliff + 1) jOpp = payoffP
    exact over_the_edge_is_death cliff (cliff + 1) jOpp (Nat.lt_succ_self cliff)
  · decide

-- ══════════════════════════════════════════════════════════
-- PART III.  THE PHYSICAL LAYER  (finite certificates) + NARRATIVE
-- ══════════════════════════════════════════════════════════

/-
  Measured stopwatch timecodes of the run (Rustic Church bridge rule: the
  physics is stated as finite data; only its arithmetic consequences are
  proved). Source: the clip at youtu.be/cyXaW9Jucmc —

    start of the run  t = 52 s   (engines fire)
    Buzz's sleeve     t = 74 s   (the jacket catches the door handle)
    Jim bails         t = 79 s   (he swerves out)
    car over the edge t = 83 s

  Frames are counted at 24 fps from the start of the run.
-/

def fps : Nat := 24
def runStartSec : Nat := 52     -- the run begins
def sleeveSec : Nat := 74       -- Buzz's sleeve catches the handle
def bailSec : Nat := 79         -- Jim bails out of his car
def edgeSec : Nat := 83         -- the car goes over the edge

/-- Length of the run to the edge, in seconds: 83 − 52 = 31. -/
def runDurationSec : Nat := edgeSec - runStartSec
/-- The edge, in frames from the start of the run: 31 · 24 = 744. -/
def cliffFrames : Nat := runDurationSec * fps
/-- The frame at which Buzz's clinamen is blocked (sleeve caught): 22 · 24 = 528. -/
def sleeveFrame : Nat := (sleeveSec - runStartSec) * fps
/-- The frame at which Jim swerves out: 27 · 24 = 648. -/
def jimBailFrame : Nat := (bailSec - runStartSec) * fps

theorem run_duration_seconds : runDurationSec = 31 := by decide
theorem edge_in_frames : cliffFrames = 744 := by decide
theorem sleeve_in_frames : sleeveFrame = 528 := by decide
theorem jim_bail_in_frames : jimBailFrame = 648 := by decide

/-- **Jim swerves with margin and lives.** Jim's bail at frame 648 is well
    before the edge at 744 — he executes the clinamen, with 96 frames (four
    seconds) to spare. -/
theorem jim_executes_clinamen : executesClinamen jimBailFrame cliffFrames := by
  unfold executesClinamen; decide
theorem jim_margin_frames : cliffFrames - jimBailFrame = 96 := by decide
theorem jim_margin_seconds : edgeSec - bailSec = 4 := by decide

/-- **The doomed window.** Buzz's sleeve catches 216 frames — nine full
    seconds — before the edge: his swerve is foreclosed while the car is still
    far up the plateau. Nine seconds alive, but already fallen. -/
theorem buzz_doomed_window_frames : cliffFrames - sleeveFrame = 216 := by decide
theorem buzz_doomed_window_seconds : edgeSec - sleeveSec = 9 := by decide

/-- The sleeve catches strictly before the edge — and before Jim even bails. -/
theorem sleeve_before_edge : sleeveFrame < cliffFrames := by decide
theorem sleeve_before_bail : sleeveFrame < jimBailFrame := by decide

/-- The scene in the measured frames: Jim swerves at frame 648 (96 frames shy of
    the edge) and takes the winning payoff; Buzz's sleeve, caught at frame 528,
    forces his realized jump one frame past the edge, and he dies. -/
theorem jim_lives_buzz_dies :
    chickiePayoff cliffFrames jimBailFrame (realizedJump true sleeveFrame cliffFrames) = payoffT ∧
    chickiePayoff cliffFrames (realizedJump true sleeveFrame cliffFrames) jimBailFrame = payoffP := by
  refine ⟨?_, ?_⟩ <;> decide

-- ── The four narrative segments of the sequence. ──

/-- The four scenes the sequence builds through. The swerve window is the
    `race`; the `climax` is the edge crossed. -/
inductive Phase
  | setup        -- arrival at the bluff, the onlookers, Jim and Buzz
  | preparation  -- talking to Judy, dirt rubbed on the palms, engines set
  | race         -- the run: cars accelerate toward the cliff (the swerve window)
  | climax       -- the edge: the jump, and Buzz's car over the side
  deriving DecidableEq

def phaseRank : Phase → Nat
  | Phase.setup => 0
  | Phase.preparation => 1
  | Phase.race => 2
  | Phase.climax => 3

/-- The segments are strictly ordered as the tension builds. -/
theorem phases_strictly_ordered :
    phaseRank Phase.setup < phaseRank Phase.preparation ∧
    phaseRank Phase.preparation < phaseRank Phase.race ∧
    phaseRank Phase.race < phaseRank Phase.climax := by decide

/-- Which phase a swerve at frame `j` lands in: still in the race if it beats
    the edge, otherwise the climax (the car is already going over). -/
def phaseOfJump (j : Nat) : Phase :=
  if j ≤ cliffFrames then Phase.race else Phase.climax

/-- A swerve inside the race phase survives: it executes the clinamen and avoids
    the deterministic fall. -/
theorem race_jump_survives (j : Nat) (h : j ≤ cliffFrames) :
    phaseOfJump j = Phase.race ∧ ¬ deterministicFall j cliffFrames := by
  refine ⟨?_, ?_⟩
  · unfold phaseOfJump; rw [if_pos h]
  · exact clinamen_is_survival j cliffFrames h

/-- A swerve that slips into the climax phase is the fall: it has crossed the
    edge and dies. -/
theorem climax_jump_dies (j : Nat) (h : cliffFrames < j) :
    phaseOfJump j = Phase.climax ∧ deterministicFall j cliffFrames := by
  refine ⟨?_, ?_⟩
  · unfold phaseOfJump; rw [if_neg (Nat.not_le_of_lt h)]
  · unfold deterministicFall; exact h

-- ══════════════════════════════════════════════════════════
-- MASTER BUNDLE
-- ══════════════════════════════════════════════════════════

/-- The Chickie Run, bundled: Chicken has two anti-coordinated equilibria and no
    dominant strategy; the mutual crash is its worst outcome; the rational edge
    of the timing game is to swerve at the last frame; and the whole tragedy is
    that a blocked clinamen turns that same brave plan into the deterministic
    fall over the cliff. -/
theorem chickie_run_master (cliff jOpp : Nat) :
    -- two pure equilibria, none dominant, crash is worst
    isNash Move.stay Move.swerve ∧
    isNash Move.swerve Move.stay ∧
    ¬ isNash Move.stay Move.stay ∧
    myPayoff Move.stay Move.stay < myPayoff Move.swerve Move.stay ∧
    -- jump-at-edge is never the chicken
    payoffR ≤ chickiePayoff cliff cliff jOpp ∧
    -- the swerve saves; the blocked swerve is the fall
    deterministicFall (realizedJump true cliff cliff) cliff ∧
    chickiePayoff cliff (realizedJump true cliff cliff) jOpp = payoffP := by
  refine ⟨nash_stay_swerve, nash_swerve_stay, not_nash_both_stay,
          crash_is_worst_not_pd, jump_at_edge_never_chicken cliff jOpp,
          blocked_clinamen_is_fall cliff cliff, ?_⟩
  exact over_the_edge_is_death cliff (realizedJump true cliff cliff) jOpp
        (blocked_clinamen_is_fall cliff cliff)

end ChickieRunSwerveGame
end GnosisMath
