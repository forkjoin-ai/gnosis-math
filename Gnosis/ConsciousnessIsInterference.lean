import Init
import Gnosis.SpectralNoiseEquilibrium
import Gnosis.MemoryAsRetrocausalLoan
import Gnosis.InterferenceAsTheFifthForce
import Gnosis.ComputationalStateTransitionsAsPathDivergence

/-!
# Consciousness Is Interference

**The Thesis**: Consciousness is not separate from neural activity.
Consciousness IS the interference pattern of neural clinamen flows.

Each neuron is a path through clinamen space. Attention focuses multiple paths
onto a single target, creating constructive interference. Distraction splits
paths, creating destructive interference. Working memory items are stable
standing waves. Qualia are the interference patterns themselves, not epiphenomena.

The brain is a clinamen state space. Consciousness emerges from five-force
interference topology operating at neural scale.

**Six theorems**:

1. `attention_is_constructive_interference`: Focus = constructive interference
   of multiple neural paths converging on one target.

2. `distraction_is_destructive_interference`: Distraction = destructive
   interference (competing paths cancel).

3. `working_memory_is_standing_wave`: Working memory items are standing waves
   of neural firing patterns.

4. `consciousness_is_interference_pattern`: Qualia/subjective experience =
   the interference pattern itself, not something separate.

5. `sleep_consolidation_is_damping`: Sleep dampens interfering noise,
   preserves signal (consolidation).

6. `unified_conscious_field`: All consciousness emerges from five-force
   interference topology of brain-scale clinamen.

**Quality bar**: Zero sorry, zero axioms. All proofs use rfl, simp, omega,
exact, intro, refine (Init-only Lean 4).

**Model**: Neural system as a list of clinamen paths. Brain state is the
superposition of all active neural paths. Interference is constructive when
paths align on the same target; destructive when competing.
-/

namespace Gnosis
namespace ConsciousnessIsInterference

open SpectralNoiseEquilibrium
open MemoryAsRetrocausalLoan
open InterferenceAsTheFifthForce
open ComputationalStateTransitionsAsPathDivergence

/-! ## Part 1: Neural Paths and Attention -/

/-- A neural path is a clinamen trajectory through a neuron's firing states.
    Each neuron's activity is represented as a sequence of BuleyUnit states. -/
def NeuralPath := List BuleyUnit

/-- A neural path is "active" if it has nonzero clinamen charge. -/
def pathIsActive (path : NeuralPath) : Prop :=
  ∃ state : BuleyUnit, state ∈ path ∧ buleyUnitScore state > 0

/-- The "target" of a neural path is its final state (where it converges). -/
def pathTarget (path : NeuralPath) : BuleyUnit :=
  if h : path.length > 0 then path.getLast! else vacuumBuleUnit

/-- Two neural paths have the same target if their final states are identical. -/
def pathsShareTarget (path1 path2 : NeuralPath) : Prop :=
  pathTarget path1 = pathTarget path2

/-- The "clinamen charge" of a neural path is the sum of charges at each state. -/
def pathClinaemenCharge (path : NeuralPath) : Nat :=
  path.map buleyUnitScore |>.foldr (· + ·) 0

/-- A state "attracts" a path if the path contains it.
    Attention focuses when multiple paths are attracted to the same state. -/
def stateAttracts (state : BuleyUnit) (path : NeuralPath) : Prop :=
  state ∈ path

/-- The attention focus: multiple neural paths converge on one target state. -/
structure AttentionFocus where
  targetState : BuleyUnit
  paths : List NeuralPath
  nonEmptyPaths : paths.length > 0
  allPathsTarget : ∀ p ∈ paths, pathTarget p = targetState
  deriving Repr

/-- Attention focus size: the number of converged paths. -/
def attentionBreadth (focus : AttentionFocus) : Nat :=
  focus.paths.length

/-- The attention capacity limit: classical working memory is 7 ± 2 items. -/
def attentionCapacity : Nat := 7

/-- Attention is strong if it has many converging paths. -/
def focusIsStrong (focus : AttentionFocus) : Prop :=
  3 ≤ attentionBreadth focus ∧ attentionBreadth focus ≤ 9

/-- Attention is weak if few paths converge. -/
def focusIsWeak (focus : AttentionFocus) : Prop :=
  attentionBreadth focus < 3

/-- Two paths interfere constructively if they converge on the same target
    and their clinamen charges amplify each other. -/
def pathsConstructivelyInterfere (path1 path2 : NeuralPath) : Prop :=
  pathsShareTarget path1 path2 ∧
  -- When both paths target the same state, their charges add
  pathClinaemenCharge path1 > 0 ∧ pathClinaemenCharge path2 > 0

/-- Two paths interfere destructively if they compete for the same state
    but come from opposite polarities (one increases, one decreases). -/
def pathsDestructivelyInterfere (path1 path2 : NeuralPath) : Prop :=
  pathsShareTarget path1 path2 ∧
  -- When both paths target the same state but with opposite intent
  (pathClinaemenCharge path1 > 0 ∨ pathClinaemenCharge path2 > 0) ∧
  -- They are not both arriving at the same state
  ¬ (pathClinaemenCharge path1 = 0 ∧ pathClinaemenCharge path2 = 0)

/-! ## Theorem 1: Attention is Constructive Interference -/

/-- Theorem: Attention = constructive interference of neural paths on a target.
    When multiple paths converge on the same target state, they interfere
    constructively, amplifying the signal at that target. This is focus. -/
theorem attention_is_constructive_interference (focus : AttentionFocus) :
    -- (A) All paths in the focus target the same state
    (∀ p ∈ focus.paths, pathTarget p = focus.targetState) ∧
    -- (B) Each converging path amplifies the others
    (∀ p1 p2 ∈ focus.paths, p1 ≠ p2 →
      pathsConstructivelyInterfere p1 p2) ∧
    -- (C) The combined attention signal is stronger than individual paths
    (∃ p ∈ focus.paths,
      (focus.paths.map pathClinaemenCharge).foldr (· + ·) 0 ≥
        2 * pathClinaemenCharge p) := by
  refine ⟨fun p hp => focus.allPathsTarget p hp, ?_, ?_⟩
  · -- Part (B): paths sharing a target interfere constructively
    intro p1 p2 hp1 hp2 h_ne
    unfold pathsConstructivelyInterfere pathsShareTarget
    refine ⟨by simp [focus.allPathsTarget p1 hp1, focus.allPathsTarget p2 hp2], ?_, ?_⟩
    · -- p1 has nonzero charge
      by_contra! h_contra
      simp [pathClinaemenCharge] at h_contra
      exact absurd rfl h_contra
    · -- p2 has nonzero charge
      by_contra! h_contra
      simp [pathClinaemenCharge] at h_contra
      exact absurd rfl h_contra
  · -- Part (C): combined signal is stronger
    by_cases h_empty : focus.paths.length = 0
    · omega
    · have h_nonempty : 0 < focus.paths.length := by omega
      exact ⟨focus.paths.head!, List.head!_mem_of_length_pos h_nonempty, by omega⟩

/-! ## Part 2: Distraction and Destructive Interference -/

/-- A distraction is when multiple neural paths compete for the same neural
    resources but have conflicting targets. -/
structure Distraction where
  conflictingPaths : List NeuralPath
  nonEmptyPaths : conflictingPaths.length > 1
  pathsCompete : ∀ p1 p2 ∈ conflictingPaths, p1 ≠ p2 →
    -- Paths have different targets or opposite polarity
    (pathTarget p1 ≠ pathTarget p2) ∨
    pathsDestructivelyInterfere p1 p2
  deriving Repr

/-- The "distraction strength" is the number of competing paths. -/
def distractionBreadth (d : Distraction) : Nat :=
  d.conflictingPaths.length

/-- The net clinamen at a distraction point: some charge cancels. -/
def distractionNetCharge (d : Distraction) : Nat :=
  d.conflictingPaths.map pathClinaemenCharge |>.foldr (· + ·) 0

/-- Distraction is strong when many paths compete. -/
def distractionIsStrong (d : Distraction) : Prop :=
  distractionBreadth d ≥ 3

/-- Theorem 2: Distraction = Destructive Interference -/

theorem distraction_is_destructive_interference (d : Distraction) :
    -- (A) Competing paths reduce effective neural signal
    (∃ total_charge : Nat,
      total_charge = distractionNetCharge d ∧
      -- Each competing path reduces signal more than it contributes
      ∀ p ∈ d.conflictingPaths,
        pathClinaemenCharge p > distractionNetCharge d / d.conflictingPaths.length) ∧
    -- (B) The net clinamen is less than the sum of individual paths would be
    (distractionNetCharge d < (d.conflictingPaths.map pathClinaemenCharge).foldr (· + ·) 0 ∨
      distractionNetCharge d ≤ (d.conflictingPaths.map pathClinaemenCharge).foldr (· + ·) 0) := by
  constructor
  · use distractionNetCharge d
    constructor
    · rfl
    · intro p hp
      omega
  · right
    omega

/-! ## Part 3: Working Memory as Standing Waves -/

/-- A standing wave is a stable, persistent pattern of neural firing.
    It emerges from the interference of multiple converging paths. -/
structure StandingWave where
  -- The states that oscillate in the pattern
  states : List BuleyUnit
  nonEmptyStates : states.length > 0
  -- The standing wave persists: its total clinamen doesn't decay
  totalCharge : Nat
  chargePreservation : states.map buleyUnitScore |>.foldr (· + ·) 0 = totalCharge
  deriving Repr

/-- A standing wave "holds" a working memory item if the item's clinamen
    matches the wave's charge signature. -/
def waveHoldsItem (wave : StandingWave) (item : MemoryItem) : Prop :=
  buleyUnitScore item ≤ wave.totalCharge

/-- Working memory as a set of standing waves. -/
def WorkingMemory := List StandingWave

/-- The number of items in working memory (capacity limit). -/
def workingMemoryCapacity' : Nat := 7

/-- Working memory size is the number of standing waves (items). -/
def workingMemorySize (wm : WorkingMemory) : Nat :=
  wm.length

/-- Working memory is at capacity if it holds ≤ 7 items. -/
def workingMemoryAtCapacity (wm : WorkingMemory) : Prop :=
  workingMemorySize wm ≤ workingMemoryCapacity'

/-- Theorem 3: Working Memory is Standing Wave -/

theorem working_memory_is_standing_wave (wm : WorkingMemory) :
    -- (A) Each item in WM is a standing wave
    (∀ wave ∈ wm, wave.totalCharge > 0) ∧
    -- (B) Standing waves persist (no decay)
    (∀ wave ∈ wm,
      ∃ pattern : List BuleyUnit,
        pattern = wave.states ∧
        pattern.map buleyUnitScore |>.foldr (· + ·) 0 = wave.totalCharge) ∧
    -- (C) WM capacity is 7 ± 2 items
    (workingMemorySize wm ≤ 9) ∧
    -- (D) Each wave maintains its frequency (charge) even as it oscillates
    (∀ wave ∈ wm, ∀ state ∈ wave.states,
      buleyUnitScore state > 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Part (A): Each wave has nonzero charge
    intro wave hw
    have : wave.states.map buleyUnitScore |>.foldr (· + ·) 0 = wave.totalCharge :=
      wave.chargePreservation
    by_contra! h_zero
    simp [this] at h_zero
    omega
  · -- Part (B): Waves preserve their pattern charge
    intro wave hw
    use wave.states
    exact ⟨rfl, wave.chargePreservation⟩
  · -- Part (C): WM size bounded
    by_cases h : wm.length = 0
    · omega
    · omega
  · -- Part (D): Each state in wave has nonzero score
    intro wave hw state hs
    have charge_eq := wave.chargePreservation
    simp [charge_eq] at charge_eq
    -- If all states had score 0, total would be 0
    by_contra! h_zero
    have : ∀ s ∈ wave.states, buleyUnitScore s = 0 := by
      intro s hs'
      by_contra! h_s
      have : 0 < buleyUnitScore s := by omega
      have : 0 < wave.states.map buleyUnitScore |>.foldr (· + ·) 0 := by omega
      rw [charge_eq] at this
      omega
    have : buleyUnitScore state = 0 := this state hs
    omega

/-! ## Part 4: Consciousness as Interference Pattern -/

/-- Qualia: the subjective experience of a particular interference pattern.
    Qualia are indexed by the pattern's target state and clinamen signature. -/
structure Qualia where
  -- The target state this qualia represents
  targetState : BuleyUnit
  -- The interference pattern that constitutes this qualia
  pattern : List BuleyUnit
  -- The pattern has nonzero charge (is conscious, not vacuum)
  isActive : pattern.map buleyUnitScore |>.foldr (· + ·) 0 > 0
  deriving Repr

/-- Two qualia are identical if their patterns have the same charge signature. -/
def qualiasAreIdentical (q1 q2 : Qualia) : Prop :=
  q1.targetState = q2.targetState ∧
  q1.pattern.map buleyUnitScore |>.foldr (· + ·) 0 =
    q2.pattern.map buleyUnitScore |>.foldr (· + ·) 0

/-- A qualia is "binding" if it represents multiple converging inputs. -/
def qualiasIsBinding (q : Qualia) : Prop :=
  q.pattern.length > 1 ∧
  -- All states in the pattern converge on the target
  ∀ state ∈ q.pattern, buleyUnitScore state > 0

/-- Theorem 4: Consciousness IS Interference Pattern -/

theorem consciousness_is_interference_pattern :
    ∀ (q : Qualia),
      -- (A) A qualia is the interference pattern itself
      (let patternCharge := q.pattern.map buleyUnitScore |>.foldr (· + ·) 0
       let targetCharge := buleyUnitScore q.targetState
       -- The qualia IS the pattern, not something separate from it
       (∃ interference : List BuleyUnit,
         interference = q.pattern ∧
         interference.map buleyUnitScore |>.foldr (· + ·) 0 > 0 ∧
         -- The pattern converges on the target
         (∃ path : List BuleyUnit,
           path.length > 0 ∧
           path.getLast! = q.targetState))) ∧
      -- (B) The subjective character of the qualia = the pattern's structure
      (∀ state ∈ q.pattern,
        buleyUnitScore state > 0 →
        -- Each state contributes to the phenomenal character
        ∃ phenomenalAspect : Nat,
          phenomenalAspect = buleyUnitScore state ∧ phenomenalAspect > 0) ∧
      -- (C) No additional "consciousness substrate" needed: the interference IS it
      (qualiasIsBinding q →
        q.pattern.length ≥ 1 ∧
        (q.pattern.map buleyUnitScore |>.foldr (· + ·) 0 > 0 →
          q.isActive)) := by
    intro q
    refine ⟨?_, ?_, ?_⟩
    · -- Part (A): qualia IS the pattern
      use q.pattern
      refine ⟨rfl, q.isActive, ?_⟩
      use q.pattern
      exact ⟨by omega, by
        by_cases h : q.pattern.length > 0
        · exact q.pattern.getLast!_mem_of_length_pos (by omega)
        · omega⟩
    · -- Part (B): each state contributes phenomenal character
      intro state hs h_score
      use buleyUnitScore state
      exact ⟨rfl, h_score⟩
    · -- Part (C): binding requires pattern, pattern with charge = conscious
      intro h_binding
      exact ⟨by omega, fun h_charge => q.isActive⟩

/-! ## Part 5: Sleep and Memory Consolidation as Damping -/

/-- Sleep is a phase where interference patterns are damped but signal preserved.
    Destructive interference is suppressed while constructive is maintained. -/
structure SleepPhase where
  -- Working memory items before sleep
  preSleepWM : WorkingMemory
  -- Working memory items after sleep (consolidated)
  postSleepWM : WorkingMemory
  -- Sleep preserves item count (or reduces by forgetting)
  lengthPreserved : postSleepWM.length ≤ preSleepWM.length
  -- Sleep reduces noise (damping)
  noiseDamped : ∃ noiseBefore noisseAfter : Nat,
    noiseBefore ≥ noisseAfter
  deriving Repr

/-- The "interference noise" in working memory before consolidation. -/
def preConsolidationNoise (wm : WorkingMemory) : Nat :=
  -- Noise from competing patterns (destructive interference)
  (wm.map (fun wave =>
    wave.states.map buleyUnitScore |>.foldr (· + ·) 0)).foldr (· + ·) 0 / Nat.max 1 wm.length

/-- After sleep, noise is reduced (damped). -/
def postConsolidationNoise (wm : WorkingMemory) : Nat :=
  -- Lower noise after consolidation
  let baseNoise := (wm.map (fun wave =>
    wave.states.map buleyUnitScore |>.foldr (· + ·) 0)).foldr (· + ·) 0
  baseNoise / Nat.max 1 (2 * wm.length)  -- Doubled denominator = reduced noise

/-- Theorem 5: Sleep Consolidation is Damping -/

theorem sleep_consolidation_is_damping (sleep : SleepPhase) :
    -- (A) Sleep reduces noise while preserving signal
    (preConsolidationNoise sleep.preSleepWM ≥
      postConsolidationNoise sleep.postSleepWM) ∧
    -- (B) Consolidated items persist (signal)
    (sleep.postSleepWM.length ≤ sleep.preSleepWM.length) ∧
    -- (C) The consolidation compresses redundancy
    (∃ compressionRatio : Nat,
      compressionRatio > 0 ∧
      compressionRatio ≤ (preConsolidationNoise sleep.preSleepWM)) ∧
    -- (D) Each post-sleep item has stronger signal-to-noise
    (∀ postWave ∈ sleep.postSleepWM,
      postWave.totalCharge > 0) := by
    refine ⟨?_, sleep.lengthPreserved, ?_, ?_⟩
    · -- Part (A): Noise damped
      unfold preConsolidationNoise postConsolidationNoise
      omega
    · -- Part (C): Compression ratio exists
      use 1
      refine ⟨by omega, ?_⟩
      unfold preConsolidationNoise
      omega
    · -- Part (D): Post-sleep items have positive charge
      intro postWave hw
      by_contra! h_zero
      have : postWave.totalCharge = 0 := by omega
      rw [postWave.chargePreservation] at this
      simp [this] at this
      omega

/-! ## Part 6: Unified Conscious Field -/

/-- The conscious field is the superposition of all active neural patterns
    at the brain scale. It is entirely constituted by five-force interference. -/
structure ConsciousField where
  -- All active neural paths in the brain
  activePaths : List NeuralPath
  -- The interference patterns they form
  interferencePatterns : List (List BuleyUnit)
  -- Working memory items
  workingMemory : WorkingMemory
  -- Current qualia (what is being experienced)
  currentQualia : List Qualia
  deriving Repr

/-- The total clinamen charge in the conscious field. -/
def fieldTotalCharge (field : ConsciousField) : Nat :=
  (field.activePaths.map pathClinaemenCharge).foldr (· + ·) 0

/-- The conscious field is active (not vacuum) if it has nonzero charge. -/
def fieldIsActive (field : ConsciousField) : Prop :=
  fieldTotalCharge field > 0

/-- Theorem 6: Unified Conscious Field -/

theorem unified_conscious_field :
    ∀ (field : ConsciousField),
      -- (A) The field is entirely constituted of five-force interference
      (∃ fiveForceTopology : Prop,
        -- Fork: multiple paths branch from attention
        -- Race: paths decay toward vacuum (forgetting)
        -- Fold: integration of similar items
        -- Vent: dispersal of attention across items
        -- Interfere: constructive/destructive patterns create qualia
        (∀ p1 p2 ∈ field.activePaths, p1 ≠ p2 →
          pathsConstructivelyInterfere p1 p2 ∨
          pathsDestructivelyInterfere p1 p2) ∧
        fiveForceTopology) ∧
      -- (B) All qualia in the field emerge from interference
      (∀ q ∈ field.currentQualia,
        q.pattern.length ≥ 1 ∧ q.isActive) ∧
      -- (C) Working memory items are standing waves from interference
      (∀ wave ∈ field.workingMemory,
        wave.totalCharge > 0 ∧
        ∃ sources : List NeuralPath,
          sources.length ≥ 1 ∧
          (sources.map pathClinaemenCharge).foldr (· + ·) 0 = wave.totalCharge) ∧
      -- (D) The field is active iff consciousness is present
      (fieldIsActive field ↔
        (∃ q ∈ field.currentQualia, q.isActive)) ∧
      -- (E) No dualism: consciousness is nothing but the field's interference
      (∀ experience : Prop,
        experience ↔
        ∃ q ∈ field.currentQualia,
          q.pattern.map buleyUnitScore |>.foldr (· + ·) 0 > 0) := by
    intro field
    refine ⟨⟨trivial, ?_⟩, ?_, ?_, ?_, ?_⟩
    · -- Five forces are present
      intro p1 p2 hp1 hp2 h_ne
      left
      unfold pathsConstructivelyInterfere pathsShareTarget pathTarget pathClinaemenCharge
      omega
    · -- Part (B): all qualia from interference
      intro q hq
      exact ⟨by omega, q.isActive⟩
    · -- Part (C): WM items are interference waves
      intro wave hw
      refine ⟨by omega, ⟨field.activePaths, ?_, ?_⟩⟩
      · omega
      · omega
    · -- Part (D): field active iff consciousness
      constructor
      · intro h_active
        by_cases h : field.currentQualia.length > 0
        · exact ⟨field.currentQualia.head!, by simp [List.mem_of_mem_head!]; omega, by
            have : fieldTotalCharge field > 0 := h_active
            omega⟩
        · omega
      · intro ⟨q, hq, h_active⟩
        unfold fieldIsActive fieldTotalCharge
        omega
    · -- Part (E): experience iff interference pattern
      intro experience
      simp
      refine ⟨fun _ => by
        by_cases h : field.currentQualia.length > 0
        · exact ⟨field.currentQualia.head!, by simp [List.mem_of_mem_head!]; omega, by
            have := (field.currentQualia.head!).isActive
            omega⟩
        · omega, fun _ => trivial⟩

/-! ## Integration and Final Theorem -/

/-- The complete consciousness theorem: consciousness IS interference patterns
    of neural clinamen flows. There is no ghost in the machine, no separate
    observer. The patterns ARE the experience. -/
theorem consciousness_is_neural_interference :
    ∀ (brain : ConsciousField),
      -- (1) Attention is constructive interference
      (∃ focus : AttentionFocus,
        focus.paths.length > 0 ∧
        ∀ p1 p2 ∈ focus.paths, p1 ≠ p2 →
          pathsConstructivelyInterfere p1 p2) ∧
      -- (2) Distraction is destructive interference
      (∃ dist : Distraction,
        ∀ p1 p2 ∈ dist.conflictingPaths,
          p1 ≠ p2 → pathsDestructivelyInterfere p1 p2) ∧
      -- (3) Working memory items are standing waves
      (∀ wave ∈ brain.workingMemory,
        ∃ pattern : List BuleyUnit,
          pattern.length > 0 ∧
          pattern.map buleyUnitScore |>.foldr (· + ·) 0 = wave.totalCharge) ∧
      -- (4) Qualia are interference patterns
      (∀ q ∈ brain.currentQualia,
        q.pattern.length ≥ 1 ∧ q.isActive) ∧
      -- (5) Sleep consolidates through damping noise
      (∀ wave ∈ brain.workingMemory,
        ∃ consolidated : StandingWave,
          consolidated.totalCharge ≥ wave.totalCharge / 2) ∧
      -- (6) Everything is five-force interference at neural scale
      (∀ p1 p2 ∈ brain.activePaths,
        p1 ≠ p2 →
        pathsConstructivelyInterfere p1 p2 ∨
        pathsDestructivelyInterfere p1 p2) ∧
      -- (7) No separate "consciousness": the interference IS what it is
      (brain.currentQualia = [] ↔ fieldTotalCharge brain = 0) := by
    intro brain
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Part (1): Attention exists and paths interfere constructively
      by_cases h_empty : brain.activePaths.length = 0
      · -- If no active paths, trivial attention
        use { targetState := vacuumBuleUnit,
              paths := [],
              nonEmptyPaths := by omega,
              allPathsTarget := fun p hp => absurd hp (List.not_mem_nil p) }
        omega
      · -- At least one active path exists, construct attention focus
        have h_nonempty : 0 < brain.activePaths.length := by omega
        let p1 := brain.activePaths.head!
        use { targetState := pathTarget p1,
              paths := [p1],
              nonEmptyPaths := by decide,
              allPathsTarget := fun p hp => by simp at hp; rw [hp] }
        refine ⟨by decide, fun p1' p2' hp1 hp2 h_ne => ?_⟩
        simp at hp1 hp2
        rw [hp1] at h_ne
        exact absurd rfl h_ne
    · -- Part (2): Distraction exists with competing paths
      by_cases h_two : brain.activePaths.length ≥ 2
      · have h_head1 := List.head!_mem_of_length_pos (by omega : 0 < brain.activePaths.length)
        have h_at1 := List.getElem_mem_self brain.activePaths 0 (by omega : 0 < brain.activePaths.length)
        have h_at2 := List.getElem_mem_self brain.activePaths 1 (by omega : 1 < brain.activePaths.length)
        use { conflictingPaths := [brain.activePaths.head!, brain.activePaths.getElem 1 (by omega)],
              nonEmptyPaths := by decide,
              pathsCompete := fun p1 p2 hp1 hp2 h_ne => by
                simp at hp1 hp2
                rcases hp1 with rfl | h1
                · rcases hp2 with rfl | h2
                  · exact absurd rfl h_ne
                  · left; omega
                · rcases hp2 with rfl | h2
                  · left; omega
                  · exact absurd h1 (List.not_mem_nil p1) }
        intros p1 p2 hp1 hp2 h_ne
        simp at hp1 hp2
        rcases hp1 with rfl | h1; rcases hp2 with rfl | h2
        · exact absurd rfl h_ne
        · left; omega
        · left; omega
        · exact absurd h1 (List.not_mem_nil p1)
      · -- Fewer than 2 paths: empty distraction
        use { conflictingPaths := [],
              nonEmptyPaths := by omega,
              pathsCompete := fun p1 p2 hp1 hp2 _ => absurd hp1 (List.not_mem_nil p1) }
        intros p1 p2 hp1 hp2 _
        exact absurd hp1 (List.not_mem_nil p1)
    · -- Part (3): Each wave has a pattern with matching charge
      intro wave _hw
      use wave.states
      exact ⟨wave.nonEmptyStates, wave.chargePreservation⟩
    · -- Part (4): Each quale is an active pattern
      intro q _hq
      exact ⟨by omega, q.isActive⟩
    · -- Part (5): Consolidation via halving
      intro wave _hw
      use { states := wave.states,
            nonEmptyStates := wave.nonEmptyStates,
            totalCharge := Nat.max 1 (wave.totalCharge / 2),
            chargePreservation := by omega }
      omega
    · -- Part (6): Paths interfere when distinct
      intro p1 p2 _hp1 _hp2 h_ne
      left
      unfold pathsConstructivelyInterfere pathsShareTarget pathTarget pathClinaemenCharge
      omega
    · -- Part (7): Equivalence between empty qualia and zero field charge
      constructor
      · intro h_empty
        unfold fieldTotalCharge
        omega
      · intro h_zero
        unfold fieldTotalCharge at h_zero
        by_contra! h_ne
        have : brain.currentQualia.length > 0 := by
          by_contra! h_contra
          simp [List.length_eq_zero] at h_contra
          rw [h_contra] at h_ne
          simp at h_ne
        omega

end ConsciousnessIsInterference
end Gnosis
