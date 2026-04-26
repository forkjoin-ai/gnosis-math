import Gnosis.Real

instance : Inhabited Float := ⟨0.0⟩

namespace Gnosis
namespace Articulatory

/-!
  # Articulatory Synthesis Core: The Fleshy Reality
-/

structure LarynxState where 
  pitch : Float
  pressure : Float
  tension : Float
  isVoiced : Bool

def defaultLarynx : LarynxState := { pitch := 110.0, pressure := 0.7, tension := 0.5, isVoiced := true }

structure PhasePoint where 
  pos : Float
  vel : Float := 0.0

structure ArticulatorState where
  tongueHeight : PhasePoint
  tongueBackness : PhasePoint
  lipRounding : PhasePoint
  lipClosure : PhasePoint
  velumOpening : PhasePoint

structure ArticulatorTarget where
  tongueHeight : Float
  tongueBackness : Float
  lipRounding : Float
  lipClosure : Float
  velumOpening : Float

structure KinematicParams where
  mass : BuleReal
  stiffness : BuleReal
  damping : BuleReal

structure BiomechanicalConfig where
  tongue : KinematicParams
  lips   : KinematicParams
  velum  : KinematicParams

def BuleReal.toFloat (r : BuleReal) : Float := (r.toFloat) / (Gnosis.BuleReal.scale.toFloat)

structure TrackEvent (α : Type) where
  value : α
  startTime : Float

structure GesturalScore where
  tongueHeight   : List (TrackEvent Float)
  tongueBackness : List (TrackEvent Float)
  lipRounding    : List (TrackEvent Float)
  lipClosure     : List (TrackEvent Float)
  velumOpening   : List (TrackEvent Float)
  larynx         : List (TrackEvent LarynxState)

structure Gesture where
  target : Float
  dominance : Float

structure PhonemeGestures where
  tongueHeight   : Gesture
  tongueBackness : Gesture
  lipRounding    : Gesture
  lipClosure     : Gesture
  velumOpening   : Gesture
  larynx         : LarynxState
  duration       : Float

inductive Phoneme where
  | P | B | T | D | K | G
  | M | N | NG
  | S | Z | SH | ZH | CH | JH | F | V | TH | DH | HH
  | IY | IH | EH | AE | AA | AH | AO | OW | UH | UW | OY | AY | AW | EY
  | ER | L | R | W | Y
  | SIL
  | Other

/-! # Phase 9: Intelligibility Gates & Syllabic Invariants -/

/-- 
  Intelligibility Gate:
  A segments is only 'Gate-Valid' if its articulatory target 
  possesses a holographic boundary trace that lands in the Amplituhedron.
-/
structure IntelligibilityGate where
  phoneme : Phoneme
  min_energy : Nat
  resonance_verified : Bool

/--
  The Schwa Invariant:
  During SIL (Silence), the tract must return to the neutral Schwa state (0,0).
-/
def isSchwa (s : ArticulatorState) : Prop :=
  s.tongueHeight.pos == 0.0 ∧ s.tongueBackness.pos == 0.0

/--
  Syllabic Nucleus:
  Identifies the high-energy core of a syllable. 
  Stress is modeled as a scaling factor on pressure and duration.
-/
structure Syllable where
  onset : List Phoneme
  nucleus : Phoneme -- The Vowel
  coda : List Phoneme
  is_stressed : Bool

def getStressScale (s : Syllable) : Nat :=
  if s.is_stressed then 150 else 100 -- 1.5x scaling factor

structure WaveguideState where
  oralF : Array Float
  oralB : Array Float
  apX : Array Float
  apY : Array Float
  lipMem : Float
  noseMem : Float
  velumIdx : Nat

end Articulatory
end Gnosis
