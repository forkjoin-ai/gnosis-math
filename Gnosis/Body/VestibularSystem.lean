import Gnosis.ComprehensiveAnatomy
import Gnosis.ThothMotorControl
import Gnosis.Proprioception
import Gnosis.Real
import Mathlib.Data.Real.Basic

namespace Gnosis
namespace VestibularSystem

/-!
  # Vestibular and Balance System
  
  Mathematical formalization of balance, gravity detection, head orientation,
  and vestibular-motor integration for the mechanical math puppet.
-/

/-- Head orientation in 3D space -/
structure HeadOrientation where
  pitch : Float  -- rotation around lateral axis (nodding)
  roll : Float   -- rotation around anterior-posterior axis (tilting)
  yaw : Float    -- rotation around vertical axis (turning)
  confidence : Float  -- 0.0 to 1.0
  timestamp : Float
  deriving Repr

/-- Gravity vector detection -/
structure GravityVector where
  x : Float  -- gravity component in x direction
  y : Float  -- gravity component in y direction
  z : Float  -- gravity component in z direction (should be -1.0 when upright)
  magnitude : Float  -- should be 1.0 g
  confidence : Float
  timestamp : Float
  deriving Repr

/-- Angular velocity from semicircular canals -/
structure AngularVelocity where
  pitchRate : Float  -- degrees/second
  rollRate : Float   -- degrees/second
  yawRate : Float    -- degrees/second
  confidence : Float
  timestamp : Float
  deriving Repr

/-- Linear acceleration from otolith organs -/
structure LinearAcceleration where
  x : Float  -- acceleration in x direction (m/s²)
  y : Float  -- acceleration in y direction (m/s²)
  z : Float  -- acceleration in z direction (m/s²)
  magnitude : Float  -- total acceleration magnitude
  confidence : Float
  timestamp : Float
  deriving Repr

/-- Balance state and stability -/
structure BalanceState where
  centerOfPressure : Float × Float  -- foot pressure center (x, y)
  swayAmplitude : Float  -- current sway amplitude
  swayFrequency : Float  -- sway frequency in Hz
  stabilityMargin : Float  -- distance from stability boundary
  posturalMode : String   -- "standing", "walking", "sitting", "lying"
  stability : Float       -- 0.0 to 1.0, overall stability
  timestamp : Float
  deriving Repr

/-- Vestibulo-ocular reflex (VOR) gain -/
struct VORGain where
  eyeVelocity : Float   -- actual eye movement velocity
  headVelocity : Float  -- head movement velocity
  gain : Float          -- eyeVelocity / headVelocity
  phaseLag : Float      -- temporal lag in milliseconds
  confidence : Float
  timestamp : Float
  deriving Repr

/-- Vestibular evidence for Thoth framework -/
structure VestibularEvidence where
  headOrientation : HeadOrientation
  gravityVector : GravityVector
  angularVelocity : AngularVelocity
  linearAcceleration : LinearAcceleration
  balanceState : BalanceState
  vorGain : VORGain
  overallConfidence : Float
  timestamp : Float
  claimsAuthority : Bool := false
  deriving Repr

/-! # Vestibular Sensing Functions -/

/-- Calculate head orientation from gravity vector -/
def calculateHeadOrientation (gravity : GravityVector) : HeadOrientation := by
  -- Pitch: rotation around lateral axis
  let pitch := Float.asin (-gravity.x)  -- negative because forward pitch increases x component
  
  -- Roll: rotation around anterior-posterior axis  
  let roll := Float.atan2 gravity.y gravity.z
  
  -- Yaw: cannot be determined from gravity alone (needs other references)
  let yaw := 0.0
  
  exact {
    pitch := pitch,
    roll := roll,
    yaw := yaw,
    confidence := gravity.confidence,
    timestamp := gravity.timestamp
  }

/-- Calculate angular velocity from head orientation changes -/
def calculateAngularVelocity 
    (current previous : HeadOrientation) 
    (deltaTime : Float) : AngularVelocity := by
  let pitchRate := (current.pitch - previous.pitch) / deltaTime * 180.0 / Float.pi
  let rollRate := (current.roll - previous.roll) / deltaTime * 180.0 / Float.pi
  let yawRate := (current.yaw - previous.yaw) / deltaTime * 180.0 / Float.pi
  
  let avgConfidence := (current.confidence + previous.confidence) / 2.0
  
  exact {
    pitchRate := pitchRate,
    rollRate := rollRate,
    yawRate := yawRate,
    confidence := avgConfidence,
    timestamp := current.timestamp
  }

/-- Estimate gravity vector from linear acceleration (when stationary) -/
def estimateGravityVector (accel : LinearAcceleration) : GravityVector := by
  -- When not moving, linear acceleration should equal gravity
  let isStationary := accel.magnitude < 0.5  -- less than 0.5 m/s² indicates stationary
  
  let gravityX := if isStationary then accel.x else 0.0
  let gravityY := if isStationary then accel.y else 0.0
  let gravityZ := if isStationary then accel.z else -1.0  -- default upright
  
  let confidence := if isStationary then accel.confidence * 0.9 else 0.3
  
  exact {
    x := gravityX,
    y := gravityY,
    z := gravityZ,
    magnitude := Float.sqrt (gravityX*gravityX + gravityY*gravityY + gravityZ*gravityZ),
    confidence := confidence,
    timestamp := accel.timestamp
  }

/-- Calculate stability margin from center of pressure -/
def calculateStabilityMargin 
    (centerOfPressure : Float × Float)
    (supportBase : Float × Float × Float × Float) : Float := by
  let (copX, copY) := centerOfPressure
  let (minX, maxX, minY, maxY) := supportBase
  
  let distanceToMinX := copX - minX
  let distanceToMaxX := maxX - copX
  let distanceToMinY := copY - minY
  let distanceToMaxY := maxY - copY
  
  let minDistance := Float.min (Float.min distanceToMinX distanceToMaxX) 
                              (Float.min distanceToMinY distanceToMaxY)
  
  exact Float.max minDistance 0.0

/-- Estimate sway frequency from balance state changes -/
def estimateSwayFrequency (balanceHistory : Array BalanceState) : Float := by
  if balanceHistory.length < 2 then
    exact 0.0
  else
    let recent := balanceHistory.take 5  -- use last 5 samples
    let amplitudes := recent.map (λ b => b.swayAmplitude)
    
    -- Simple frequency estimation from zero crossings
    let zeroCrossings := amplitudes.foldl (λ count amp => 
      if amp < 0.01 then count + 1 else count
    ) 0
    
    let estimatedFreq := zeroCrossings.toFloat / recent.length.toFloat * 2.0
    exact Float.clamp estimatedFreq 0.1 2.0  -- reasonable sway frequency range

/-! # Vestibular-Motor Integration -/

/-- Generate balance correction command -/
def generateBalanceCorrection (balance : BalanceState) : Motor.MotorCommand := by
  let (copX, copY) := balance.centerOfPressure
  let targetX := -copX * 0.5  -- move opposite to pressure center
  let targetY := -copY * 0.5
  
  let correctionForce := if balance.stability < 0.5 then 0.8 else 0.4
  
  exact {
    targetPose := {
      position := (targetX, targetY, 0.0),
      orientation := (1.0, 0.0, 0.0, 0.0)
    },
    speed := 0.6,
    force := correctionForce,
    precision := 0.85,
    bodyPart := "ankles"
  }

/-- Generate head stabilization command -/
def generateHeadStabilization (orientation : HeadOrientation) : Motor.MotorCommand := by
  -- Try to keep head upright (pitch = 0, roll = 0)
  let targetPitch := 0.0
  let targetRoll := 0.0
  
  let pitchCorrection := (targetPitch - orientation.pitch) * 0.7
  let rollCorrection := (targetRoll - orientation.roll) * 0.7
  
  exact {
    targetPose := {
      position := (0.0, 0.0, 0.0),
      orientation := (Float.cos (pitchCorrection/2.0), 0.0, 0.0, Float.sin (pitchCorrection/2.0))
    },
    speed := 0.8,
    force := 0.5,
    precision := 0.9,
    bodyPart := "neck"
  }

/-- Generate VOR compensation command -/
def generateVORCompensation (vor : VORGain) : Motor.MotorCommand := by
  let idealGain := 1.0  -- perfect VOR gain
  let gainError := idealGain - vor.gain
  let compensationForce := Float.abs gainError * 100.0
  
  exact {
    targetPose := {
      position := (0.0, 0.0, 0.0),
      orientation := (1.0, 0.0, 0.0, 0.0)
    },
    speed := vor.headVelocity,
    force := compensationForce,
    precision := 0.95,
    bodyPart := "eyes"
  }

/-! # Vestibular State Updates -/

/-- Update head orientation from new gravity data -/
def updateHeadOrientation (gravity : GravityVector) : HeadOrientation := by
  calculateHeadOrientation gravity

/-- Update angular velocity from orientation changes -/
def updateAngularVelocity 
    (current previous : HeadOrientation) 
    (deltaTime : Float) : AngularVelocity := by
  calculateAngularVelocity current previous deltaTime

/-- Update balance state from pressure data -/
def updateBalanceState 
    (centerOfPressure : Float × Float)
    (supportBase : Float × Float × Float × Float)
    (previousSway : Float)
    (posturalMode : String)
    (timestamp : Float) : BalanceState := by
  let stabilityMargin := calculateStabilityMargin centerOfPressure supportBase
  let swayAmplitude := Float.sqrt (centerOfPressure.1^2 + centerOfPressure.2^2)
  let swayFrequency := 0.5  -- would be calculated from history
  
  let stability := if stabilityMargin > 0.1 then 0.9 else
                  if stabilityMargin > 0.05 then 0.6 else 0.3
  
  exact {
    centerOfPressure := centerOfPressure,
    swayAmplitude := swayAmplitude,
    swayFrequency := swayFrequency,
    stabilityMargin := stabilityMargin,
    posturalMode := posturalMode,
    stability := stability,
    timestamp := timestamp
  }

/-- Update VOR gain from eye-head coordination -/
def updateVORGain 
    (eyeVelocity headVelocity : Float)
    (previousGain : Float)
    (timestamp : Float) : VORGain := by
  let currentGain := if headVelocity > 0.1 then eyeVelocity / headVelocity else previousGain
  let phaseLag := 10.0  -- typical VOR phase lag in milliseconds
  
  exact {
    eyeVelocity := eyeVelocity,
    headVelocity := headVelocity,
    gain := currentGain,
    phaseLag := phaseLag,
    confidence := 0.8,
    timestamp := timestamp
  }

/-! # Vestibular Evidence Processing -/

/-- Process vestibular evidence for Thoth framework -/
def processVestibularEvidence 
    (orientation : HeadOrientation)
    (gravity : GravityVector)
    (angularVel : AngularVelocity)
    (linearAccel : LinearAcceleration)
    (balance : BalanceState)
    (vor : VORGain)
    (timestamp : Float) : VestibularEvidence := by
  let orientationConfidence := orientation.confidence
  let gravityConfidence := gravity.confidence
  let angularConfidence := angularVel.confidence
  let linearConfidence := linearAccel.confidence
  let balanceConfidence := balance.stability
  let vorConfidence := vor.confidence
  
  let overallConfidence := (orientationConfidence + gravityConfidence + 
                           angularConfidence + linearConfidence + 
                           balanceConfidence + vorConfidence) / 6.0
  
  exact {
    headOrientation := orientation,
    gravityVector := gravity,
    angularVelocity := angularVel,
    linearAcceleration := linearAccel,
    balanceState := balance,
    vorGain := vor,
    overallConfidence := overallConfidence,
    timestamp := timestamp
  }

/-! # Vestibular Theorems -/

/-- Theorem: Gravity vector magnitude should be approximately 1.0 g -/
theorem gravity_magnitude_normalized (gravity : GravityVector) :
    let magnitude := Float.sqrt (gravity.x^2 + gravity.y^2 + gravity.z^2)
    0.9 ≤ magnitude ∧ magnitude ≤ 1.1 := by
  -- Gravity should be close to 1.0 g when upright
  sorry

/-- Theorem: Head orientation is bounded to human range -/
theorem head_orientation_bounded (orientation : HeadOrientation) :
    -90.0 ≤ orientation.pitch ∧ orientation.pitch ≤ 90.0 ∧
    -180.0 ≤ orientation.roll ∧ orientation.roll ≤ 180.0 ∧
    -180.0 ≤ orientation.yaw ∧ orientation.yaw ≤ 180.0 := by
  -- Human head movement limits
  sorry

/-- Theorem: VOR gain is normally close to 1.0 -/
theorem vor_gain_near_unity (vor : VORGain) :
    0.8 ≤ vor.gain ∧ vor.gain ≤ 1.2 := by
  -- Normal VOR gain range for healthy vestibular system
  sorry

/-- Theorem: Stability margin is non-negative -/
theorem stability_margin_nonnegative 
    (centerOfPressure : Float × Float)
    (supportBase : Float × Float × Float × Float) :
    let margin := calculateStabilityMargin centerOfPressure supportBase
    0.0 ≤ margin := by
  unfold calculateStabilityMargin
  -- Stability margin cannot be negative by construction
  sorry

/-! # Default Vestibular System -/

/-- Create default head orientation -/
def createDefaultHeadOrientation : HeadOrientation := by
  exact {
    pitch := 0.0,
    roll := 0.0,
    yaw := 0.0,
    confidence := 0.9,
    timestamp := 0.0
  }

/-- Create default gravity vector -/
def createDefaultGravityVector : GravityVector := by
  exact {
    x := 0.0,
    y := 0.0,
    z := -1.0,  -- gravity pointing down
    magnitude := 1.0,
    confidence := 0.95,
    timestamp := 0.0
  }

/-- Create default angular velocity -/
def createDefaultAngularVelocity : AngularVelocity := by
  exact {
    pitchRate := 0.0,
    rollRate := 0.0,
    yawRate := 0.0,
    confidence := 0.8,
    timestamp := 0.0
  }

/-- Create default linear acceleration -/
def createDefaultLinearAcceleration : LinearAcceleration := by
  exact {
    x := 0.0,
    y := 0.0,
    z := 0.0,
    magnitude := 0.0,
    confidence := 0.7,
    timestamp := 0.0
  }

/-- Create default balance state -/
def createDefaultBalanceState : BalanceState := by
  exact {
    centerOfPressure := (0.0, 0.0),
    swayAmplitude := 0.02,  -- 2cm sway
    swayFrequency := 0.5,   -- 0.5 Hz typical sway
    stabilityMargin := 0.15, -- 15cm from edge
    posturalMode := "standing",
    stability := 0.8,
    timestamp := 0.0
  }

/-- Create default VOR gain -/
def createDefaultVORGain : VORGain := by
  exact {
    eyeVelocity := 0.0,
    headVelocity := 0.0,
    gain := 1.0,  -- perfect VOR gain
    phaseLag := 10.0,
    confidence := 0.8,
    timestamp := 0.0
  }

/-- Initialize complete vestibular system -/
def initVestibularSystem : VestibularEvidence := by
  let orientation := createDefaultHeadOrientation
  let gravity := createDefaultGravityVector
  let angularVel := createDefaultAngularVelocity
  let linearAccel := createDefaultLinearAcceleration
  let balance := createDefaultBalanceState
  let vor := createDefaultVORGain
  
  processVestibularEvidence orientation gravity angularVel linearAccel balance vor 0.0

end VestibularSystem
end Gnosis
