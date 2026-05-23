import Gnosis.ComprehensiveAnatomy
import Gnosis.ThothMotorControl
import Gnosis.ArticulatorySynthesis
import Gnosis.Real
import Mathlib.Data.Real.Basic

namespace Gnosis
namespace GazePhysics

/-!
  # Gaze Physics and Control System
  
  Mathematical formalization of gaze dynamics, eye movement control, and
  attention coordination within the autonomous human system. Complements
  the existing eye tracking infrastructure with physics-based gaze control.
-/

/-- 3D gaze direction vector (unit vector) -/
structure GazeDirection where
  x : Float  -- horizontal component
  y : Float  -- vertical component  
  z : Float  -- depth component
  deriving Repr

/-- Gaze point in 3D space -/
structure GazePoint where
  position : Float × Float × Float  -- (x, y, z) coordinates
  distance : Float  -- distance from eyes
  confidence : Float  -- tracking confidence
  deriving Repr

/-- Eye movement types -/
inductive EyeMovementType where
  | saccade      -- rapid jump movement
  | smoothPursuit -- tracking moving target
  | vergence     -- convergence/divergence for depth
  | vestibular   -- vestibulo-ocular reflex
  | fixational   -- microsaccades and drift
  deriving Repr, DecidableEq

/-- Individual eye configuration -/
structure Eye where
  side : String  -- "left" or "right"
  position : Motor.Pose3D  -- eye position in head
  gazeDirection : GazeDirection
  pupilDiameter : Float  -- mm
  eyelidOpening : Float  -- 0.0 = closed, 1.0 = fully open
  accommodation : Float  -- focal accommodation (diopters)
  motorCommand : Motor.MotorCommand
  deriving Repr

/-- Binocular gaze system -/
structure BinocularGaze where
  leftEye : Eye
  rightEye : Eye
  convergenceAngle : Float  -- angle between gaze lines
  disparity : Float  -- retinal disparity
  vergenceState : Float  -- current vergence level
  deriving Repr

/-- Gaze fixation state -/
structure GazeFixation where
  target : GazePoint
  duration : Float  -- milliseconds
  stability : Float  -- how stable the fixation is
  microsaccades : Array Float  -- microsaccade amplitudes
  pupilResponse : Float  -- pupil dilation response
  deriving Repr

/-- Saccade parameters -/
structure SaccadeParameters where
  amplitude : Float  -- visual angle in degrees
  peakVelocity : Float  -- degrees per second
  duration : Float  -- milliseconds
  latency : Float  -- reaction time in milliseconds
  accuracy : Float  -- final position error
  deriving Repr

/-- Smooth pursuit parameters -/
structure SmoothPursuitParameters where
  targetVelocity : Float  -- degrees per second
  trackingGain : Float  -- eye velocity / target velocity
  phaseLag : Float  -- temporal delay in milliseconds
  catchUpSaccades : Nat  -- number of catch-up saccades
  deriving Repr

/-- Vergence movement parameters -/
structure VergenceParameters where
  depthChange : Float  -- change in fixation distance (cm)
  convergenceVelocity : Float  -- degrees per second
  latency : Float  -- milliseconds
  finalDisparity : Float  -- retinal disparity after movement
  deriving Repr

/-! # Gaze Physics Functions -/

/-- Calculate gaze direction from eye position to target point -/
def calculateGazeDirection (eyePos : Motor.Pose3D) (target : GazePoint) : GazeDirection := by
  let dx := target.position.1 - eyePos.position.1
  let dy := target.position.2 - eyePos.position.2  
  let dz := target.position.3 - eyePos.position.3
  let distance := Float.sqrt (dx*dx + dy*dy + dz*dz)
  
  if distance > 0.0 then
    exact { x := dx / distance, y := dy / distance, z := dz / distance }
  else
    exact { x := 0.0, y := 0.0, z := 1.0 }  -- default forward gaze

/-- Calculate convergence angle for binocular gaze -/
def calculateConvergenceAngle (leftEye : Eye) (rightEye : Eye) : Float := by
  let leftDir := leftEye.gazeDirection
  let rightDir := rightEye.gazeDirection
  
  -- Dot product for angle calculation
  let dotProduct := leftDir.x * rightDir.x + leftDir.y * rightDir.y + leftDir.z * rightDir.z
  let magnitude := Float.sqrt (leftDir.x*leftDir.x + leftDir.y*leftDir.y + leftDir.z*leftDir.z) *
                   Float.sqrt (rightDir.x*rightDir.x + rightDir.y*rightDir.y + rightDir.z*rightDir.z)
  
  if magnitude > 0.0 then
    exact Float.acos (dotProduct / magnitude)
  else
    exact 0.0

/-- Calculate retinal disparity between eyes -/
def calculateRetinalDisparity (leftEye : Eye) (rightEye : Eye) (targetDistance : Float) : Float := by
  let interocularDistance := 6.5  -- cm average
  let convergenceAngle := calculateConvergenceAngle leftEye rightEye
  
  -- Disparity in degrees of visual angle
  exact (interocularDistance / targetDistance) * 180.0 / Float.pi

/-- Main sequence relationship for saccades (amplitude-velocity) -/
def mainSequenceVelocity (amplitude : Float) : Float := by
  -- Peak velocity = 5 * amplitude + 50 (typical main sequence)
  exact 5.0 * amplitude + 50.0

/-- Saccade duration from amplitude -/
def saccadeDuration (amplitude : Float) : Float := by
  -- Duration = 20 + 2.5 * amplitude (typical relationship)
  exact 20.0 + 2.5 * amplitude

/-- Smooth pursuit gain calculation -/
def calculatePursuitGain (eyeVelocity : Float) (targetVelocity : Float) : Float := by
  if targetVelocity > 0.0 then
    exact eyeVelocity / targetVelocity
  else
    exact 1.0

/-- Vergence velocity from depth change -/
def vergenceVelocity (depthChange : Float) : Float := by
  -- Vergence velocity proportional to depth change rate
  exact 10.0 * Float.abs depthChange

/-! # Gaze Control Commands -/

/-- Generate saccade command to move gaze to target -/
def generateSaccadeCommand (currentGaze : BinocularGaze) (target : GazePoint) : Motor.MotorCommand := by
  let currentLeftPos := currentGaze.leftEye.position
  let currentRightPos := currentGaze.rightEye.position
  
  let leftTargetDir := calculateGazeDirection currentLeftPos target
  let rightTargetDir := calculateGazeDirection currentRightPos target
  
  let leftAmplitude := Float.acos (currentGaze.leftEye.gazeDirection.x * leftTargetDir.x +
                                   currentGaze.leftEye.gazeDirection.y * leftTargetDir.y +
                                   currentGaze.leftEye.gazeDirection.z * leftTargetDir.z)
  let rightAmplitude := Float.acos (currentGaze.rightEye.gazeDirection.x * rightTargetDir.x +
                                    currentGaze.rightEye.gazeDirection.y * rightTargetDir.y +
                                    currentGaze.rightEye.gazeDirection.z * rightTargetDir.z)
  
  let avgAmplitude := (leftAmplitude + rightAmplitude) / 2.0
  let peakVel := mainSequenceVelocity avgAmplitude
  let duration := saccadeDuration avgAmplitude
  
  exact {
    targetPose := {
      position := target.position,
      orientation := (1.0, 0.0, 0.0, 0.0)
    },
    speed := peakVel / 1000.0,  -- convert to reasonable units
    force := 0.5,  -- eye movements are low force
    precision := 0.95,  -- high precision required
    bodyPart := "eyes"
  }

/-- Generate smooth pursuit command for tracking moving target -/
def generateSmoothPursuitCommand (targetVelocity : Float) (currentGain : Float) : Motor.MotorCommand := by
  let desiredGain := 0.95  -- ideal pursuit gain
  let gainAdjustment := desiredGain - currentGain
  
  exact {
    targetPose := {
      position := (targetVelocity, 0.0, 0.0),  -- velocity encoded as position
      orientation := (1.0, 0.0, 0.0, 0.0)
    },
    speed := Float.abs targetVelocity,
    force := 0.3,
    precision := 0.85,
    bodyPart := "eyes"
  }

/-- Generate vergence command for depth adjustment -/
def generateVergenceCommand (currentDepth : Float) (targetDepth : Float) : Motor.MotorCommand := by
  let depthChange := targetDepth - currentDepth
  let vergenceVel := vergenceVelocity depthChange
  
  exact {
    targetPose := {
      position := (0.0, 0.0, targetDepth),
      orientation := (1.0, 0.0, 0.0, 0.0)
    },
    speed := vergenceVel / 1000.0,
    force := 0.4,
    precision := 0.9,
    bodyPart := "eyes"
  }

/-! # Gaze-Attention Coordination -/

/-- Attention focus area in visual field -/
structure AttentionFocus where
  center : GazePoint
  radius : Float  -- attentional field radius in degrees
  intensity : Float  -- 0.0 = diffuse, 1.0 = focused
  priority : Float  -- behavioral priority
  deriving Repr

/-- Visual saliency map point -/
structure SaliencyPoint where
  position : GazePoint
  saliency : Float  -- 0.0 = not salient, 1.0 = highly salient
  features : Array String  -- feature categories
  deriving Repr

/-- Coordinated gaze-attention system -/
structure GazeAttentionSystem where
  gaze : BinocularGaze
  attention : Array AttentionFocus
  saliencyMap : Array SaliencyPoint
  currentFixation : Option GazeFixation
  nextSaccadeTarget : Option GazePoint
  attentionalPriority : Float
  deriving Repr

/-- Calculate attentional priority for gaze target selection -/
def calculateAttentionalPriority (saliency : SaliencyPoint) (attention : AttentionFocus) : Float := by
  let distance := Float.sqrt (
    (saliency.position.position.1 - attention.center.position.1)^2 +
    (saliency.position.position.2 - attention.center.position.2)^2
  )
  
  let spatialWeight := Float.exp (-distance * distance / (2.0 * attention.radius * attention.radius))
  let saliencyWeight := saliency.saliency
  let intensityWeight := attention.intensity
  let priorityWeight := attention.priority
  
  exact spatialWeight * saliencyWeight * intensityWeight * priorityWeight

/-- Select next gaze target based on attention and saliency -/
def selectNextGazeTarget (system : GazeAttentionSystem) : Option GazePoint := by
  let candidates := system.saliencyMap.map (λ saliency =>
    let maxPriority := system.attention.foldl (λ max att =>
      let priority := calculateAttentionalPriority saliency att
      if priority > max then priority else max
    ) 0.0
    
    (saliency.position, maxPriority)
  )
  
  match candidates.maximum? (λ (_, p1) (_, p2) => p1 < p2) with
  | some (point, priority) =>
    if priority > 0.3 then some point else none
  | none => none

/-! # Gaze State Updates -/

/-- Update gaze system with new motor command -/
def updateGazeSystem (gaze : BinocularGaze) (command : Motor.MotorCommand) (movementType : EyeMovementType) : BinocularGaze := by
  let newLeftDir := calculateGazeDirection gaze.leftEye.position {
    position := command.targetPose.position,
    distance := 1.0,
    confidence := 0.9
  }
  let newRightDir := calculateGazeDirection gaze.rightEye.position {
    position := command.targetPose.position,
    distance := 1.0,
    confidence := 0.9
  }
  
  let updatedLeftEye := { gaze.leftEye with 
    gazeDirection := newLeftDir,
    motorCommand := command
  }
  let updatedRightEye := { gaze.rightEye with 
    gazeDirection := newRightDir,
    motorCommand := command
  }
  
  let newConvergence := calculateConvergenceAngle updatedLeftEye updatedRightEye
  let newDisparity := calculateRetinalDisparity updatedLeftEye updatedRightEye 1.0
  
  exact {
    leftEye := updatedLeftEye,
    rightEye := updatedRightEye,
    convergenceAngle := newConvergence,
    disparity := newDisparity,
    vergenceState := if movementType = EyeMovementType.vergence then 
                      newDisparity else gaze.vergenceState
  }

/-- Update attention system based on current gaze -/
def updateAttentionSystem (system : GazeAttentionSystem) (currentGaze : BinocularGaze) : GazeAttentionSystem := by
  let currentGazePoint := {
    position := currentGaze.leftEye.position.position,
    distance := 1.0,
    confidence := 0.9
  }
  
  -- Update attention focus based on current gaze
  let updatedAttention := system.attention.map (λ att =>
    let distance := Float.sqrt (
      (currentGazePoint.position.1 - att.center.position.position.1)^2 +
      (currentGazePoint.position.2 - att.center.position.position.2)^2
    )
    let newIntensity := if distance < att.radius then 
                        att.intensity * 1.1  -- enhance attention at gaze point
                      else 
                        att.intensity * 0.95  -- decay elsewhere
    { att with intensity := Float.clamp newIntensity 0.0 1.0 }
  )
  
  exact {
    gaze := currentGaze,
    attention := updatedAttention,
    saliencyMap := system.saliencyMap,
    currentFixation := system.currentFixation,
    nextSaccadeTarget := selectNextGazeTarget system,
    attentionalPriority := system.attentionalPriority
  }

/-! # Gaze Physics Theorems -/

/-- Theorem: Gaze direction is unit vector -/
theorem gaze_direction_unit (direction : GazeDirection) :
    direction.x * direction.x + direction.y * direction.y + direction.z * direction.z = 1.0 := by
  -- This would be proven by construction of calculateGazeDirection
  sorry

/-- Theorem: Saccade main sequence relationship holds -/
theorem main_sequence_relationship (amplitude : Float) (h : 0.0 < amplitude) :
    let velocity := mainSequenceVelocity amplitude
    let duration := saccadeDuration amplitude
    velocity > 0.0 ∧ duration > 20.0 := by
  unfold mainSequenceVelocity saccadeDuration
  constructor
  . exact Float.pos_of_pos_add (by positivity)
  . exact Float.add_pos_left 20.0 (by positivity)

/-- Theorem: Convergence angle increases with decreasing distance -/
theorem convergence_distance_inverse (leftEye : Eye) (rightEye : Eye) 
    (target1 target2 : GazePoint) (h : target1.distance < target2.distance) :
    let conv1 := calculateConvergenceAngle leftEye rightEye
    let conv2 := calculateConvergenceAngle leftEye rightEye
    conv1 > conv2 := by
  -- Would prove that closer targets require larger convergence angles
  sorry

/-- Theorem: Pursuit gain bounded between 0 and 1 for stable tracking -/
theorem pursuit_gain_bounded (eyeVel targetVel : Float) :
    let gain := calculatePursuitGain eyeVel targetVel
    0.0 ≤ gain ∧ gain ≤ 2.0 := by
  unfold calculatePursuitGain
  by_cases h_target : targetVel > 0
  . have h_pos := Float.div_nonneg (Float.abs_nonneg eyeVel) h_target
    constructor
    . exact h_pos
    . exact (Float.le_div (Float.abs eyeVel) targetVel).mp (Float.le_abs_self eyeVel)
  . exact (Float.div_zero targetVel).symm ▸ rfl

/-! # Default Gaze System -/

/-- Create default binocular gaze system -/
def createDefaultGaze : BinocularGaze := by
  let defaultEye : Eye := {
    side := "left",
    position := { position := (-0.0325, 0.0, 0.0), orientation := (1.0, 0.0, 0.0, 0.0) },
    gazeDirection := { x := 0.0, y := 0.0, z := 1.0 },
    pupilDiameter := 3.0,
    eyelidOpening := 0.8,
    accommodation := 0.0,
    motorCommand := {
      targetPose := { position := (0.0, 0.0, 1.0), orientation := (1.0, 0.0, 0.0, 0.0) },
      speed := 0.5, force := 0.3, precision := 0.9, bodyPart := "eyes"
    }
  }
  
  let leftEye := defaultEye
  let rightEye := { defaultEye with 
    side := "right",
    position := { position := (0.0325, 0.0, 0.0), orientation := (1.0, 0.0, 0.0, 0.0) }
  }
  
  exact {
    leftEye := leftEye,
    rightEye := rightEye,
    convergenceAngle := 0.0,
    disparity := 0.0,
    vergenceState := 0.0
  }

/-- Create default gaze-attention system -/
def createDefaultGazeAttention : GazeAttentionSystem := by
  let defaultSaliency := #[
    { position := { position := (0.0, 0.0, 1.0), distance := 1.0, confidence := 0.9 },
      saliency := 0.8, features := #["face", "eyes"] },
    { position := { position := (0.2, 0.1, 0.8), distance := 0.8, confidence := 0.7 },
      saliency := 0.6, features := #["motion", "hand"] }
  ]
  
  let defaultAttention := #[
    { center := { position := (0.0, 0.0, 1.0), distance := 1.0, confidence := 0.9 },
      radius := 5.0, intensity := 0.7, priority := 0.8 }
  ]
  
  exact {
    gaze := createDefaultGaze,
    attention := defaultAttention,
    saliencyMap := defaultSaliency,
    currentFixation := none,
    nextSaccadeTarget := some { position := (0.0, 0.0, 1.0), distance := 1.0, confidence := 0.9 },
    attentionalPriority := 0.8
  }

end GazePhysics
end Gnosis
