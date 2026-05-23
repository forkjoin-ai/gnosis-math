import Gnosis.ComprehensiveAnatomy
import Gnosis.ThothMotorControl
import Gnosis.GazePhysics
import Gnosis.Real
import Mathlib.Data.Real.Basic

namespace Gnosis
namespace HearingPhysics

/-!
  # Hearing Physics and Auditory Processing
  
  Mathematical formalization of hearing physics, sound source localization,
  and auditory attention within the autonomous human system.
-/

/-- Sound wave properties -/
structure SoundWave where
  frequency : Float  -- Hz
  amplitude : Float  -- 0.0 to 1.0
  phase : Float      -- radians
  duration : Float   -- seconds
  deriving Repr

/-- Sound source in 3D space -/
structure SoundSource where
  position : Float × Float × Float  -- (x, y, z) coordinates
  velocity : Float × Float × Float  -- movement velocity
  intensity : Float  -- sound intensity level
  frequency : Float  -- dominant frequency
  directionality : Float  -- 0.0 = omnidirectional, 1.0 = highly directional
  deriving Repr

/-- Auditory canal and middle ear properties -/
structure AuditorySystem where
  earSide : String  -- "left" or "right"
  earPosition : Motor.Pose3D  -- ear position on head
  canalLength : Float  -- cm, typically 2.5 cm
  eardrumArea : Float  -- cm², typically 0.65 cm²
  ossicleAmplification : Float  -- typically 22x amplification
  cochlearFrequencyRange : (Float × Float)  -- (20 Hz, 20 kHz)
  currentImpedance : Float  -- acoustic impedance
  deriving Repr

/-- Binaural hearing system -/
structure BinauralHearing where
  leftEar : AuditorySystem
  rightEar : AuditorySystem
  interauralDistance : Float  -- cm, typically 17-18 cm
  headRelatedTransferFunction : Array Float  -- HRTF coefficients
  binauralSensitivity : Float  -- 0.0 to 1.0
  deriving Repr

/-- Interaural time difference (ITD) -/
structure InterauralTimeDifference where
  timeDiff : Float  -- microseconds
  confidence : Float  -- 0.0 to 1.0
  frequencyBand : Float  -- Hz band for calculation
  deriving Repr

/-- Interaural level difference (ILD) -/
structure InterauralLevelDifference where
  levelDiff : Float  -- dB
  confidence : Float  -- 0.0 to 1.0
  frequencyBand : Float  -- Hz band for calculation
  deriving Repr

/-- Sound localization estimate -/
struct SoundLocalization where
  azimuth : Float  -- degrees, -180 to 180
  elevation : Float  -- degrees, -90 to 90
  distance : Float  -- meters
  confidence : Float  -- 0.0 to 1.0
  method : String  -- "ITD", "ILD", "HRTF", "spectrum"
  deriving Repr

/-- Auditory attention focus -/
structure AuditoryAttention where
  focusSource : Option SoundSource
  focusRegion : (Float × Float × Float)  -- spatial region bounds
  attentionalGain : Float  -- 0.0 to 1.0
  suppressionLevel : Float  -- 0.0 to 1.0 for competing sources
  priority : Float  -- behavioral priority
  deriving Repr

/-- Auditory scene analysis -/
structure AuditoryScene where
  soundSources : Array SoundSource
  activeStreams : Array Nat  -- indices of attended streams
  backgroundNoise : Float  -- noise level
  cocktailPartyEffect : Float  -- ability to separate sources
  spatialAwareness : Float  -- overall spatial audio awareness
  deriving Repr

/-! # Hearing Physics Functions -/

/-- Calculate sound pressure level at distance from source -/
def calculateSoundPressureLevel (source : SoundSource) (distance : Float) : Float := by
  -- Inverse square law: SPL decreases with distance squared
  if distance > 0.1 then  -- avoid division by very small numbers
    exact source.intensity - 20.0 * Float.log10 (distance / 0.1)
  else
    exact source.intensity  -- at source distance

/-- Calculate interaural time difference for sound source -/
def calculateITD (binaural : BinauralHearing) (source : SoundSource) : InterauralTimeDifference := by
  let leftEarPos := binaural.leftEar.earPosition.position
  let rightEarPos := binaural.rightEar.earPosition.position
  let sourcePos := source.position
  
  let leftDistance := Float.sqrt (
    (sourcePos.1 - leftEarPos.1)^2 + (sourcePos.2 - leftEarPos.2)^2 + (sourcePos.3 - leftEarPos.3)^2
  )
  let rightDistance := Float.sqrt (
    (sourcePos.1 - rightEarPos.1)^2 + (sourcePos.2 - rightEarPos.2)^2 + (sourcePos.3 - rightEarPos.3)^2
  )
  
  let distanceDiff := leftDistance - rightDistance
  let timeDiff := distanceDiff / 343.0 * 1000000.0  -- convert to microseconds (speed of sound = 343 m/s)
  
  let confidence := if Float.abs distanceDiff > 0.001 then 0.9 else 0.3
  
  exact {
    timeDiff := timeDiff,
    confidence := confidence,
    frequencyBand := 1000.0  -- 1 kHz reference
  }

/-- Calculate interaural level difference for sound source -/
def calculateILD (binaural : BinauralHearing) (source : SoundSource) : InterauralLevelDifference := by
  let leftEarPos := binaural.leftEar.earPosition.position
  let rightEarPos := binaural.rightEar.earPosition.position
  
  let leftDistance := Float.sqrt (
    (sourcePos.1 - leftEarPos.1)^2 + (sourcePos.2 - leftEarPos.2)^2 + (sourcePos.3 - leftEarPos.3)^2
  )
  let rightDistance := Float.sqrt (
    (sourcePos.1 - rightEarPos.1)^2 + (sourcePos.2 - rightEarPos.2)^2 + (sourcePos.3 - rightEarPos.3)^2
  )
  
  let leftSPL := calculateSoundPressureLevel source leftDistance
  let rightSPL := calculateSoundPressureLevel source rightDistance
  let levelDiff := leftSPL - rightSPL
  
  let confidence := if Float.abs levelDiff > 1.0 then 0.8 else 0.4
  
  exact {
    levelDiff := levelDiff,
    confidence := confidence,
    frequencyBand := source.frequency
  }

/-- Localize sound source using ITD and ILD -/
def localizeSoundSource (binaural : BinauralHearing) (source : SoundSource) : SoundLocalization := by
  let itd := calculateITD binaural source
  let ild := calculateILD binaural source
  
  -- Convert ITD to azimuth (simplified Woodworth model)
  let azimuth := if Float.abs itd.timeDiff < 700.0 then  -- max ITD for humans
    Float.asin (itd.timeDiff / 700.0 * Float.pi / 2.0) * 180.0 / Float.pi
  else
    if itd.timeDiff > 0 then 90.0 else -90.0
  
  -- Estimate distance from intensity
  let estimatedDistance := if source.intensity > 30.0 then
    Float.pow 10.0 ((80.0 - source.intensity) / 20.0)  -- inverse of SPL calculation
  else
    10.0  -- default far distance
  
  -- Combine confidence measures
  let combinedConfidence := (itd.confidence + ild.confidence) / 2.0
  
  exact {
    azimuth := azimuth,
    elevation := 0.0,  -- simplified, would need vertical ITD/ILD
    distance := estimatedDistance,
    confidence := combinedConfidence,
    method := "ITD_ILD"
  }

/-- Calculate cocktail party effect (source separation) -/
def calculateCocktailPartyEffect (scene : AuditoryScene) (targetIndex : Nat) : Float := by
  if targetIndex < scene.soundSources.length then
    let target := scene.soundSources[targetIndex]!
    let competingSources := scene.soundSources.filter (λ (i, s) => i ≠ targetIndex)
    
    -- Calculate signal-to-noise ratio for target source
    let targetLevel := target.intensity
    let noiseLevel := competingSources.foldl (λ sum (_, s) => sum + s.intensity) 0.0
    
    let snr := if noiseLevel > 0.0 then targetLevel - noiseLevel else 60.0
    
    -- Cocktail party effect improves with higher SNR
    exact Float.clamp (snr / 60.0) 0.0 1.0
  else
    exact 0.0

/-- Apply auditory attention gain to sound source -/
def applyAuditoryAttention (attention : AuditoryAttention) (source : SoundSource) : SoundSource := by
  match attention.focusSource with
  | some focusSource =>
    let distance := Float.sqrt (
      (source.position.1 - focusSource.position.1)^2 +
      (source.position.2 - focusSource.position.2)^2 +
      (source.position.3 - focusSource.position.3)^2
    )
    
    let spatialGain := if distance < 1.0 then
      attention.attentionalGain * (1.0 - distance / 1.0)
    else
      0.0
    
    { source with intensity := source.intensity * (1.0 + spatialGain) }
  | none =>
    let (minX, maxX, minY, maxY, minZ, maxZ) := attention.focusRegion
    let inRegion := minX ≤ source.position.1 ∧ source.position.1 ≤ maxX ∧
                   minY ≤ source.position.2 ∧ source.position.2 ≤ maxY ∧
                   minZ ≤ source.position.3 ∧ source.position.3 ≤ maxZ
    
    let regionGain := if inRegion then attention.attentionalGain else 0.0
    { source with intensity := source.intensity * (1.0 + regionGain) }

/-! # Auditory Motor Commands -/

/-- Generate head turn command for sound source localization -/
def generateHeadTurnCommand (currentPose : Motor.Pose3D) (targetSound : SoundSource) : Motor.MotorCommand := by
  let headPosition := currentPose.position
  let soundDirection := {
    x := targetSound.position.1 - headPosition.1,
    y := targetSound.position.2 - headPosition.2,
    z := targetSound.position.3 - headPosition.3
  }
  
  let distance := Float.sqrt (soundDirection.x^2 + soundDirection.y^2 + soundDirection.z^2)
  let normalizedDir := if distance > 0.0 then
    { soundDirection with 
      x := soundDirection.x / distance,
      y := soundDirection.y / distance,
      z := soundDirection.z / distance
    }
  else
    { soundDirection with x := 0.0, y := 0.0, z := 1.0 }
  
  -- Calculate yaw angle for head turn
  let targetYaw := Float.atan2 normalizedDir.y normalizedDir.x
  
  exact {
    targetPose := {
      position := currentPose.position,
      orientation := (Float.cos (targetYaw/2.0), 0.0, 0.0, Float.sin (targetYaw/2.0))
    },
    speed := 1.0,  -- moderate head turn speed
    force := 0.8,
    precision := 0.7,
    bodyPart := "head"
  }

/-- Generate ear movement command (for species with mobile ears) -/
def generateEarMovementCommand (earSide : String) (targetSound : SoundSource) : Motor.MotorCommand := by
  let earPosition := if earSide = "left" then (-0.08, 0.0, 0.0) else (0.08, 0.0, 0.0)
  let soundDirection := {
    x := targetSound.position.1 - earPosition.1,
    y := targetSound.position.2 - earPosition.2,
    z := targetSound.position.3 - earPosition.3
  }
  
  let azimuth := Float.atan2 soundDirection.y soundDirection.x
  
  exact {
    targetPose := {
      position := earPosition,
      orientation := (Float.cos (azimuth/2.0), 0.0, 0.0, Float.sin (azimuth/2.0))
    },
    speed := 2.0,  -- ear movements are fast
    force := 0.3,
    precision := 0.8,
    bodyPart := s!"{earSide}Ear"
  }

/-! # Auditory Scene Analysis -/

/-- Update auditory scene with new sound source -/
def updateAuditoryScene (scene : AuditoryScene) (newSource : SoundSource) : AuditoryScene := by
  let updatedSources := scene.soundSources.push newSource
  
  -- Update cocktail party effect
  let newCocktailParty := calculateCocktailPartyEffect { scene with soundSources := updatedSources } 0
  
  -- Update spatial awareness
  let sourceCount := updatedSources.length.toFloat
  let newSpatialAwareness := Float.clamp (sourceCount / 10.0) 0.0 1.0
  
  exact {
    soundSources := updatedSources,
    activeStreams := scene.activeStreams,
    backgroundNoise := scene.backgroundNoise,
    cocktailPartyEffect := newCocktailParty,
    spatialAwareness := newSpatialAwareness
  }

/-- Select auditory attention target based on priority and salience -/
def selectAuditoryAttentionTarget (scene : AuditoryScene) (attention : AuditoryAttention) : Option SoundSource := by
  let scoredSources := scene.soundSources.map (λ (i, source) =>
    let distance := match attention.focusSource with
      | some focus => Float.sqrt (
        (source.position.1 - focus.position.1)^2 +
        (source.position.2 - focus.position.2)^2 +
        (source.position.3 - focus.position.3)^2
      )
      | none => 1.0  -- default distance
    
    let spatialScore := Float.exp (-distance / 2.0)
    let intensityScore := source.intensity / 100.0  -- normalize intensity
    let priorityScore := attention.priority
    
    let totalScore := spatialScore * intensityScore * priorityScore
    (i, source, totalScore)
  )
  
  match scoredSources.maximum? (λ (_, _, s1) (_, _, s2) => s1 < s2) with
  | some (idx, source, score) =>
    if score > 0.3 then some source else none
  | none => none

/-! # Hearing Physics Theorems -/

/-- Theorem: Sound pressure level follows inverse square law -/
theorem sound_pressure_inverse_square (source : SoundSource) (d1 d2 : Float) (h : 0.1 < d1 ∧ 0.1 < d2 ∧ d1 < d2) :
    let spl1 := calculateSoundPressureLevel source d1
    let spl2 := calculateSoundPressureLevel source d2
    spl1 > spl2 := by
  unfold calculateSoundPressureLevel
  have h_d1_pos := h.left
  have h_d2_pos := h.right.left
  have h_d1_lt_d2 := h.right.right
  -- Since distance increases, SPL decreases
  sorry

/-- Theorem: ITD is bounded by maximum interaural distance -/
theorem itd_bounded (binaural : BinauralHearing) (source : SoundSource) :
    let itd := calculateITD binaural source
    -700.0 ≤ itd.timeDiff ∧ itd.timeDiff ≤ 700.0 := by
  unfold calculateITD
  -- Maximum ITD occurs when source is directly to one side
  sorry

/-- Theorem: ILD increases with source azimuth -/
theorem ild_azimuth_monotonic (binaural : BinauralHearing) (azimuth1 azimuth2 : Float) 
    (h : -90.0 ≤ azimuth1 ∧ azimuth1 ≤ azimuth2 ∧ azimuth2 ≤ 90.0) :
    let source1 := { position := (Float.sin azimuth1 * 2.0, 0.0, Float.cos azimuth1 * 2.0),
                    velocity := (0.0, 0.0, 0.0), intensity := 60.0, frequency := 1000.0, directionality := 0.0 }
    let source2 := { position := (Float.sin azimuth2 * 2.0, 0.0, Float.cos azimuth2 * 2.0),
                    velocity := (0.0, 0.0, 0.0), intensity := 60.0, frequency := 1000.0, directionality := 0.0 }
    let ild1 := calculateILD binaural source1
    let ild2 := calculateILD binaural source2
    Float.abs ild1.levelDiff ≤ Float.abs ild2.levelDiff := by
  -- ILD should increase as source moves further from center
  sorry

/-- Theorem: Cocktail party effect improves with source separation -/
theorem cocktail_party_separation (scene1 scene2 : AuditoryScene) 
    (h : scene1.soundSources.length = scene2.soundSources.length ∧
          ∀ i, scene1.soundSources[i]!.position ≠ scene2.soundSources[i]!.position) :
    let cp1 := calculateCocktailPartyEffect scene1 0
    let cp2 := calculateCocktailPartyEffect scene2 0
    cp2 ≥ cp1 := by
  -- Better spatial separation should improve cocktail party effect
  sorry

/-! # Default Hearing System -/

/-- Create default auditory system -/
def createDefaultAuditorySystem : BinauralHearing := by
  let defaultEar : AuditorySystem := {
    earSide := "left",
    earPosition := { position := (-0.085, 0.0, 0.0), orientation := (1.0, 0.0, 0.0, 0.0) },
    canalLength := 2.5,
    eardrumArea := 0.65,
    ossicleAmplification := 22.0,
    cochlearFrequencyRange := (20.0, 20000.0),
    currentImpedance := 1.0
  }
  
  let leftEar := defaultEar
  let rightEar := { defaultEar with 
    earSide := "right",
    earPosition := { position := (0.085, 0.0, 0.0), orientation := (1.0, 0.0, 0.0, 0.0) }
  }
  
  let hrtfCoefficients := Array.range 25 |> Array.map (λ i => 
    Float.sin (i.toFloat * Float.pi / 12.5) * 0.8  -- simplified HRTF
  )
  
  exact {
    leftEar := leftEar,
    rightEar := rightEar,
    interauralDistance := 17.0,
    headRelatedTransferFunction := hrtfCoefficients,
    binauralSensitivity := 0.9
  }

/-- Create default auditory scene -/
def createDefaultAuditoryScene : AuditoryScene := by
  let defaultSources := #[
    { position := (1.0, 0.0, 0.0), velocity := (0.0, 0.0, 0.0), 
      intensity := 60.0, frequency := 440.0, directionality := 0.5 },
    { position := (-0.5, 0.5, 0.2), velocity := (0.0, 0.0, 0.0), 
      intensity := 50.0, frequency := 880.0, directionality := 0.3 }
  ]
  
  exact {
    soundSources := defaultSources,
    activeStreams := #[0],
    backgroundNoise := 30.0,
    cocktailPartyEffect := 0.7,
    spatialAwareness := 0.6
  }

/-- Create default auditory attention -/
def createDefaultAuditoryAttention : AuditoryAttention := by
  exact {
    focusSource := none,
    focusRegion := (-2.0, 2.0, -2.0, 2.0, -1.0, 3.0),  -- reasonable spatial bounds
    attentionalGain := 0.8,
    suppressionLevel := 0.3,
    priority := 0.7
  }

end HearingPhysics
end Gnosis
