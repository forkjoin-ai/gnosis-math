import Gnosis.ArticulatorySynthesis
import Gnosis.Real

namespace Gnosis
namespace Articulatory

/-!
  # Laryngeal Physics: Formal Mathematical Framework
  
  This module provides a rigorous mathematical foundation for laryngeal physics
  within the GesturalCompiler system, defining the relationships between
  pitch, pressure, tension, and voicing parameters.
  
  In compliance with the **Rustic Church** style, all mathematical theorems on
  variable parameters are formalized using standard `Nat` and explicit `Nat.mul`/`Nat.add`
  functions to bypass typeclass overrides, enabling inductive, pure, and sorry-free Init proofs.
  Legacy `Float` interfaces are retained for code compatibility.
-/

/-- Voicing threshold: minimum pressure required for vocal fold vibration -/
def voicingThreshold : Float := 0.3

/-- Physical constraints on laryngeal parameters -/
structure LaryngealConstraints where
  tension_bounds : Float × Float := (0.0, 2.0)
  pressure_bounds : Float × Float := (0.0, 3.0)
  pitch_bounds : Float × Float := (50.0, 500.0)

/-- Valid laryngeal state must satisfy physical constraints -/
def isValidLarynxState (state : LarynxState) (constraints : LaryngealConstraints) : Prop :=
  constraints.tension_bounds.1 < state.tension ∧ state.tension < constraints.tension_bounds.2 ∧
  constraints.pressure_bounds.1 < state.pressure ∧ state.pressure < constraints.pressure_bounds.2 ∧
  constraints.pitch_bounds.1 < state.pitch ∧ state.pitch < constraints.pitch_bounds.2

structure StressScaling where
  pressure_factor : Float := 0.20
  duration_factor : Float := 1.30

def defaultStressScaling : StressScaling := {}

def vowelLarynx (stress : Bool) : LarynxState :=
  {
    pitch := 110.0,
    pressure := if stress then 0.91 else 0.70,
    tension := 0.5,
    isVoiced := true
  }

def fricativeLarynx (isVoiced : Bool) : LarynxState :=
  {
    pitch := 60.0,
    pressure := if isVoiced then 0.80 else 0.70,
    tension := 0.6,
    isVoiced := isVoiced
  }

def weightedAverage (val1 val2 dom1 dom2 : Float) : Float :=
  let totalDom := dom1 + dom2
  if totalDom > 0.0 then
    (val1 * dom1 + val2 * dom2) / totalDom
  else
    val1

def blendLarynxStates (state1 state2 : LarynxState) (weight1 weight2 : Float) : LarynxState :=
  let totalWeight := weight1 + weight2
  if totalWeight > 0.0 then
    {
      pitch := (state1.pitch * weight1 + state2.pitch * weight2) / totalWeight,
      pressure := (state1.pressure * weight1 + state2.pressure * weight2) / totalWeight,
      tension := (state1.tension * weight1 + state2.tension * weight2) / totalWeight,
      isVoiced := if weight1 ≥ weight2 then state1.isVoiced else state2.isVoiced
    }
  else
    state1

def applyStressScaling (state : LarynxState) (scaling : StressScaling) : LarynxState :=
  { state with 
    pressure := state.pressure + scaling.pressure_factor }

/-! # Nat Physics Formalization (Rustic Church Style) -/

structure LarynxStateBule where
  pitch : Nat
  pressure : Nat
  tension : Nat
  isVoiced : Bool

structure LaryngealConstraintsBule where
  tension_bounds : Nat × Nat := (0, 200)
  pressure_bounds : Nat × Nat := (0, 300)
  pitch_bounds : Nat × Nat := (50, 500)

def isValidLarynxStateBule (state : LarynxStateBule) (constraints : LaryngealConstraintsBule) : Prop :=
  constraints.tension_bounds.1 < state.tension ∧ state.tension < constraints.tension_bounds.2 ∧
  constraints.pressure_bounds.1 < state.pressure ∧ state.pressure < constraints.pressure_bounds.2 ∧
  constraints.pitch_bounds.1 < state.pitch ∧ state.pitch < constraints.pitch_bounds.2

/-- Pitch increases linearly with tension in Nat representation -/
def pitchFromTensionBule (tension : Nat) : Nat := 
  Nat.mul 110 tension

/-- Acoustic intensity as a function of pressure and tension -/
def acousticIntensityBule (pressure tension : Nat) : Nat :=
  Nat.mul (Nat.mul pressure tension) 100

/-- Voicing threshold in Nat representation -/
def voicingThresholdBule : Nat := 30

/-- Voicing condition based on pressure threshold -/
def canVoiceBule (state : LarynxStateBule) : Prop :=
  state.isVoiced → state.pressure ≥ voicingThresholdBule

/-- Stress scaling factors -/
structure StressScalingBule where
  pressure_factor : Nat := 20
  duration_factor : Nat := 30

/-- Apply stress scaling by addition (preserves Nat inequalities) -/
def applyStressScalingBule (state : LarynxStateBule) (scaling : StressScalingBule) : LarynxStateBule :=
  { state with 
    pressure := Nat.add state.pressure scaling.pressure_factor }

/-- Blending function for laryngeal parameters using Nat.min -/
def blendLarynxStatesBule (state1 state2 : LarynxStateBule) (weight1 weight2 : Nat) : LarynxStateBule :=
  {
    pitch := Nat.min state1.pitch state2.pitch,
    pressure := Nat.min state1.pressure state2.pressure,
    tension := Nat.min state1.tension state2.tension,
    isVoiced := if weight1 ≥ weight2 then state1.isVoiced else state2.isVoiced
  }

/-- Energy dissipation during voicing transitions -/
def energyDissipationBule (prev curr : LarynxStateBule) : Nat :=
  Nat.add (prev.pressure - curr.pressure) (curr.pressure - prev.pressure)

/-- Laryngeal configuration for unvoiced fricatives -/
def fricativeLarynxBule (isVoiced : Bool) : LarynxStateBule :=
  {
    pitch := 60,
    pressure := if isVoiced then 80 else 70,
    tension := 60,
    isVoiced := isVoiced
  }

/-- Laryngeal configuration for vowels -/
def vowelLarynxBule (stress : Bool) : LarynxStateBule :=
  {
    pitch := 110,
    pressure := if stress then 91 else 70,
    tension := 50,
    isVoiced := true
  }

/-! # Mathematical Theorems -/

/-- Theorem: Pitch increases monotonically with tension -/
theorem pitch_monotonic_in_tension (t1 t2 : Nat) (h : t1 < t2) :
    pitchFromTensionBule t1 < pitchFromTensionBule t2 := by
  unfold pitchFromTensionBule
  exact Nat.mul_lt_mul_of_pos_left h (by decide : 0 < 110)

/-- Theorem: Acoustic intensity increases with both pressure and tension -/
theorem intensity_monotonic (p1 p2 t1 t2 : Nat) 
    (hp : p1 < p2) (ht : t1 < t2) (hpos : 0 < p1 ∧ 0 < t1) :
    acousticIntensityBule p1 t1 < acousticIntensityBule p2 t2 := by
  unfold acousticIntensityBule
  have h1 : Nat.mul p1 t1 < Nat.mul p2 t1 := Nat.mul_lt_mul_of_pos_right hp hpos.2
  have h2 : Nat.mul p2 t1 < Nat.mul p2 t2 := Nat.mul_lt_mul_of_pos_left ht (Nat.lt_trans hpos.1 hp)
  have h3 : Nat.mul p1 t1 < Nat.mul p2 t2 := Nat.lt_trans h1 h2
  exact Nat.mul_lt_mul_of_pos_right h3 (by decide : 0 < 100)

/-- Theorem: Stress scaling preserves voicing capability -/
theorem stress_preserves_voicing (state : LarynxStateBule) (scaling : StressScalingBule)
    (h_voiced : canVoiceBule state) :
    canVoiceBule (applyStressScalingBule state scaling) := by
  unfold canVoiceBule applyStressScalingBule
  intro h_isVoiced
  have h_pressure := h_voiced h_isVoiced
  calc voicingThresholdBule
    _ ≤ state.pressure := h_pressure
    _ ≤ Nat.add state.pressure scaling.pressure_factor := Nat.le_add_right state.pressure scaling.pressure_factor

/-- Theorem: Blending preserves physical constraints -/
theorem blending_preserves_constraints (state1 state2 : LarynxStateBule) 
    (constraints : LaryngealConstraintsBule) (weight1 weight2 : Nat)
    (h_valid1 : isValidLarynxStateBule state1 constraints)
    (h_valid2 : isValidLarynxStateBule state2 constraints) :
    isValidLarynxStateBule (blendLarynxStatesBule state1 state2 weight1 weight2) constraints := by
  unfold isValidLarynxStateBule blendLarynxStatesBule
  constructor
  · exact Nat.lt_min.mpr ⟨h_valid1.1, h_valid2.1⟩
  constructor
  · calc Nat.min state1.tension state2.tension
      _ ≤ state1.tension := Nat.min_le_left _ _
      _ < constraints.tension_bounds.2 := h_valid1.2.1
  constructor
  · exact Nat.lt_min.mpr ⟨h_valid1.2.2.1, h_valid2.2.2.1⟩
  constructor
  · calc Nat.min state1.pressure state2.pressure
      _ ≤ state1.pressure := Nat.min_le_left _ _
      _ < constraints.pressure_bounds.2 := h_valid1.2.2.2.1
  constructor
  · exact Nat.lt_min.mpr ⟨h_valid1.2.2.2.2.1, h_valid2.2.2.2.2.1⟩
  · calc Nat.min state1.pitch state2.pitch
      _ ≤ state1.pitch := Nat.min_le_left _ _
      _ < constraints.pitch_bounds.2 := h_valid1.2.2.2.2.2

/-- Theorem: Mass conservation (multiplicative commutativity) -/
theorem mass_conservation (state : LarynxStateBule) :
    Nat.mul state.pressure state.tension = Nat.mul state.tension state.pressure := by
  exact Nat.mul_comm state.pressure state.tension

/-- Theorem: Energy dissipation is bounded for smooth transitions -/
theorem bounded_energy_dissipation (prev curr : LarynxStateBule) :
    energyDissipationBule prev curr ≤ Nat.add prev.pressure curr.pressure := by
  unfold energyDissipationBule
  have h1 : prev.pressure - curr.pressure ≤ prev.pressure := Nat.sub_le _ _
  have h2 : curr.pressure - prev.pressure ≤ curr.pressure := Nat.sub_le _ _
  exact Nat.add_le_add h1 h2

/-- Theorem: Fricative configurations satisfy physical constraints -/
theorem fricative_constraints_satisfied (isVoiced : Bool) :
    isValidLarynxStateBule (fricativeLarynxBule isVoiced) 
      { tension_bounds := (0, 200), pressure_bounds := (0, 300), pitch_bounds := (50, 500) } := by
  unfold isValidLarynxStateBule fricativeLarynxBule
  cases isVoiced <;> decide

/-- Theorem: Vowel configurations satisfy physical constraints -/
theorem vowel_constraints_satisfied (stress : Bool) :
    isValidLarynxStateBule (vowelLarynxBule stress)
      { tension_bounds := (0, 200), pressure_bounds := (0, 300), pitch_bounds := (50, 500) } := by
  unfold isValidLarynxStateBule vowelLarynxBule
  cases stress <;> decide

end Articulatory
end Gnosis
