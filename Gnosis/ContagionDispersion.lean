import Init
import Gnosis.AtmosphericCirculation

namespace Gnosis.ContagionDispersion

def diffuse_pressure (p delta : Nat) : Nat := p + delta

theorem pressure_spillover_monotone (p delta1 delta2 : Nat) (h : delta1 <= delta2) :
    diffuse_pressure p delta1 <= diffuse_pressure p delta2 :=
  Nat.add_le_add_left h p

theorem shear_kernel_lift (B kernel shear : Nat) :
    AtmosphericCirculation.stormCirc B shear <= AtmosphericCirculation.stormCirc (B + kernel) shear := by
  unfold AtmosphericCirculation.stormCirc
  have h_B : B <= B + kernel := Nat.le_add_right B kernel
  have h_sub_mono : B - min shear B <= (B + kernel) - min shear (B + kernel) := by
    have h2 : B - min shear B <= (B + kernel) - min shear B := Nat.sub_le_sub_right h_B _
    have h_min_le : min shear B <= min shear (B + kernel) := by
      cases Nat.le_total shear B with
      | inl hle =>
        rw [Nat.min_eq_left hle, Nat.min_eq_left (Nat.le_trans hle h_B)]
      | inr hge =>
        rw [Nat.min_eq_right hge, Nat.min_eq_right (Nat.le_trans hge h_B)]
        exact h_B
    have h3 : (B + kernel) - min shear (B + kernel) <= (B + kernel) - min shear B :=
      Nat.sub_le_sub_left h_min_le _
    exact Nat.le_trans h2 h3
  exact Nat.add_le_add_right h_sub_mono 1

theorem routing_morphism (B s1 s2 : Nat) (h : s1 <= s2) :
    (AtmosphericCirculation.stormCirc B s2 <= AtmosphericCirculation.stormCirc B s1) ∧
    (AtmosphericCirculation.stormPress B s1 <= AtmosphericCirculation.stormPress B s2) := by
  constructor
  · unfold AtmosphericCirculation.stormCirc
    have h_min : min s1 B <= min s2 B := by
      cases Nat.le_total s1 B with
      | inl hle1 =>
        rw [Nat.min_eq_left hle1]
        cases Nat.le_total s2 B with
        | inl hle2 =>
          rw [Nat.min_eq_left hle2]
          exact h
        | inr hge2 =>
          rw [Nat.min_eq_right hge2]
          exact hle1
      | inr hge1 =>
        rw [Nat.min_eq_right hge1]
        exact Nat.min_le_right s2 B
    exact Nat.add_le_add_right (Nat.sub_le_sub_left h_min B) 1
  · exact AtmosphericCirculation.press_monotone_shear B s1 s2 h

end Gnosis.ContagionDispersion
