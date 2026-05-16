import Init
import Gnosis.AtmosphericCirculation

namespace Gnosis.ContagionDispersion

def diffuse_pressure (p delta : Nat) : Nat := p + delta

theorem pressure_spillover_monotone (p delta1 delta2 : Nat) (h : delta1 <= delta2) :
    diffuse_pressure p delta1 <= diffuse_pressure p delta2 :=
  Nat.add_le_add_left h p

/-- Circulation under budget increase (when shear ≤ B): monotone growth. -/
theorem shear_kernel_lift (B kernel shear : Nat) (h_shear : shear <= B) :
    AtmosphericCirculation.stormCirc B shear <= AtmosphericCirculation.stormCirc (B + kernel) shear := by
  unfold AtmosphericCirculation.stormCirc
  -- When shear ≤ B, both mins evaluate to shear
  rw [Nat.min_eq_left h_shear, Nat.min_eq_left (Nat.le_trans h_shear (Nat.le_add_right B kernel))]
  -- Goal: B - shear + 1 ≤ (B + kernel) - shear + 1
  -- Follows from B ≤ B + kernel via subtraction monotonicity
  have : B - shear <= (B + kernel) - shear := Nat.sub_le_sub_right (Nat.le_add_right B kernel) shear
  exact Nat.add_le_add_right this 1

/-- Circulation decreases (weakly) as shear increases; pressure increases correspondingly. -/
theorem routing_morphism (B s1 s2 : Nat) (h : s1 <= s2) :
    (AtmosphericCirculation.stormCirc B s2 <= AtmosphericCirculation.stormCirc B s1) ∧
    (AtmosphericCirculation.stormPress B s1 <= AtmosphericCirculation.stormPress B s2) := by
  constructor
  · unfold AtmosphericCirculation.stormCirc
    -- We need to show B - min(s2, B) + 1 ≤ B - min(s1, B) + 1
    -- This is equivalent to showing min(s2, B) ≥ min(s1, B)
    have h_min : min s1 B <= min s2 B := by
      by_cases h1 : s1 <= B
      case pos =>
        rw [Nat.min_eq_left h1]
        -- s1 ≤ B, and s1 ≤ s2
        by_cases h2 : s2 <= B
        case pos =>
          rw [Nat.min_eq_left h2]
          exact h
        case neg =>
          -- s2 > B but s1 ≤ s2, so s1 ≤ B < s2
          rw [Nat.min_eq_right (Nat.le_of_not_le h2)]
          exact h1
      case neg =>
        -- s1 > B
        rw [Nat.min_eq_right (Nat.le_of_not_le h1)]
        -- min(s2, B) ≥ B since s1 ≤ s2 and s1 > B implies ...
        -- Actually: since s1 > B and s1 ≤ s2, we have B < s2, so min(s2, B) = B
        rw [Nat.min_eq_right (Nat.le_trans (Nat.le_of_not_le h1) h)]
        exact Nat.le_refl B
    -- Having min(s1, B) ≤ min(s2, B), we derive the circulation inequality
    -- B - min(s1, B) ≥ B - min(s2, B), so B - min(s2, B) + 1 ≤ B - min(s1, B) + 1
    have : B - min s2 B <= B - min s1 B := Nat.sub_le_sub_left h_min B
    exact Nat.add_le_add_right this 1
  · exact AtmosphericCirculation.press_monotone_shear B s1 s2 h

end Gnosis.ContagionDispersion
