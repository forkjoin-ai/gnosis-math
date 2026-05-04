namespace Gnosis

def frontierArea3 (left middle right : Nat) : Nat := left + middle + right

def peakFrontier3 (left middle right : Nat) : Nat := max left (max middle right)

def envelopeArea3 (left middle right : Nat) : Nat := 3 * peakFrontier3 left middle right

def wallaceNumerator3 (left middle right : Nat) : Nat :=
  envelopeArea3 left middle right - frontierArea3 left middle right

def wallaceDenominator3 (left middle right : Nat) : Nat :=
  envelopeArea3 left middle right

theorem frontierArea3_le_envelopeArea3 (left middle right : Nat) :
    frontierArea3 left middle right <= envelopeArea3 left middle right := by
  unfold frontierArea3 envelopeArea3 peakFrontier3
  have hLeft : left <= max left (max middle right) := Nat.le_max_left _ _
  have hMiddleInner : middle <= max middle right := Nat.le_max_left _ _
  have hMiddle : middle <= max left (max middle right) :=
    Nat.le_trans hMiddleInner (Nat.le_max_right left (max middle right))
  have hRightInner : right <= max middle right := Nat.le_max_right _ _
  have hRight : right <= max left (max middle right) :=
    Nat.le_trans hRightInner (Nat.le_max_right left (max middle right))
  -- left + middle + right ≤ M + M + M = 3 * M  where M = max left (max middle right)
  have hSum : left + middle + right
      ≤ max left (max middle right) + max left (max middle right)
        + max left (max middle right) :=
    Nat.add_le_add (Nat.add_le_add hLeft hMiddle) hRight
  have hThree : 3 * max left (max middle right)
      = max left (max middle right) + max left (max middle right)
        + max left (max middle right) := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.succ_mul, Nat.two_mul]
  exact hThree ▸ hSum

theorem wallace_bounds3 (left middle right : Nat) :
    wallaceNumerator3 left middle right <= wallaceDenominator3 left middle right := by
  unfold wallaceNumerator3 wallaceDenominator3
  exact Nat.sub_le _ _

theorem wallace_complement3 (left middle right : Nat) :
    frontierArea3 left middle right + wallaceNumerator3 left middle right =
      wallaceDenominator3 left middle right := by
  have hAreaLeEnvelope := frontierArea3_le_envelopeArea3 left middle right
  unfold wallaceNumerator3 wallaceDenominator3
  exact Nat.add_sub_of_le hAreaLeEnvelope

theorem wallace_zero_iff_full3 (left middle right : Nat) :
    wallaceNumerator3 left middle right = 0 ↔
      frontierArea3 left middle right = wallaceDenominator3 left middle right := by
  have hAreaLeEnvelope := frontierArea3_le_envelopeArea3 left middle right
  unfold wallaceNumerator3 wallaceDenominator3
  constructor
  · intro hSubZero
    have hEnvLeFront :
        envelopeArea3 left middle right ≤ frontierArea3 left middle right :=
      Nat.le_of_sub_eq_zero hSubZero
    exact Nat.le_antisymm hAreaLeEnvelope hEnvLeFront
  · intro hEq
    exact Nat.sub_eq_zero_of_le (Nat.le_of_eq hEq.symm)

def diamondFrontierArea (branchWidth : Nat) : Nat := frontierArea3 1 branchWidth 1

def diamondWallaceNumerator (branchWidth : Nat) : Nat := wallaceNumerator3 1 branchWidth 1

def diamondWallaceDenominator (branchWidth : Nat) : Nat := wallaceDenominator3 1 branchWidth 1

theorem diamond_peak {branchWidth : Nat} (hBranchWidth : 0 < branchWidth) :
    peakFrontier3 1 branchWidth 1 = branchWidth := by
  unfold peakFrontier3
  rw [Nat.max_eq_left (Nat.succ_le_of_lt hBranchWidth)]
  exact Nat.max_eq_right (Nat.succ_le_of_lt hBranchWidth)

theorem diamond_wallace_closed_form {branchWidth : Nat}
    (hBranchWidth : 0 < branchWidth) :
    diamondFrontierArea branchWidth = branchWidth + 2 /\
      diamondWallaceNumerator branchWidth = 2 * (branchWidth - 1) /\
      diamondWallaceDenominator branchWidth = 3 * branchWidth := by
  have hPeak := diamond_peak hBranchWidth
  constructor
  · unfold diamondFrontierArea frontierArea3
    -- Goal: 1 + branchWidth + 1 = branchWidth + 2
    rw [Nat.add_comm 1 branchWidth]
  constructor
  · unfold diamondWallaceNumerator wallaceNumerator3 envelopeArea3 frontierArea3
    rw [hPeak]
    -- Goal: 3 * branchWidth - (1 + branchWidth + 1) = 2 * (branchWidth - 1)
    have hSum : (1 : Nat) + branchWidth + 1 = branchWidth + 2 := by
      rw [Nat.add_comm 1 branchWidth]
    rw [hSum]
    -- Goal: 3 * branchWidth - (branchWidth + 2) = 2 * (branchWidth - 1)
    have h3b : 3 * branchWidth = 2 * branchWidth + branchWidth := by
      rw [show (3 : Nat) = 2 + 1 from rfl, Nat.succ_mul]
    rw [h3b, ← Nat.sub_sub, Nat.add_sub_cancel, Nat.mul_sub]
  · unfold diamondWallaceDenominator wallaceDenominator3 envelopeArea3
    rw [hPeak]

theorem diamond_wallace_zero_iff_unit {branchWidth : Nat}
    (hBranchWidth : 0 < branchWidth) :
    diamondWallaceNumerator branchWidth = 0 ↔ branchWidth = 1 := by
  have hPeak := diamond_peak hBranchWidth
  unfold diamondWallaceNumerator wallaceNumerator3 envelopeArea3 frontierArea3
  rw [hPeak]
  -- Goal: 3 * branchWidth - (1 + branchWidth + 1) = 0 ↔ branchWidth = 1
  have hSum : (1 : Nat) + branchWidth + 1 = branchWidth + 2 := by
    rw [Nat.add_comm 1 branchWidth]
  have h3b : 3 * branchWidth = 2 * branchWidth + branchWidth := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.succ_mul]
  rw [hSum, h3b, ← Nat.sub_sub, Nat.add_sub_cancel]
  -- Goal: 2 * branchWidth - 2 = 0 ↔ branchWidth = 1
  constructor
  · intro hZ
    have h2bLe2 : 2 * branchWidth ≤ 2 := Nat.le_of_sub_eq_zero hZ
    have hGe : 2 ≤ 2 * branchWidth := Nat.mul_le_mul_left 2 hBranchWidth
    have h2bEq2 : 2 * branchWidth = 2 * 1 := Nat.le_antisymm h2bLe2 hGe
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2bEq2
  · intro hEq
    rw [hEq]

end Gnosis