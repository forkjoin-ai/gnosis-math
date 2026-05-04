
namespace Gnosis

def multiplexedCapacity (sequentialCapacity recoveredOverlap : Nat) : Nat :=
  sequentialCapacity - recoveredOverlap

def sequentialWallaceNumerator (busyWork sequentialCapacity : Nat) : Nat :=
  sequentialCapacity - busyWork

def multiplexedWallaceNumerator
    (busyWork sequentialCapacity recoveredOverlap : Nat) : Nat :=
  multiplexedCapacity sequentialCapacity recoveredOverlap - busyWork

theorem multiplexed_capacity_ge_busy
    {busyWork sequentialCapacity recoveredOverlap : Nat}
    (_hBusyPositive : 0 < busyWork)
    (hBusyFits : busyWork <= sequentialCapacity)
    (hRecoveredLegal : recoveredOverlap <= sequentialCapacity - busyWork) :
    busyWork <= multiplexedCapacity sequentialCapacity recoveredOverlap := by
  unfold multiplexedCapacity
  -- Goal: busyWork ≤ sequentialCapacity - recoveredOverlap
  -- From hRecoveredLegal + hBusyFits, derive busyWork + recoveredOverlap ≤ sequentialCapacity,
  -- then conclude via Nat.le_sub_of_add_le.
  exact Nat.le_sub_of_add_le
    (Nat.add_le_of_le_sub' hBusyFits hRecoveredLegal)

theorem multiplexing_wallace_numerator_monotone
    {busyWork sequentialCapacity recoveredOverlap : Nat}
    (_hBusyFits : busyWork <= sequentialCapacity)
    (_hRecoveredLegal : recoveredOverlap <= sequentialCapacity - busyWork) :
    multiplexedWallaceNumerator busyWork sequentialCapacity recoveredOverlap <=
      sequentialWallaceNumerator busyWork sequentialCapacity := by
  unfold multiplexedWallaceNumerator multiplexedCapacity sequentialWallaceNumerator
  -- Goal: (sequentialCapacity - recoveredOverlap) - busyWork
  --       ≤ sequentialCapacity - busyWork
  -- Sub on the right is monotone in the minuend; (S - r) ≤ S, so subtract busyWork.
  exact Nat.sub_le_sub_right
    (Nat.sub_le sequentialCapacity recoveredOverlap) busyWork

theorem multiplexing_wallace_numerator_drop_equals_overlap
    {busyWork sequentialCapacity recoveredOverlap : Nat}
    (_hBusyFits : busyWork <= sequentialCapacity)
    (hRecoveredLegal : recoveredOverlap <= sequentialCapacity - busyWork) :
    sequentialWallaceNumerator busyWork sequentialCapacity -
        multiplexedWallaceNumerator busyWork sequentialCapacity recoveredOverlap =
      recoveredOverlap := by
  unfold multiplexedWallaceNumerator multiplexedCapacity sequentialWallaceNumerator
  -- Goal: (sequentialCapacity - busyWork)
  --     - ((sequentialCapacity - recoveredOverlap) - busyWork)
  --     = recoveredOverlap
  -- Swap (S - r) - b to (S - b) - r via sub_right_comm, then collapse with sub_sub_self
  -- using hRecoveredLegal : recoveredOverlap ≤ sequentialCapacity - busyWork.
  rw [Nat.sub_right_comm sequentialCapacity recoveredOverlap busyWork]
  exact Nat.sub_sub_self hRecoveredLegal

theorem multiplexing_fill_monotone
    {busyWork sequentialCapacity recoveredOverlap : Nat} :
    busyWork * multiplexedCapacity sequentialCapacity recoveredOverlap <=
      busyWork * sequentialCapacity := by
  have hMuxLeSeq : multiplexedCapacity sequentialCapacity recoveredOverlap <= sequentialCapacity := by
    unfold multiplexedCapacity
    exact Nat.sub_le _ _
  exact Nat.mul_le_mul_left busyWork hMuxLeSeq

theorem multiplexing_wallace_ratio_monotone
    {busyWork sequentialCapacity recoveredOverlap : Nat}
    (hBusyFits : busyWork <= sequentialCapacity)
    (hRecoveredLegal : recoveredOverlap <= sequentialCapacity - busyWork) :
    multiplexedWallaceNumerator busyWork sequentialCapacity recoveredOverlap * sequentialCapacity <=
      sequentialWallaceNumerator busyWork sequentialCapacity *
        multiplexedCapacity sequentialCapacity recoveredOverlap := by
  let muxCap := multiplexedCapacity sequentialCapacity recoveredOverlap
  let muxWall := multiplexedWallaceNumerator busyWork sequentialCapacity recoveredOverlap
  let seqWall := sequentialWallaceNumerator busyWork sequentialCapacity
  have hRecoveredFits : recoveredOverlap <= sequentialCapacity := by
    exact Nat.le_trans hRecoveredLegal (Nat.sub_le _ _)
  have hSeqCapSplit : sequentialCapacity = muxCap + recoveredOverlap := by
    unfold muxCap multiplexedCapacity
    simpa [Nat.add_comm] using (Nat.sub_add_cancel hRecoveredFits).symm
  have hSeqWallGeMux : muxWall <= seqWall := by
    unfold muxWall seqWall
    exact multiplexing_wallace_numerator_monotone hBusyFits hRecoveredLegal
  have hSeqWallSplit : seqWall = muxWall + recoveredOverlap := by
    have hDrop :
        seqWall - muxWall = recoveredOverlap := by
      unfold seqWall muxWall
      exact multiplexing_wallace_numerator_drop_equals_overlap hBusyFits hRecoveredLegal
    have hEqAdd : seqWall = recoveredOverlap + muxWall :=
      (Nat.sub_eq_iff_eq_add hSeqWallGeMux).1 hDrop
    simpa [Nat.add_comm] using hEqAdd
  have hMuxWallLeCap : muxWall <= muxCap := by
    unfold muxWall muxCap multiplexedWallaceNumerator
    exact Nat.sub_le _ _
  calc
    muxWall * sequentialCapacity
      = muxWall * (muxCap + recoveredOverlap) := by rw [hSeqCapSplit]
    _ = muxWall * muxCap + muxWall * recoveredOverlap := by rw [Nat.mul_add]
    _ <= muxWall * muxCap + muxCap * recoveredOverlap := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right recoveredOverlap hMuxWallLeCap) _
    _ = muxWall * muxCap + recoveredOverlap * muxCap := by
      rw [Nat.mul_comm muxCap recoveredOverlap]
    _ = (muxWall + recoveredOverlap) * muxCap := by rw [Nat.add_mul]
    _ = seqWall * muxCap := by rw [hSeqWallSplit]

theorem multiplexing_wallace_ratio_strict
    {busyWork sequentialCapacity recoveredOverlap : Nat}
    (hBusyPositive : 0 < busyWork)
    (hBusyFits : busyWork <= sequentialCapacity)
    (hRecoveredLegal : recoveredOverlap <= sequentialCapacity - busyWork)
    (hRecoveredPositive : 0 < recoveredOverlap) :
    multiplexedWallaceNumerator busyWork sequentialCapacity recoveredOverlap * sequentialCapacity <
      sequentialWallaceNumerator busyWork sequentialCapacity *
        multiplexedCapacity sequentialCapacity recoveredOverlap := by
  let muxCap := multiplexedCapacity sequentialCapacity recoveredOverlap
  let muxWall := multiplexedWallaceNumerator busyWork sequentialCapacity recoveredOverlap
  let seqWall := sequentialWallaceNumerator busyWork sequentialCapacity
  have hRecoveredFits : recoveredOverlap <= sequentialCapacity := by
    exact Nat.le_trans hRecoveredLegal (Nat.sub_le _ _)
  have hSeqCapSplit : sequentialCapacity = muxCap + recoveredOverlap := by
    unfold muxCap multiplexedCapacity
    simpa [Nat.add_comm] using (Nat.sub_add_cancel hRecoveredFits).symm
  have hSeqWallGeMux : muxWall <= seqWall := by
    unfold muxWall seqWall
    exact multiplexing_wallace_numerator_monotone hBusyFits hRecoveredLegal
  have hSeqWallSplit : seqWall = muxWall + recoveredOverlap := by
    have hDrop :
        seqWall - muxWall = recoveredOverlap := by
      unfold seqWall muxWall
      exact multiplexing_wallace_numerator_drop_equals_overlap hBusyFits hRecoveredLegal
    have hEqAdd : seqWall = recoveredOverlap + muxWall :=
      (Nat.sub_eq_iff_eq_add hSeqWallGeMux).1 hDrop
    simpa [Nat.add_comm] using hEqAdd
  have hMuxBusy : busyWork <= muxCap := by
    unfold muxCap
    exact multiplexed_capacity_ge_busy hBusyPositive hBusyFits hRecoveredLegal
  have hMuxWallLtCap : muxWall < muxCap := by
    show multiplexedCapacity sequentialCapacity recoveredOverlap - busyWork
        < multiplexedCapacity sequentialCapacity recoveredOverlap
    -- 0 < busyWork and busyWork ≤ muxCap ⇒ muxCap - busyWork < muxCap
    exact Nat.sub_lt_self hBusyPositive hMuxBusy
  calc
    muxWall * sequentialCapacity
      = muxWall * (muxCap + recoveredOverlap) := by rw [hSeqCapSplit]
    _ = muxWall * muxCap + muxWall * recoveredOverlap := by rw [Nat.mul_add]
    _ < muxWall * muxCap + muxCap * recoveredOverlap := by
      exact Nat.add_lt_add_left
        (Nat.mul_lt_mul_of_pos_right hMuxWallLtCap hRecoveredPositive) _
    _ = muxWall * muxCap + recoveredOverlap * muxCap := by
      rw [Nat.mul_comm muxCap recoveredOverlap]
    _ = (muxWall + recoveredOverlap) * muxCap := by rw [Nat.add_mul]
    _ = seqWall * muxCap := by rw [hSeqWallSplit]

-- ─── THM-MULTIPLEXING-SATURATION-CEILING ────────────────────────────
-- Floor: recovering overlap monotonically helps (multiplexing_wallace_ratio_monotone).
-- Ceiling: maximum useful overlap = sequentialCapacity - busyWork.
-- Beyond that, overlap has no further effect.
-- ─────────────────────────────────────────────────────────────────────