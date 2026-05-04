-- HeteroMoAFabric.lean — Heterogeneous mixture-of-attention fabric proofs
-- Country-church chapel idiom: Init/omega only, no Mathlib.

namespace Gnosis

inductive BackendLayer where
  | cpu
  | gpu
  | npu
  | wasm
  deriving DecidableEq, Repr

def totalLanes (cpuLanes gpuLanes npuLanes wasmLanes : Nat) : Nat :=
  cpuLanes + gpuLanes + npuLanes + wasmLanes

def activeLayerCount (cpuLanes gpuLanes npuLanes wasmLanes : Nat) : Nat :=
  (if 0 < cpuLanes then 1 else 0) +
    (if 0 < gpuLanes then 1 else 0) +
      (if 0 < npuLanes then 1 else 0) +
        (if 0 < wasmLanes then 1 else 0)

def mirroredKernelTotal (cpuLanes gpuLanes npuLanes wasmLanes : Nat) : Nat :=
  2 * totalLanes cpuLanes gpuLanes npuLanes wasmLanes

def readyBackendCount (cpuReady gpuReady npuReady wasmReady : Bool) : Nat :=
  (if cpuReady then 1 else 0) +
    (if gpuReady then 1 else 0) +
      (if npuReady then 1 else 0) +
        (if wasmReady then 1 else 0)

def cannonCursor (laneCount cursor waveWidth : Nat) : Nat :=
  if laneCount = 0 then 0 else (cursor + waveWidth) % laneCount

def helixPhase (layerCount round : Nat) : Nat :=
  if layerCount = 0 then 0 else round % layerCount

inductive PairDecision where
  | acceptAgreement
  | acceptPrimary
  | escalate
  deriving DecidableEq, Repr

def pairedKernelDecision (agree primarySufficient shadowFired : Bool) : PairDecision :=
  if agree then
    .acceptAgreement
  else if primarySufficient && not shadowFired then
    .acceptPrimary
  else
    .escalate

def binaryHeaderBytes : Nat := 10

def binaryFrameBytes (payloadBytes : Nat) : Nat :=
  binaryHeaderBytes + payloadBytes

def skippedWithinBudget (skippedHedges scheduledShadows : Nat) : Prop :=
  skippedHedges <= scheduledShadows

def conservedBytes (winnerBytes loserBytes ventBytes totalBytes : Nat) : Prop :=
  winnerBytes + loserBytes + ventBytes = totalBytes

def metaLaminarHeight (streamLayers backendLayers : Nat) : Nat :=
  streamLayers + backendLayers + 1

theorem mirroredKernelTotal_eq_twice_totalLanes
    (cpuLanes gpuLanes npuLanes wasmLanes : Nat) :
    mirroredKernelTotal cpuLanes gpuLanes npuLanes wasmLanes =
      2 * totalLanes cpuLanes gpuLanes npuLanes wasmLanes := by
  rfl

theorem activeLayerCount_le_totalLanes
    (cpuLanes gpuLanes npuLanes wasmLanes : Nat) :
    activeLayerCount cpuLanes gpuLanes npuLanes wasmLanes <=
      totalLanes cpuLanes gpuLanes npuLanes wasmLanes := by
  unfold activeLayerCount totalLanes
  -- Per-lane bound: `(if 0 < n then 1 else 0) ≤ n`.
  have indicator_le : ∀ n : Nat, (if 0 < n then 1 else 0) ≤ n := by
    intro n
    by_cases h : 0 < n
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact Nat.zero_le _
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (indicator_le cpuLanes) (indicator_le gpuLanes))
      (indicator_le npuLanes))
    (indicator_le wasmLanes)

theorem activeLayerCount_pos_of_totalLanes_pos
    {cpuLanes gpuLanes npuLanes wasmLanes : Nat}
    (h_total : 0 < totalLanes cpuLanes gpuLanes npuLanes wasmLanes) :
    0 < activeLayerCount cpuLanes gpuLanes npuLanes wasmLanes := by
  unfold totalLanes at h_total
  unfold activeLayerCount
  -- Bound each indicator below by its lane count contribution would not
  -- close this directly. Instead: show at least one indicator is `1` because
  -- otherwise all lanes are zero, contradicting `h_total`.
  -- Strategy: contrapositive — if the sum of indicators is zero, each is zero,
  -- so each lane is zero, so totalLanes is zero.
  by_cases h1 : 0 < cpuLanes
  · -- First summand is `1`. Use `Nat.lt_of_lt_of_le 1 (1 + ...)`.
    rw [if_pos h1]
    -- Goal: 0 < ((1 + _) + _) + _.  Bound by 1 ≤ ((1 + _) + _) + _.
    have h_one : 1 ≤ ((1 + (if 0 < gpuLanes then 1 else 0)) +
        (if 0 < npuLanes then 1 else 0)) + (if 0 < wasmLanes then 1 else 0) :=
      Nat.le_trans
        (Nat.le_trans
          (Nat.le_add_right 1 (if 0 < gpuLanes then 1 else 0))
          (Nat.le_add_right (1 + (if 0 < gpuLanes then 1 else 0))
            (if 0 < npuLanes then 1 else 0)))
        (Nat.le_add_right ((1 + (if 0 < gpuLanes then 1 else 0)) +
            (if 0 < npuLanes then 1 else 0))
          (if 0 < wasmLanes then 1 else 0))
    exact h_one
  · rw [if_neg h1]
    have h_cpu_zero : cpuLanes = 0 := Nat.eq_zero_of_not_pos h1
    by_cases h2 : 0 < gpuLanes
    · rw [if_pos h2]
      -- Goal: 0 < ((0 + 1) + _) + _.
      have h_one : 1 ≤ ((0 + 1 + (if 0 < npuLanes then 1 else 0)) +
          (if 0 < wasmLanes then 1 else 0)) :=
        Nat.le_trans
          (Nat.le_trans
            (Nat.le_of_eq (Nat.zero_add 1).symm)
            (Nat.le_add_right (0 + 1) (if 0 < npuLanes then 1 else 0)))
          (Nat.le_add_right ((0 + 1) + (if 0 < npuLanes then 1 else 0))
            (if 0 < wasmLanes then 1 else 0))
      exact h_one
    · rw [if_neg h2]
      have h_gpu_zero : gpuLanes = 0 := Nat.eq_zero_of_not_pos h2
      by_cases h3 : 0 < npuLanes
      · rw [if_pos h3]
        -- Goal: 0 < ((0 + 0) + 1) + _. Note: `0 + 0 + 1 = 1` definitionally.
        have h_eq : (0 + 0 + 1 : Nat) = 1 := rfl
        have h_one : 1 ≤ (0 + 0 + 1 + (if 0 < wasmLanes then 1 else 0)) :=
          Nat.le_trans
            (Nat.le_of_eq h_eq.symm)
            (Nat.le_add_right (0 + 0 + 1) (if 0 < wasmLanes then 1 else 0))
        exact h_one
      · rw [if_neg h3]
        have h_npu_zero : npuLanes = 0 := Nat.eq_zero_of_not_pos h3
        -- All of cpu, gpu, npu are zero. wasm must be positive.
        have h_wasm : 0 < wasmLanes := by
          rw [h_cpu_zero, h_gpu_zero, h_npu_zero] at h_total
          -- h_total : 0 < 0 + 0 + 0 + wasmLanes; reduces to 0 + wasmLanes.
          rw [Nat.zero_add] at h_total
          exact h_total
        rw [if_pos h_wasm]
        -- Goal: 0 < 0 + 0 + 0 + 1. This reduces to 0 < 1 definitionally.
        exact Nat.succ_pos 0

theorem activeLayerCount_le_four
    (cpuLanes gpuLanes npuLanes wasmLanes : Nat) :
    activeLayerCount cpuLanes gpuLanes npuLanes wasmLanes <= 4 := by
  unfold activeLayerCount
  by_cases h1 : 0 < cpuLanes <;> by_cases h2 : 0 < gpuLanes <;>
    by_cases h3 : 0 < npuLanes <;> by_cases h4 : 0 < wasmLanes <;>
    simp [h1, h2, h3, h4] <;> decide

theorem activeLayerCount_eq_four_of_all_positive
    {cpuLanes gpuLanes npuLanes wasmLanes : Nat}
    (h_cpu : 0 < cpuLanes)
    (h_gpu : 0 < gpuLanes)
    (h_npu : 0 < npuLanes)
    (h_wasm : 0 < wasmLanes) :
    activeLayerCount cpuLanes gpuLanes npuLanes wasmLanes = 4 := by
  simp [activeLayerCount, h_cpu, h_gpu, h_npu, h_wasm]

theorem activeLayerCount_eq_zero_of_all_zero :
    activeLayerCount 0 0 0 0 = 0 := by
  simp [activeLayerCount]

theorem activeLayerCount_pos_iff_totalLanes_pos
    (cpuLanes gpuLanes npuLanes wasmLanes : Nat) :
    0 < activeLayerCount cpuLanes gpuLanes npuLanes wasmLanes ↔
      0 < totalLanes cpuLanes gpuLanes npuLanes wasmLanes := by
  constructor
  · intro h_active
    -- 0 < active ≤ total ⇒ 0 < total.
    exact Nat.lt_of_lt_of_le h_active
      (activeLayerCount_le_totalLanes cpuLanes gpuLanes npuLanes wasmLanes)
  · intro h_total
    exact activeLayerCount_pos_of_totalLanes_pos h_total

theorem readyBackendCount_pos_of_any_ready
    {cpuReady gpuReady npuReady wasmReady : Bool}
    (h_ready : cpuReady = true ∨ gpuReady = true ∨ npuReady = true ∨ wasmReady = true) :
    0 < readyBackendCount cpuReady gpuReady npuReady wasmReady := by
  unfold readyBackendCount
  cases cpuReady <;> cases gpuReady <;> cases npuReady <;> cases wasmReady <;>
    first | decide | (simp at h_ready)

theorem readyBackendCount_le_four
    (cpuReady gpuReady npuReady wasmReady : Bool) :
    readyBackendCount cpuReady gpuReady npuReady wasmReady <= 4 := by
  unfold readyBackendCount
  cases cpuReady <;> cases gpuReady <;> cases npuReady <;> cases wasmReady <;> decide

theorem readyBackendCount_eq_zero_of_all_not_ready
    (h_cpu : cpuReady = false)
    (h_gpu : gpuReady = false)
    (h_npu : npuReady = false)
    (h_wasm : wasmReady = false) :
    readyBackendCount cpuReady gpuReady npuReady wasmReady = 0 := by
  simp [readyBackendCount, h_cpu, h_gpu, h_npu, h_wasm]

theorem readyBackendCount_eq_four_of_all_ready
    (h_cpu : cpuReady = true)
    (h_gpu : gpuReady = true)
    (h_npu : npuReady = true)
    (h_wasm : wasmReady = true) :
    readyBackendCount cpuReady gpuReady npuReady wasmReady = 4 := by
  simp [readyBackendCount, h_cpu, h_gpu, h_npu, h_wasm]

theorem readyBackendCount_pos_iff_any_ready
    (cpuReady gpuReady npuReady wasmReady : Bool) :
    0 < readyBackendCount cpuReady gpuReady npuReady wasmReady ↔
      cpuReady = true ∨ gpuReady = true ∨ npuReady = true ∨ wasmReady = true := by
  constructor
  · intro h_ready
    cases cpuReady <;> cases gpuReady <;> cases npuReady <;> cases wasmReady <;>
      simp [readyBackendCount] at h_ready ⊢
  · exact readyBackendCount_pos_of_any_ready

theorem diverse_ready_backends_of_cpu_and_accelerator
    {cpuReady gpuReady npuReady wasmReady : Bool}
    (h_cpu : cpuReady = true)
    (h_accel : gpuReady = true ∨ npuReady = true ∨ wasmReady = true) :
    2 <= readyBackendCount cpuReady gpuReady npuReady wasmReady := by
  unfold readyBackendCount
  rw [h_cpu]
  -- Goal shape: 2 ≤ ((if true then 1 else 0) + ...).  Reduce the cpu if.
  rw [if_pos rfl]
  -- Goal: 2 ≤ ((1 + (if gpu...)) + (if npu...)) + (if wasm...).
  rcases h_accel with h_gpu | h_rest
  · -- gpuReady = true ⇒ second indicator is also 1.
    rw [h_gpu, if_pos rfl]
    -- Goal: 2 ≤ ((1 + 1) + (if npu...)) + (if wasm...). Use 2 ≤ 1 + 1 ≤ ...
    have h_two : (2 : Nat) ≤ 1 + 1 := Nat.le_refl 2
    exact Nat.le_trans h_two
      (Nat.le_trans
        (Nat.le_add_right (1 + 1) (if npuReady = true then 1 else 0))
        (Nat.le_add_right ((1 + 1) + (if npuReady = true then 1 else 0))
          (if wasmReady = true then 1 else 0)))
  · rcases h_rest with h_npu | h_wasm
    · -- npuReady = true.
      rw [h_npu, if_pos rfl]
      -- Goal: 2 ≤ ((1 + (if gpu...)) + 1) + (if wasm...).
      -- Use: 2 = 1 + 1 ≤ (1 + 0) + 1 ≤ (1 + g) + 1 ≤ ((1 + g) + 1) + w.
      have h_step1 : (2 : Nat) ≤ 1 + (if gpuReady = true then 1 else 0) + 1 := by
        -- Show 1 + (if g) + 1 = (1 + (if g)) + 1, lower-bound the gpu indicator by 0.
        have h_ind : 0 ≤ (if gpuReady = true then 1 else 0) := Nat.zero_le _
        -- 1 + (if g) ≥ 1 by Nat.le_add_right.
        have h_le : (1 : Nat) ≤ 1 + (if gpuReady = true then 1 else 0) :=
          Nat.le_add_right 1 _
        -- Add 1 on the right:
        have h_plus : (1 + 1 : Nat) ≤ (1 + (if gpuReady = true then 1 else 0)) + 1 :=
          Nat.add_le_add_right h_le 1
        exact h_plus
      exact Nat.le_trans h_step1
        (Nat.le_add_right ((1 + (if gpuReady = true then 1 else 0)) + 1)
          (if wasmReady = true then 1 else 0))
    · -- wasmReady = true.
      rw [h_wasm, if_pos rfl]
      -- Goal: 2 ≤ ((1 + (if gpu...)) + (if npu...)) + 1.
      have h_le : (1 : Nat) ≤ (1 + (if gpuReady = true then 1 else 0)) +
          (if npuReady = true then 1 else 0) :=
        Nat.le_trans
          (Nat.le_add_right 1 (if gpuReady = true then 1 else 0))
          (Nat.le_add_right (1 + (if gpuReady = true then 1 else 0))
            (if npuReady = true then 1 else 0))
      have h_plus : (1 + 1 : Nat) ≤ ((1 + (if gpuReady = true then 1 else 0)) +
          (if npuReady = true then 1 else 0)) + 1 :=
        Nat.add_le_add_right h_le 1
      exact h_plus

theorem cannonCursor_step_mod
    {laneCount cursor waveWidth : Nat}
    (h_laneCount : 0 < laneCount) :
    cannonCursor laneCount cursor waveWidth = (cursor + waveWidth) % laneCount := by
  simp [cannonCursor, Nat.ne_of_gt h_laneCount]

theorem cannonCursor_zero_of_zero_laneCount
    (cursor waveWidth : Nat) :
    cannonCursor 0 cursor waveWidth = 0 := by
  simp [cannonCursor]

theorem cannonCursor_lt_laneCount
    {laneCount cursor waveWidth : Nat}
    (h_laneCount : 0 < laneCount) :
    cannonCursor laneCount cursor waveWidth < laneCount := by
  rw [cannonCursor_step_mod h_laneCount]
  exact Nat.mod_lt _ h_laneCount

theorem cannonCursor_waveWidth_zero_eq_cursor_mod
    {laneCount cursor : Nat}
    (h_laneCount : 0 < laneCount) :
    cannonCursor laneCount cursor 0 = cursor % laneCount := by
  simp [cannonCursor, Nat.ne_of_gt h_laneCount]

theorem helixPhase_lt_layerCount
    {layerCount round : Nat}
    (h_layerCount : 0 < layerCount) :
    helixPhase layerCount round < layerCount := by
  simp [helixPhase, Nat.ne_of_gt h_layerCount, Nat.mod_lt, h_layerCount]

theorem helixPhase_zero_of_zero_layerCount
    (round : Nat) :
    helixPhase 0 round = 0 := by
  simp [helixPhase]

theorem pairedKernelDecision_of_agreement
    {primarySufficient shadowFired : Bool} :
    pairedKernelDecision true primarySufficient shadowFired = PairDecision.acceptAgreement := by
  simp [pairedKernelDecision]

theorem pairedKernelDecision_of_sufficient_primary
    {shadowFired : Bool}
    (h_shadow : shadowFired = false) :
    pairedKernelDecision false true shadowFired = PairDecision.acceptPrimary := by
  simp [pairedKernelDecision, h_shadow]

theorem pairedKernelDecision_of_disagreement
    {primarySufficient shadowFired : Bool}
    (h_agree : primarySufficient = false ∨ shadowFired = true) :
    pairedKernelDecision false primarySufficient shadowFired = PairDecision.escalate := by
  rcases h_agree with h_primary | h_shadow
  · simp [pairedKernelDecision, h_primary]
  · simp [pairedKernelDecision, h_shadow]

theorem pairedKernelDecision_ne_acceptAgreement_of_disagree
    {primarySufficient shadowFired : Bool} :
    pairedKernelDecision false primarySufficient shadowFired ≠ PairDecision.acceptAgreement := by
  cases primarySufficient <;> cases shadowFired <;> decide

theorem pairedKernelDecision_ne_acceptPrimary_of_disagreement
    {primarySufficient shadowFired : Bool}
    (h_disagree : primarySufficient = false ∨ shadowFired = true) :
    pairedKernelDecision false primarySufficient shadowFired ≠ PairDecision.acceptPrimary := by
  rcases h_disagree with h_primary | h_shadow
  · simp [pairedKernelDecision, h_primary]
  · simp [pairedKernelDecision, h_shadow]

theorem pairedKernelDecision_ne_escalate_of_agreement
    {primarySufficient shadowFired : Bool} :
    pairedKernelDecision true primarySufficient shadowFired ≠ PairDecision.escalate := by
  simp [pairedKernelDecision]

theorem pairedKernelDecision_ne_escalate_of_sufficient_primary
    {shadowFired : Bool}
    (h_shadow : shadowFired = false) :
    pairedKernelDecision false true shadowFired ≠ PairDecision.escalate := by
  simp [pairedKernelDecision, h_shadow]

theorem pairedKernelDecision_eq_acceptAgreement_iff
    (agree primarySufficient shadowFired : Bool) :
    pairedKernelDecision agree primarySufficient shadowFired = PairDecision.acceptAgreement ↔
      agree = true := by
  cases agree <;> cases primarySufficient <;> cases shadowFired <;> decide

theorem pairedKernelDecision_eq_acceptPrimary_iff
    (agree primarySufficient shadowFired : Bool) :
    pairedKernelDecision agree primarySufficient shadowFired = PairDecision.acceptPrimary ↔
      agree = false ∧ primarySufficient = true ∧ shadowFired = false := by
  cases agree <;> cases primarySufficient <;> cases shadowFired <;> decide

theorem pairedKernelDecision_eq_escalate_iff
    (agree primarySufficient shadowFired : Bool) :
    pairedKernelDecision agree primarySufficient shadowFired = PairDecision.escalate ↔
      agree = false ∧ (primarySufficient = false ∨ shadowFired = true) := by
  cases agree <;> cases primarySufficient <;> cases shadowFired <;> decide

theorem binaryHeaderBytes_eq_ten :
    binaryHeaderBytes = 10 := by
  rfl

theorem binaryFrameBytes_ge_header (payloadBytes : Nat) :
    binaryHeaderBytes <= binaryFrameBytes payloadBytes := by
  unfold binaryFrameBytes binaryHeaderBytes
  exact Nat.le_add_right 10 payloadBytes

theorem binaryFrameBytes_strictMono :
    ∀ a b : Nat, a < b → binaryFrameBytes a < binaryFrameBytes b := by
  intro payload₁ payload₂ h_payload
  unfold binaryFrameBytes
  exact Nat.add_lt_add_left h_payload binaryHeaderBytes

theorem binaryFrameBytes_injective :
    ∀ a b : Nat, binaryFrameBytes a = binaryFrameBytes b → a = b := by
  intro a b h
  unfold binaryFrameBytes binaryHeaderBytes at h
  exact Nat.add_left_cancel h

theorem binaryFrameBytes_eq_header_of_zero_payload :
    binaryFrameBytes 0 = binaryHeaderBytes := by
  simp [binaryFrameBytes]

theorem binaryFrameBytes_eq_header_iff
    (payloadBytes : Nat) :
    binaryFrameBytes payloadBytes = binaryHeaderBytes ↔ payloadBytes = 0 := by
  unfold binaryFrameBytes binaryHeaderBytes
  constructor
  · intro h
    -- 10 + payloadBytes = 10 = 10 + 0 ⇒ payloadBytes = 0.
    exact Nat.add_left_cancel (h.trans (Nat.add_zero 10).symm)
  · intro h; rw [h]

theorem binaryFrameBytes_pos (payloadBytes : Nat) :
    0 < binaryFrameBytes payloadBytes := by
  unfold binaryFrameBytes binaryHeaderBytes
  exact Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 10) (Nat.le_add_right 10 payloadBytes)

theorem payloadBytes_le_binaryFrameBytes
    (payloadBytes : Nat) :
    payloadBytes <= binaryFrameBytes payloadBytes := by
  unfold binaryFrameBytes binaryHeaderBytes
  exact Nat.le_add_left payloadBytes 10

theorem skippedWithinBudget_of_le
    {skippedHedges scheduledShadows : Nat}
    (h_budget : skippedHedges <= scheduledShadows) :
    skippedWithinBudget skippedHedges scheduledShadows := by
  exact h_budget

theorem conservedBytes_of_total
    {winnerBytes loserBytes ventBytes totalBytes : Nat}
    (h_total : totalBytes = winnerBytes + loserBytes + ventBytes) :
    conservedBytes winnerBytes loserBytes ventBytes totalBytes := by
  simpa [conservedBytes] using h_total.symm

theorem conservedBytes_iff_total
    {winnerBytes loserBytes ventBytes totalBytes : Nat} :
    conservedBytes winnerBytes loserBytes ventBytes totalBytes ↔
      totalBytes = winnerBytes + loserBytes + ventBytes := by
  constructor
  · intro h_conserved
    simpa [conservedBytes] using h_conserved.symm
  · intro h_total
    simpa [conservedBytes] using h_total.symm

theorem skippedWithinBudget_zero
    (scheduledShadows : Nat) :
    skippedWithinBudget 0 scheduledShadows := by
  exact Nat.zero_le scheduledShadows

theorem metaLaminarHeight_pos (streamLayers backendLayers : Nat) :
    0 < metaLaminarHeight streamLayers backendLayers := by
  unfold metaLaminarHeight
  exact Nat.succ_pos _

theorem metaLaminarHeight_ge_streamLayers_succ
    (streamLayers backendLayers : Nat) :
    streamLayers + 1 <= metaLaminarHeight streamLayers backendLayers := by
  unfold metaLaminarHeight
  exact Nat.add_le_add_right (Nat.le_add_right streamLayers backendLayers) 1

theorem metaLaminarHeight_ge_backendLayers_succ
    (streamLayers backendLayers : Nat) :
    backendLayers + 1 <= metaLaminarHeight streamLayers backendLayers := by
  unfold metaLaminarHeight
  exact Nat.add_le_add_right (Nat.le_add_left backendLayers streamLayers) 1

theorem metaLaminarHeight_eq_one_iff
    (streamLayers backendLayers : Nat) :
    metaLaminarHeight streamLayers backendLayers = 1 ↔
      streamLayers = 0 ∧ backendLayers = 0 := by
  unfold metaLaminarHeight
  constructor
  · intro h_height
    have h_sum : streamLayers + backendLayers = 0 :=
      Nat.add_right_cancel (h_height.trans (Nat.zero_add 1).symm)
    have h_stream : streamLayers = 0 := Nat.eq_zero_of_add_eq_zero_right h_sum
    have h_backend : backendLayers = 0 := Nat.eq_zero_of_add_eq_zero_left h_sum
    exact ⟨h_stream, h_backend⟩
  · rintro ⟨rfl, rfl⟩
    simp

end Gnosis