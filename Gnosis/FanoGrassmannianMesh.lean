import Init
import Gnosis.FanoIncidence
import Gnosis.AmplituhedronGrassmannian
import Gnosis.AeonStandingWaveCoordinateBridge

/-!
# Fano incidence inside the `Gr(2,12)` mesh

This module embeds the seven Fano points into the first seven columns of the
Aeon-12 carrier and reads every distinct Fano pair as a valid `Gr(2,12)`
Plucker gate. The incidence completion theorem then gives the structured third
point associated with a pair collision.
-/

namespace Gnosis
namespace FanoGrassmannianMesh

open Gnosis.FanoIncidence
open AmplituhedronAttention.Grassmannian

/-- First McKay coefficient / Griess-plus-trivial dimension used as the
finite Monster-side carrier size in this bounded projection. -/
def monsterMoonshineDim : Nat := 196884

/-- The Monster-side carrier tiles exactly into Aeon-12 phase blocks. -/
def monsterAeonBlocks : Nat := 16407

theorem monsterMoonshineDim_eq_ambient_blocks :
    monsterMoonshineDim =
      Gnosis.AeonStandingWaveCoordinateBridge.ambientDim * monsterAeonBlocks := by
  native_decide

/-- Project a Monster-side column into the Aeon-12 phase carrier. -/
def monsterColumnPhase (column : Nat) : Nat :=
  column % Gnosis.AeonStandingWaveCoordinateBridge.ambientDim

/-- Project a Monster-side unordered pair into the 66 Aeon pair labels when
the two Monster columns land on distinct Aeon phases. Same-phase pairs collapse
to no `Gr(2,12)` gate at this resolution. -/
def monsterPairAeonGate (a b : Nat) : Option (List Nat) :=
  let i := monsterColumnPhase a
  let j := monsterColumnPhase b
  if i = j then none else some (if i < j then [i, j] else [j, i])

def aeonPhaseFanoState : Nat → Option TritonState
  | 0 => some FanoPoint.b001.state
  | 1 => some FanoPoint.b010.state
  | 2 => some FanoPoint.b011.state
  | 3 => some FanoPoint.b100.state
  | 4 => some FanoPoint.b101.state
  | 5 => some FanoPoint.b110.state
  | 6 => some FanoPoint.b111.state
  | _ => none

/-- Portable finite certificate for a Monster column pair that has first been
projected into the Aeon-12 phase carrier and then admitted only when the two
phases are inside the embedded seven-point Fano subatlas. -/
structure MonsterAeonFanoCertificate where
  monsterColumns : List Nat
  aeonPhases : List Nat
  aeonGate : List Nat
  fanoStates : List TritonState
  completion : TritonState
  orientationSign : Int
  positiveGate : Bool
  residualValidated : Bool
  fingerprintVerified : Bool
deriving DecidableEq

/-- Runtime adapter for the 12-step Aeon boundary. It can project every Monster
column pair to Aeon phases, but emits a Fano XOR certificate only for validated
phase pairs in the first seven Aeon columns. -/
def monsterAeonFanoCertificate
    (a b : Nat) (residualValidated fingerprintVerified : Bool) :
    Option MonsterAeonFanoCertificate :=
  let i := monsterColumnPhase a
  let j := monsterColumnPhase b
  match monsterPairAeonGate a b, aeonPhaseFanoState i, aeonPhaseFanoState j with
  | some gate, some lhs, some rhs =>
      if residualValidated && fingerprintVerified then
        some {
          monsterColumns := [a, b]
          aeonPhases := [i, j]
          aeonGate := gate
          fanoStates := [lhs, rhs]
          completion := collide lhs rhs
          orientationSign := if i < j then 1 else -1
          positiveGate := true
          residualValidated := residualValidated
          fingerprintVerified := fingerprintVerified
        }
      else none
  | _, _, _ => none

theorem monster_aeon_fano_certificate_admits_visible_phase_pair :
    monsterAeonFanoCertificate 0 13 true true =
      some {
        monsterColumns := [0, 13]
        aeonPhases := [0, 1]
        aeonGate := [0, 1]
        fanoStates := [FanoPoint.b001.state, FanoPoint.b010.state]
        completion := FanoPoint.b011.state
        orientationSign := 1
        positiveGate := true
        residualValidated := true
        fingerprintVerified := true
      } ∧
    monsterAeonFanoCertificate 0 12 true true = none ∧
    monsterAeonFanoCertificate 6 19 true true = none ∧
    monsterAeonFanoCertificate 0 13 true false = none := by
  native_decide

theorem monster_to_aeon_projection_targets_sixty_six :
    monsterMoonshineDim =
      Gnosis.AeonStandingWaveCoordinateBridge.ambientDim * monsterAeonBlocks ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 := by
  exact ⟨monsterMoonshineDim_eq_ambient_blocks, by native_decide⟩

/-- Embed the seven Fano points into the first seven Aeon-12 columns. -/
def fanoColumn (p : FanoPoint) : Nat :=
  pointIndex p

theorem fanoColumn_lt_twelve (p : FanoPoint) : fanoColumn p < 12 := by
  have h7 : fanoColumn p < 7 := pointIndex_lt_seven p
  exact Nat.lt_trans h7 (by decide)

/-- Sorted two-column Plucker gate associated with a Fano pair. -/
def fanoPairGate (a b : FanoPoint) : List Nat :=
  let i := fanoColumn a
  let j := fanoColumn b
  if i < j then [i, j] else [j, i]

/-- Oriented two-column Plucker label before canonical sorting. -/
def orientedFanoPairGate (a b : FanoPoint) : List Nat :=
  [fanoColumn a, fanoColumn b]

/-- The sign needed to recover the oriented Plucker label from the sorted
Fano pair gate. Distinct Fano points have distinct columns, so swapping the
orientation flips this sign. -/
def fanoPairOrientationSign (a b : FanoPoint) : Int :=
  if fanoColumn a < fanoColumn b then 1 else -1

/-- Positivity bit for the canonical sorted Fano gate. Orientation signs are
tracked separately; the sorted gate itself is the positive representative. -/
def fanoPositiveGateBit (_a _b : FanoPoint) : Bool :=
  true

/-- Runtime certificate for the finite Fano Plucker-sign shadow. It records
the unsorted/oriented label, the canonical sorted gate, one orientation sign
bit, and the XOR completion state. -/
structure FanoOrientedPairRuntimeCertificate where
  orientedGate : List Nat
  sortedGate : List Nat
  orientationSign : Int
  positiveGate : Bool
  completion : TritonState

/-- A finite residual fingerprint after higher-field residual math has already
been projected outside this module. The Fano runtime only sees the three-bit
carrier state and whether the external fingerprint was validated. -/
structure FanoResidualShadowCertificate where
  fingerprint : TritonState
  validated : Bool
  visibleSeed : Bool
  routedSeed : TritonState

/-- Compute the runtime certificate directly from a Fano pair. -/
def fanoOrientedPairRuntimeCertificate
    (a b : FanoPoint) : FanoOrientedPairRuntimeCertificate where
  orientedGate := orientedFanoPairGate a b
  sortedGate := fanoPairGate a b
  orientationSign := fanoPairOrientationSign a b
  positiveGate := fanoPositiveGateBit a b
  completion := collide a.state b.state

/-- Lower an already-finite residual fingerprint into the Fano runtime. The
root fingerprint remains outside the visible route; every non-root fingerprint
is a visible XOR seed. -/
def fanoResidualShadowCertificate
    (fingerprint : TritonState) (validated : Bool) : FanoResidualShadowCertificate where
  fingerprint := fingerprint
  validated := validated
  visibleSeed := fingerprint.val != 0
  routedSeed := fingerprint

theorem fanoPairOrientationSign_square (a b : FanoPoint) :
    fanoPairOrientationSign a b * fanoPairOrientationSign a b = 1 := by
  cases a <;> cases b <;> native_decide

theorem fanoPositiveGateBit_true (a b : FanoPoint) :
    fanoPositiveGateBit a b = true := rfl

theorem fanoResidualShadowCertificate_routes_validated_visible_seed
    (fingerprint : TritonState) (hvis : (fingerprint.val != 0) = true) :
    let cert := fanoResidualShadowCertificate fingerprint true
    cert.validated = true ∧
    cert.visibleSeed = true ∧
    cert.routedSeed = fingerprint ∧
    collide cert.routedSeed godPosition = fingerprint := by
  revert fingerprint
  native_decide

theorem fanoResidualShadowCertificate_rejects_root_seed :
    let cert := fanoResidualShadowCertificate godPosition true
    cert.visibleSeed = false ∧
    cert.routedSeed = godPosition := by
  native_decide

theorem fanoPairGate_length (a b : FanoPoint) :
    (fanoPairGate a b).length = 2 := by
  unfold fanoPairGate
  by_cases h : fanoColumn a < fanoColumn b <;> simp [h]

theorem fanoPairGate_mem_gr_2_12 (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim := by
  cases a <;> cases b <;>
    simp [fanoPairGate, fanoColumn, pointIndex, Gnosis.AeonStandingWaveCoordinateBridge.ambientDim,
      Gnosis.Circadian.aeon, kSubsets] at hab ⊢

/-- The coordinate `2`-plane spanned by the oriented Fano pair inside the
Aeon-12 ambient column space. This is the local Plucker chart whose support
will collapse to the sorted Fano pair gate. -/
def fanoPairCoordinatePlane (a b : FanoPoint) :
    KPlane 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim :=
  coordinatePlane 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim
    (orientedFanoPairGate a b) rfl

theorem fanoPairCoordinatePlane_shape (a b : FanoPoint) :
    (fanoPairCoordinatePlane a b).rows.length = 2 ∧
      ∀ row ∈ (fanoPairCoordinatePlane a b).rows,
        row.length = Gnosis.AeonStandingWaveCoordinateBridge.ambientDim :=
  KPlane.shape (fanoPairCoordinatePlane a b)

/-- At the sorted Fano pair gate, the pair coordinate plane's Plucker
coordinate is exactly the one-bit orientation sign. -/
theorem fanoPairCoordinatePlane_plucker_gate_sign
    (a b : FanoPoint) (hab : a ≠ b) :
    pluckerCoord (fanoPairCoordinatePlane a b) (fanoPairGate a b) =
      fanoPairOrientationSign a b := by
  cases a <;> cases b <;> first | contradiction | native_decide

/-- Across the full 66-label `Gr(2,12)` stack, the oriented Fano pair
coordinate plane has nonzero Plucker support exactly at its sorted Fano pair
gate. -/
theorem fanoPairCoordinatePlane_plucker_support_iff
    (a b : FanoPoint) (hab : a ≠ b) (cols : List Nat)
    (hcols : cols ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim) :
    pluckerCoord (fanoPairCoordinatePlane a b) cols ≠ 0 ↔
      cols = fanoPairGate a b := by
  cases a <;> cases b <;> first | contradiction | (revert cols hcols; native_decide)

/-- Equivalent value form of support collapse: every 66-stack Plucker
coordinate is either the pair's one-bit orientation sign at the sorted Fano
gate, or zero off that gate. -/
theorem fanoPairCoordinatePlane_plucker_value_collapse
    (a b : FanoPoint) (hab : a ≠ b) (cols : List Nat)
    (hcols : cols ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim) :
    pluckerCoord (fanoPairCoordinatePlane a b) cols =
      if cols = fanoPairGate a b then fanoPairOrientationSign a b else 0 := by
  cases a <;> cases b <;> first | contradiction | (revert cols hcols; native_decide)

/-- Runtime-facing support bit: forget the Plucker magnitude/sign and keep only
whether the coordinate is nonzero. -/
def pluckerSupportBit {k d : Nat} (p : KPlane k d) (cols : List Nat) : Bool :=
  decide (pluckerCoord p cols ≠ 0)

/-- For a Fano pair coordinate plane, the runtime support bit on the 66-label
stack is exactly equality with the sorted Fano pair gate. -/
theorem fanoPairCoordinatePlane_supportBit_eq_gate
    (a b : FanoPoint) (hab : a ≠ b) (cols : List Nat)
    (hcols : cols ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim) :
    pluckerSupportBit (fanoPairCoordinatePlane a b) cols =
      decide (cols = fanoPairGate a b) := by
  cases a <;> cases b <;> first | contradiction | (revert cols hcols; native_decide)

/-- Plucker-sign shadow certificate: swapping a distinct Fano pair flips the
orientation sign, but preserves the sorted `Gr(2,12)` gate and the XOR
completion. This is the first finite boundary where a Plucker sign can be
handled as one sign bit beside the XOR route, rather than as a full
Grassmannian transform. -/
theorem fano_plucker_sign_shadow_certificate (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairGate a b = fanoPairGate b a ∧
    completePair a b = completePair b a ∧
    collide a.state b.state = collide b.state a.state ∧
    fanoPairOrientationSign b a = -fanoPairOrientationSign a b := by
  cases a <;> cases b <;>
    simp [fanoPairGate, fanoPairOrientationSign, fanoColumn, pointIndex,
      completePair, collide, tritonXor, xorNat, FanoPoint.state] at hab ⊢

/-- Partial inverse from the first seven Aeon columns back to visible Fano
points. Columns outside the embedded Fano subatlas have no XOR shadow here. -/
def fanoColumnPoint : Nat → Option FanoPoint
  | 0 => some FanoPoint.b001
  | 1 => some FanoPoint.b010
  | 2 => some FanoPoint.b011
  | 3 => some FanoPoint.b100
  | 4 => some FanoPoint.b101
  | 5 => some FanoPoint.b110
  | 6 => some FanoPoint.b111
  | _ => none

theorem fanoColumnPoint_fanoColumn (p : FanoPoint) :
    fanoColumnPoint (fanoColumn p) = some p := by
  cases p <;> rfl

/-- Decode a Monster-side column through its Aeon-12 phase into the embedded
first-seven Fano subatlas, when that phase is Fano-visible. -/
def monsterColumnFanoPoint (column : Nat) : Option FanoPoint :=
  fanoColumnPoint (monsterColumnPhase column)

/-- Runtime-visible Aeon phases are exactly the first-seven phases that decode
to a Fano point. -/
def aeonPhaseFanoVisible (phase : Nat) : Bool :=
  (fanoColumnPoint phase).isSome

/-- Monster columns are Fano-visible when their Aeon-12 phase lands in the
embedded first-seven Fano subatlas. -/
def monsterColumnFanoVisible (column : Nat) : Bool :=
  aeonPhaseFanoVisible (monsterColumnPhase column)

/-- Decode a Monster-side column pair into Fano endpoints when both Aeon phases
land in the embedded first-seven Fano subatlas. -/
def monsterPairFanoPoints (a b : Nat) : Option (FanoPoint × FanoPoint) :=
  match monsterColumnFanoPoint a, monsterColumnFanoPoint b with
  | some x, some y => some (x, y)
  | _, _ => none

/-- Monster-side Fano label projection: a decoded distinct Fano endpoint pair
lowers to its sorted embedded Fano Plucker gate. -/
def monsterPairFanoGate (a b : Nat) : Option (List Nat) :=
  match monsterPairFanoPoints a b with
  | some (x, y) => if x ≠ y then some (fanoPairGate x y) else none
  | none => none

theorem monsterPairFanoPoints_eq_some_of_phases
    (m n : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b) :
    monsterPairFanoPoints m n = some (a, b) := by
  simp [monsterPairFanoPoints, monsterColumnFanoPoint, hm, hn,
    fanoColumnPoint_fanoColumn]

theorem monsterPairFanoPoints_decode_visible
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) :
    monsterColumnFanoVisible m = true ∧
      monsterColumnFanoVisible n = true := by
  cases hm : fanoColumnPoint (monsterColumnPhase m) <;>
    cases hn : fanoColumnPoint (monsterColumnPhase n) <;>
    simp [monsterPairFanoPoints, monsterColumnFanoPoint, monsterColumnFanoVisible,
      aeonPhaseFanoVisible, hm, hn] at hdecode ⊢

/-- Decode a two-column label in the embedded first-seven Fano subatlas back
to its ordered endpoint pair. Labels outside the embedded subatlas do not
produce a Fano runtime pair. -/
def fanoGatePoints : List Nat → Option (FanoPoint × FanoPoint)
  | [i, j] =>
      match fanoColumnPoint i, fanoColumnPoint j with
      | some a, some b => some (a, b)
      | _, _ => none
  | _ => none

theorem fanoGatePoints_fanoPairGate_isSome (a b : FanoPoint) (hab : a ≠ b) :
    (fanoGatePoints (fanoPairGate a b)).isSome = true := by
  cases a <;> cases b <;> first | contradiction | native_decide

/-- Every valid two-label in the embedded `Gr(2,7)` Fano subatlas decodes to a
distinct Fano pair. -/
theorem fanoGatePoints_decodes_embedded_pair_label_isSome
    (gate : List Nat) (hgate : gate ∈ kSubsets 2 7) :
    (fanoGatePoints gate).isSome = true := by
  revert gate
  native_decide

/-- Finite XOR shadow of an embedded pair label. For a two-column label inside
the first seven columns, decode both Fano points and collide their Triton
states. Other labels are outside this finite Fano shadow. -/
def fanoGateXorShadow : List Nat → Option TritonState
  | [i, j] =>
      match fanoColumnPoint i, fanoColumnPoint j with
      | some a, some b => some (collide a.state b.state)
      | _, _ => none
  | _ => none

theorem fanoGateXorShadow_fanoPairGate (a b : FanoPoint) :
    fanoGateXorShadow (fanoPairGate a b) = some (collide a.state b.state) := by
  cases a <;> cases b <;> native_decide

theorem fanoGateXorShadow_fanoPairGate_completion
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoGateXorShadow (fanoPairGate a b) = some (completePair a b).state := by
  rw [fanoGateXorShadow_fanoPairGate, completePair_state_eq_xor a b hab]

/-- Runtime XOR adapter: erase Plucker signs/magnitudes to a support bit, then
emit the Fano XOR shadow only on supported gates. -/
def fanoPairPluckerXorRuntimeShadow
    (a b : FanoPoint) (cols : List Nat) : Option TritonState :=
  if pluckerSupportBit (fanoPairCoordinatePlane a b) cols then
    fanoGateXorShadow cols
  else
    none

/-- Runtime certificate emitted for one candidate Plucker label. The `support`
bit is the sign-erased Plucker coordinate; `xorShadow` is present only when the
runtime adapter keeps the label. -/
structure FanoPairXorRuntimeCertificate where
  gate : List Nat
  support : Bool
  xorShadow : Option TritonState

/-- Compute the sign-erased XOR runtime certificate for one candidate label. -/
def fanoPairXorRuntimeCertificate
    (a b : FanoPoint) (cols : List Nat) : FanoPairXorRuntimeCertificate where
  gate := cols
  support := pluckerSupportBit (fanoPairCoordinatePlane a b) cols
  xorShadow := fanoPairPluckerXorRuntimeShadow a b cols

/-- Pair-collision bridge: a distinct Fano pair gives a valid `Gr(2,12)`
pair gate plus the unique Fano incidence completion. -/
theorem fano_collision_has_grassmannian_gate_and_completion
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
    ∃ c,
      c ≠ a ∧ c ≠ b ∧ fanoLine a b c ∧
        ∀ d, d ≠ a → d ≠ b → fanoLine a b d → d = c := by
  exact ⟨fanoPairGate_mem_gr_2_12 a b hab, distinct_pair_has_unique_completion a b hab⟩

/-- Fano-to-Grassmannian parity certificate: a distinct Fano line gives a
valid embedded `Gr(2,12)` pair gate, and the three line points have zero total
XOR parity in the Triton carrier. This is a finite-shadow statement about the
embedded gate, not a claim that all Plucker structure reduces to XOR. -/
theorem fano_grassmannian_gate_has_xor_parity_certificate
    (a b c : FanoPoint) (hab : a ≠ b) (hline : fanoLine a b c) :
    fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
    collide (collide a.state b.state) c.state = godPosition := by
  exact ⟨fanoPairGate_mem_gr_2_12 a b hab,
    fanoLine_xor_parity_zero a b c hline⟩

/-- Gate-shadow line certificate: the embedded `Gr(2,12)` pair label decodes
through the finite Fano XOR shadow to the line completion point, and the three
carrier states fold back to the root by total XOR parity. -/
theorem fano_grassmannian_gate_shadow_recovers_line
    (a b c : FanoPoint) (hab : a ≠ b) (hline : fanoLine a b c) :
    fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
    fanoGateXorShadow (fanoPairGate a b) = some c.state ∧
    collide (collide a.state b.state) c.state = godPosition := by
  have hstate := fanoLine_state_eq_xor a b c hline
  refine ⟨fanoPairGate_mem_gr_2_12 a b hab, ?_, fanoLine_xor_parity_zero a b c hline⟩
  rw [fanoGateXorShadow_fanoPairGate, ← hstate]

/-- Pair-gate support law: each distinct embedded Fano pair is a length-2
`Gr(2,12)` label whose canonical completion is exactly the Triton XOR of the
pair, and the resulting three-state line has zero total XOR parity. -/
theorem fano_pair_gate_xor_support_law (a b : FanoPoint) (hab : a ≠ b) :
    (fanoPairGate a b).length = 2 ∧
    fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
    (completePair a b).state = collide a.state b.state ∧
    collide (collide a.state b.state) (completePair a b).state = godPosition := by
  exact ⟨fanoPairGate_length a b, fanoPairGate_mem_gr_2_12 a b hab,
    completePair_state_eq_xor a b hab, completePair_xor_parity_zero a b hab⟩

/-- Plucker-to-XOR reduction certificate for a single Fano pair coordinate
plane: the full `Gr(2,12)` Plucker stack has exactly one nonzero support gate,
that gate carries only the orientation sign, and the same gate's finite shadow
decodes to the XOR completion with zero total carrier parity. -/
theorem fanoPairCoordinatePlane_plucker_reduces_to_xor
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
    pluckerCoord (fanoPairCoordinatePlane a b) (fanoPairGate a b) =
      fanoPairOrientationSign a b ∧
    (∀ cols,
      cols ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim →
        (pluckerCoord (fanoPairCoordinatePlane a b) cols ≠ 0 ↔
          cols = fanoPairGate a b)) ∧
    fanoGateXorShadow (fanoPairGate a b) = some (completePair a b).state ∧
    collide (collide a.state b.state) (completePair a b).state = godPosition := by
  exact ⟨fanoPairGate_mem_gr_2_12 a b hab,
    fanoPairCoordinatePlane_plucker_gate_sign a b hab,
    fun cols hcols => fanoPairCoordinatePlane_plucker_support_iff a b hab cols hcols,
    fanoGateXorShadow_fanoPairGate_completion a b hab,
    completePair_xor_parity_zero a b hab⟩

/-- Pair-level XOR runtime reduction: over the 66-label stack, the sign-erased
runtime adapter emits exactly the Fano XOR completion at the supported gate and
emits nothing everywhere else. -/
theorem fanoPairCoordinatePlane_runtime_reduces_to_xor
    (a b : FanoPoint) (hab : a ≠ b) (cols : List Nat)
    (hcols : cols ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim) :
    fanoPairPluckerXorRuntimeShadow a b cols =
      if cols = fanoPairGate a b then some (completePair a b).state else none := by
  cases a <;> cases b <;> first | contradiction | (revert cols hcols; native_decide)

/-- Certificate form of the same runtime reduction. -/
theorem fanoPairXorRuntimeCertificate_reduces_to_xor
    (a b : FanoPoint) (hab : a ≠ b) (cols : List Nat)
    (hcols : cols ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim) :
    let cert := fanoPairXorRuntimeCertificate a b cols
    cert.gate = cols ∧
    cert.support = decide (cols = fanoPairGate a b) ∧
    cert.xorShadow =
      if cols = fanoPairGate a b then some (completePair a b).state else none := by
  exact ⟨rfl, fanoPairCoordinatePlane_supportBit_eq_gate a b hab cols hcols,
    fanoPairCoordinatePlane_runtime_reduces_to_xor a b hab cols hcols⟩

/-- Full 66-label runtime stack for a Fano pair coordinate plane. Each output
slot corresponds to one `Gr(2,12)` Plucker label after sign/magnitude erasure. -/
def fanoPairXorRuntimeStack (a b : FanoPoint) : List (Option TritonState) :=
  (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).map
    (fanoPairPluckerXorRuntimeShadow a b)

/-- Canonical XOR-only 66-label runtime stack. This contains no Plucker
coordinate computation: it keeps only a chosen two-column gate and the Triton
completion payload routed at that gate. -/
def fanoCanonicalXorRuntimeStack
    (gate : List Nat) (completion : TritonState) : List (Option TritonState) :=
  (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).map
    (fun cols => if cols = gate then some completion else none)

/-- Count emitted runtime payloads, ignoring `none` slots. -/
def optionPayloadCount {α : Type} : List (Option α) → Nat :=
  List.foldl (fun n x => match x with | some _ => n + 1 | none => n) 0

theorem fanoPairXorRuntimeStack_length (a b : FanoPoint) :
    (fanoPairXorRuntimeStack a b).length = 66 := by
  unfold fanoPairXorRuntimeStack
  rw [List.length_map]
  native_decide

theorem fanoCanonicalXorRuntimeStack_length
    (gate : List Nat) (completion : TritonState) :
    (fanoCanonicalXorRuntimeStack gate completion).length = 66 := by
  unfold fanoCanonicalXorRuntimeStack
  rw [List.length_map]
  native_decide

/-- The Plucker-derived runtime stack for a distinct Fano pair is exactly the
canonical XOR-only stack selected by the pair gate and its XOR completion. -/
theorem fanoPairXorRuntimeStack_eq_canonical_xor
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairXorRuntimeStack a b =
      fanoCanonicalXorRuntimeStack (fanoPairGate a b) (completePair a b).state := by
  cases a <;> cases b <;> first | contradiction | native_decide

/-- Pair-specialized canonical XOR stack: the sorted Fano gate selects exactly
the XOR completion payload. -/
def fanoPairCanonicalXorRuntimeStack
    (a b : FanoPoint) : List (Option TritonState) :=
  fanoCanonicalXorRuntimeStack (fanoPairGate a b) (completePair a b).state

theorem fanoPairXorRuntimeStack_eq_pair_canonical_xor
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairXorRuntimeStack a b = fanoPairCanonicalXorRuntimeStack a b := by
  exact fanoPairXorRuntimeStack_eq_canonical_xor a b hab

theorem fanoPairCanonicalXorRuntimeStack_length (a b : FanoPoint) :
    (fanoPairCanonicalXorRuntimeStack a b).length = 66 := by
  exact fanoCanonicalXorRuntimeStack_length (fanoPairGate a b) (completePair a b).state

/-- Label-indexed canonical XOR runtime dispatch. This adapter starts from a
candidate `Gr(2,12)` label, decodes it through the finite Fano subatlas, and
returns the pair-canonical XOR-only 66-slot stack when the label is Fano-visible
and has distinct decoded endpoints. -/
def fanoLabelCanonicalXorRuntimeStack
    (gate : List Nat) : Option (List (Option TritonState)) :=
  match fanoGatePoints gate with
  | some (a, b) =>
      if a ≠ b then some (fanoPairCanonicalXorRuntimeStack a b) else none
  | none => none

/-- Monster-side XOR runtime dispatch through the Fano subatlas. -/
def monsterPairFanoXorRuntimeStack
    (a b : Nat) : Option (List (Option TritonState)) :=
  match monsterPairFanoPoints a b with
  | some (x, y) =>
      if x ≠ y then some (fanoPairCanonicalXorRuntimeStack x y) else none
  | none => none

theorem fanoLabelCanonicalXorRuntimeStack_fanoPairGate
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoLabelCanonicalXorRuntimeStack (fanoPairGate a b) =
      some (fanoPairCanonicalXorRuntimeStack a b) := by
  cases a <;> cases b <;> first | contradiction | native_decide

/-- Label-indexed runtime dispatch is defined on every valid embedded Fano pair
label, with no caller-supplied Fano points. -/
theorem fanoLabelCanonicalXorRuntimeStack_decodes_embedded_pair_label_isSome
    (gate : List Nat) (hgate : gate ∈ kSubsets 2 7) :
    (fanoLabelCanonicalXorRuntimeStack gate).isSome = true := by
  revert gate
  native_decide

theorem fanoLabelCanonicalXorRuntimeStack_decoded_length
    (gate : List Nat) (_hgate : gate ∈ kSubsets 2 7)
    (stack : List (Option TritonState))
    (hstack : fanoLabelCanonicalXorRuntimeStack gate = some stack) :
    stack.length = 66 := by
  unfold fanoLabelCanonicalXorRuntimeStack at hstack
  cases hdecode : fanoGatePoints gate with
  | none => simp [hdecode] at hstack
  | some pair =>
      cases pair with
      | mk a b =>
          by_cases hab : a ≠ b
          · simp [hdecode, hab] at hstack
            rw [← hstack]
            exact fanoPairCanonicalXorRuntimeStack_length a b
          · simp [hdecode, hab] at hstack

theorem fanoPairXorRuntimeStack_gate_payload
    (a b : FanoPoint) (hab : a ≠ b) :
    some (completePair a b).state ∈ fanoPairXorRuntimeStack a b := by
  unfold fanoPairXorRuntimeStack
  apply List.mem_map.mpr
  refine ⟨fanoPairGate a b, fanoPairGate_mem_gr_2_12 a b hab, ?_⟩
  simpa using
    fanoPairCoordinatePlane_runtime_reduces_to_xor a b hab (fanoPairGate a b)
      (fanoPairGate_mem_gr_2_12 a b hab)

/-- The full 66-label runtime stack emits exactly one payload. -/
theorem fanoPairXorRuntimeStack_payload_count_one
    (a b : FanoPoint) (hab : a ≠ b) :
    optionPayloadCount (fanoPairXorRuntimeStack a b) = 1 := by
  cases a <;> cases b <;> first | contradiction | native_decide

/-- Every output in the full runtime stack is either absent or the canonical
XOR completion. There are no wrong payloads. -/
theorem fanoPairXorRuntimeStack_no_wrong_payload
    (a b : FanoPoint) (hab : a ≠ b) (out : Option TritonState)
    (hout : out ∈ fanoPairXorRuntimeStack a b) :
    out = none ∨ out = some (completePair a b).state := by
  unfold fanoPairXorRuntimeStack at hout
  obtain ⟨cols, hcols, hout_eq⟩ := List.mem_map.mp hout
  rw [← hout_eq]
  rw [fanoPairCoordinatePlane_runtime_reduces_to_xor a b hab cols hcols]
  by_cases hgate : cols = fanoPairGate a b
  · right
    simp [hgate]
  · left
    simp [hgate]

theorem fanoPairCanonicalXorRuntimeStack_payload_count_one
    (a b : FanoPoint) (hab : a ≠ b) :
    optionPayloadCount (fanoPairCanonicalXorRuntimeStack a b) = 1 := by
  rw [← fanoPairXorRuntimeStack_eq_pair_canonical_xor a b hab]
  exact fanoPairXorRuntimeStack_payload_count_one a b hab

theorem fanoPairCanonicalXorRuntimeStack_gate_payload
    (a b : FanoPoint) (hab : a ≠ b) :
    some (completePair a b).state ∈ fanoPairCanonicalXorRuntimeStack a b := by
  rw [← fanoPairXorRuntimeStack_eq_pair_canonical_xor a b hab]
  exact fanoPairXorRuntimeStack_gate_payload a b hab

theorem fanoPairCanonicalXorRuntimeStack_no_wrong_payload
    (a b : FanoPoint) (hab : a ≠ b) (out : Option TritonState)
    (hout : out ∈ fanoPairCanonicalXorRuntimeStack a b) :
    out = none ∨ out = some (completePair a b).state := by
  rw [← fanoPairXorRuntimeStack_eq_pair_canonical_xor a b hab] at hout
  exact fanoPairXorRuntimeStack_no_wrong_payload a b hab out hout

/-- Any visible payload emitted by the canonical XOR stack closes the original
pair back to the root by total XOR parity. -/
theorem fanoPairCanonicalXorRuntimeStack_payload_parity_zero
    (a b : FanoPoint) (hab : a ≠ b) (payload : TritonState)
    (hout : some payload ∈ fanoPairCanonicalXorRuntimeStack a b) :
    collide (collide a.state b.state) payload = godPosition := by
  have h := fanoPairCanonicalXorRuntimeStack_no_wrong_payload a b hab (some payload) hout
  rcases h with hnone | hsome
  · cases hnone
  · have hpayload : payload = (completePair a b).state := by
      exact Option.some.inj hsome
    rw [hpayload]
    exact completePair_xor_parity_zero a b hab

/-- Full payload law for label-indexed runtime dispatch: any returned stack
comes from a distinct decoded Fano pair, has exactly one payload, contains the
decoded pair's XOR completion, emits no wrong payload, and every visible payload
closes total XOR parity back to the root. -/
theorem fanoLabelCanonicalXorRuntimeStack_payload_law
    (gate : List Nat) (stack : List (Option TritonState))
    (hstack : fanoLabelCanonicalXorRuntimeStack gate = some stack) :
    ∃ a b,
      fanoGatePoints gate = some (a, b) ∧
      a ≠ b ∧
      optionPayloadCount stack = 1 ∧
      some (completePair a b).state ∈ stack ∧
      (∀ out, out ∈ stack → out = none ∨ out = some (completePair a b).state) ∧
      ∀ payload,
        some payload ∈ stack →
          collide (collide a.state b.state) payload = godPosition := by
  unfold fanoLabelCanonicalXorRuntimeStack at hstack
  cases hdecode : fanoGatePoints gate with
  | none => simp [hdecode] at hstack
  | some pair =>
      cases pair with
      | mk a b =>
          by_cases hab : a ≠ b
          · simp [hdecode, hab] at hstack
            refine ⟨a, b, rfl, hab, ?_, ?_, ?_, ?_⟩
            · rw [← hstack]
              exact fanoPairCanonicalXorRuntimeStack_payload_count_one a b hab
            · rw [← hstack]
              exact fanoPairCanonicalXorRuntimeStack_gate_payload a b hab
            · intro out hout
              rw [← hstack] at hout
              exact fanoPairCanonicalXorRuntimeStack_no_wrong_payload a b hab out hout
            · intro payload hout
              rw [← hstack] at hout
              exact fanoPairCanonicalXorRuntimeStack_payload_parity_zero a b hab payload hout
          · simp [hdecode, hab] at hstack

/-- Monster-side payload law: any returned Fano XOR runtime stack comes from a
distinct decoded Fano endpoint pair, has one payload, emits no wrong payloads,
and closes payload parity to the root. -/
theorem monsterPairFanoXorRuntimeStack_payload_law
    (m n : Nat) (stack : List (Option TritonState))
    (hstack : monsterPairFanoXorRuntimeStack m n = some stack) :
    ∃ a b,
      monsterPairFanoPoints m n = some (a, b) ∧
      a ≠ b ∧
      optionPayloadCount stack = 1 ∧
      some (completePair a b).state ∈ stack ∧
      (∀ out, out ∈ stack → out = none ∨ out = some (completePair a b).state) ∧
      ∀ payload,
        some payload ∈ stack →
          collide (collide a.state b.state) payload = godPosition := by
  unfold monsterPairFanoXorRuntimeStack at hstack
  cases hdecode : monsterPairFanoPoints m n with
  | none => simp [hdecode] at hstack
  | some pair =>
      cases pair with
      | mk a b =>
          by_cases hab : a ≠ b
          · simp [hdecode, hab] at hstack
            refine ⟨a, b, rfl, hab, ?_, ?_, ?_, ?_⟩
            · rw [← hstack]
              exact fanoPairCanonicalXorRuntimeStack_payload_count_one a b hab
            · rw [← hstack]
              exact fanoPairCanonicalXorRuntimeStack_gate_payload a b hab
            · intro out hout
              rw [← hstack] at hout
              exact fanoPairCanonicalXorRuntimeStack_no_wrong_payload a b hab out hout
            · intro payload hout
              rw [← hstack] at hout
              exact fanoPairCanonicalXorRuntimeStack_payload_parity_zero a b hab payload hout
          · simp [hdecode, hab] at hstack

/-- If two Monster columns project to distinct embedded Fano phases, the
generic Aeon pair gate is exactly the sorted Fano pair gate. This closes the
gap between phase projection and the Fano/XOR runtime label. -/
theorem monsterPairAeonGate_eq_fanoPairGate_of_phases
    (m n : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b) (hab : a ≠ b) :
    monsterPairAeonGate m n = some (fanoPairGate a b) := by
  unfold monsterPairAeonGate fanoPairGate
  rw [hm, hn]
  cases a <;> cases b <;> simp [fanoColumn, pointIndex] at hab ⊢

theorem monsterPairFanoGate_eq_fanoPairGate_of_decode
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    monsterPairFanoGate m n = some (fanoPairGate a b) := by
  simp [monsterPairFanoGate, hdecode, hab]

theorem monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    monsterPairFanoXorRuntimeStack m n =
      some (fanoPairCanonicalXorRuntimeStack a b) := by
  simp [monsterPairFanoXorRuntimeStack, hdecode, hab]

theorem monsterPairFanoXorRuntimeStack_eq_label_runtime_of_decode
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    monsterPairFanoXorRuntimeStack m n =
      fanoLabelCanonicalXorRuntimeStack (fanoPairGate a b) := by
  rw [monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode m n a b hdecode hab,
    fanoLabelCanonicalXorRuntimeStack_fanoPairGate a b hab]

/-- With explicit phase evidence, the generic Aeon projection, Fano projection,
label dispatch, and Monster runtime dispatch all select the same canonical
XOR-only stack. -/
theorem monster_aeon_gate_to_fano_xor_runtime_bridge
    (m n : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b) (hab : a ≠ b)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) :
    let gate := fanoPairGate a b
    let stack := fanoPairCanonicalXorRuntimeStack a b
    monsterPairAeonGate m n = some gate ∧
      monsterPairFanoGate m n = some gate ∧
      fanoLabelCanonicalXorRuntimeStack gate = some stack ∧
      monsterPairFanoXorRuntimeStack m n = some stack := by
  dsimp
  exact ⟨monsterPairAeonGate_eq_fanoPairGate_of_phases m n a b hm hn hab,
    monsterPairFanoGate_eq_fanoPairGate_of_decode m n a b hdecode hab,
    fanoLabelCanonicalXorRuntimeStack_fanoPairGate a b hab,
    monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode m n a b hdecode hab⟩

/-- Monster/Aeon/Fano/XOR bridge for a Monster-side pair whose Aeon phases
decode to distinct Fano endpoints: the Fano gate, label decoder, pair decoder,
Monster runtime dispatch, stack shape, one payload, payload membership,
no-wrong-payload, and total XOR parity all land on the same canonical XOR-only
runtime stack. -/
theorem monster_to_fano_xor_runtime_certificate
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    let gate := fanoPairGate a b
    let stack := fanoPairCanonicalXorRuntimeStack a b
    monsterMoonshineDim =
        Gnosis.AeonStandingWaveCoordinateBridge.ambientDim * monsterAeonBlocks ∧
      (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
      monsterPairFanoGate m n = some gate ∧
      fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
      (fanoGatePoints gate).isSome = true ∧
      fanoLabelCanonicalXorRuntimeStack gate = some stack ∧
      monsterPairFanoXorRuntimeStack m n = some stack ∧
      stack.length = 66 ∧
      optionPayloadCount stack = 1 ∧
      some (completePair a b).state ∈ stack ∧
      (∀ out, out ∈ stack → out = none ∨ out = some (completePair a b).state) ∧
      ∀ payload,
        some payload ∈ stack →
          collide (collide a.state b.state) payload = godPosition := by
  dsimp
  refine ⟨monsterMoonshineDim_eq_ambient_blocks, by native_decide, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [monsterPairFanoGate, hdecode, hab]
  · exact fanoPairGate_mem_gr_2_12 a b hab
  · exact fanoGatePoints_fanoPairGate_isSome a b hab
  · exact fanoLabelCanonicalXorRuntimeStack_fanoPairGate a b hab
  · simp [monsterPairFanoXorRuntimeStack, hdecode, hab]
  · exact fanoPairCanonicalXorRuntimeStack_length a b
  · exact fanoPairCanonicalXorRuntimeStack_payload_count_one a b hab
  · exact fanoPairCanonicalXorRuntimeStack_gate_payload a b hab
  · intro out hout
    exact fanoPairCanonicalXorRuntimeStack_no_wrong_payload a b hab out hout
  · intro payload hout
    exact fanoPairCanonicalXorRuntimeStack_payload_parity_zero a b hab payload hout

/-- Same runtime certificate with explicit generic Aeon projection evidence:
the generic `monsterPairAeonGate`, the Fano-specific gate, the label runtime
dispatch, and the Monster runtime dispatch all agree on one canonical XOR-only
stack. -/
theorem monster_aeon_projection_to_fano_xor_runtime_certificate
    (m n : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    let gate := fanoPairGate a b
    let stack := fanoPairCanonicalXorRuntimeStack a b
    monsterPairAeonGate m n = some gate ∧
      monsterPairFanoGate m n = some gate ∧
      fanoLabelCanonicalXorRuntimeStack gate = some stack ∧
      monsterPairFanoXorRuntimeStack m n = some stack ∧
      stack.length = 66 ∧
      optionPayloadCount stack = 1 ∧
      some (completePair a b).state ∈ stack ∧
      (∀ out, out ∈ stack → out = none ∨ out = some (completePair a b).state) ∧
      ∀ payload,
        some payload ∈ stack →
          collide (collide a.state b.state) payload = godPosition := by
  dsimp
  have hbridge :=
    monster_aeon_gate_to_fano_xor_runtime_bridge m n a b hm hn hab hdecode
  exact ⟨hbridge.1, hbridge.2.1, hbridge.2.2.1, hbridge.2.2.2,
    fanoPairCanonicalXorRuntimeStack_length a b,
    fanoPairCanonicalXorRuntimeStack_payload_count_one a b hab,
    fanoPairCanonicalXorRuntimeStack_gate_payload a b hab,
    fun out hout => fanoPairCanonicalXorRuntimeStack_no_wrong_payload a b hab out hout,
    fun payload hout => fanoPairCanonicalXorRuntimeStack_payload_parity_zero a b hab payload hout⟩

theorem monster_aeon_projection_to_fano_xor_runtime_certificate_of_phases
    (m n : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b) (hab : a ≠ b) :
    let gate := fanoPairGate a b
    let stack := fanoPairCanonicalXorRuntimeStack a b
    monsterColumnFanoVisible m = true ∧
      monsterColumnFanoVisible n = true ∧
      monsterPairAeonGate m n = some gate ∧
      monsterPairFanoGate m n = some gate ∧
      fanoLabelCanonicalXorRuntimeStack gate = some stack ∧
      monsterPairFanoXorRuntimeStack m n = some stack ∧
      stack.length = 66 ∧
      optionPayloadCount stack = 1 ∧
      some (completePair a b).state ∈ stack ∧
      (∀ out, out ∈ stack → out = none ∨ out = some (completePair a b).state) ∧
      ∀ payload,
        some payload ∈ stack →
          collide (collide a.state b.state) payload = godPosition := by
  dsimp
  have hdecode := monsterPairFanoPoints_eq_some_of_phases m n a b hm hn
  have hvisible := monsterPairFanoPoints_decode_visible m n a b hdecode
  have hcert :=
    monster_aeon_projection_to_fano_xor_runtime_certificate m n a b hm hn hdecode hab
  exact ⟨hvisible.1, hvisible.2, hcert.1, hcert.2.1, hcert.2.2.1,
    hcert.2.2.2.1, hcert.2.2.2.2.1, hcert.2.2.2.2.2.1,
    hcert.2.2.2.2.2.2.1, hcert.2.2.2.2.2.2.2.1,
    hcert.2.2.2.2.2.2.2.2⟩

/-- Atlas form of the Monster-visible phase bridge: any Monster pair whose
Aeon phases are explicitly identified with distinct embedded Fano columns
enters the generic Aeon gate, the Fano label decoder, and the canonical
XOR-only runtime stack with one parity-closing payload. -/
theorem monster_aeon_projection_to_fano_xor_runtime_phase_atlas_certificate :
    monsterMoonshineDim =
        Gnosis.AeonStandingWaveCoordinateBridge.ambientDim * monsterAeonBlocks ∧
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ (m n : Nat) (a b : FanoPoint),
      monsterColumnPhase m = fanoColumn a →
      monsterColumnPhase n = fanoColumn b →
      a ≠ b →
        let gate := fanoPairGate a b
        let stack := fanoPairCanonicalXorRuntimeStack a b
        monsterColumnFanoVisible m = true ∧
          monsterColumnFanoVisible n = true ∧
          monsterPairAeonGate m n = some gate ∧
          monsterPairFanoGate m n = some gate ∧
          fanoLabelCanonicalXorRuntimeStack gate = some stack ∧
          monsterPairFanoXorRuntimeStack m n = some stack ∧
          stack.length = 66 ∧
          optionPayloadCount stack = 1 ∧
          some (completePair a b).state ∈ stack ∧
          (∀ out, out ∈ stack → out = none ∨ out = some (completePair a b).state) ∧
          ∀ payload,
            some payload ∈ stack →
              collide (collide a.state b.state) payload = godPosition := by
  refine ⟨monsterMoonshineDim_eq_ambient_blocks, by native_decide, by native_decide, ?_⟩
  intro m n a b hm hn hab
  exact monster_aeon_projection_to_fano_xor_runtime_certificate_of_phases
    m n a b hm hn hab

theorem fanoPairCanonicalXorRuntimeStack_swap_invariant
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairCanonicalXorRuntimeStack a b =
      fanoPairCanonicalXorRuntimeStack b a := by
  cases a <;> cases b <;> first | contradiction | native_decide

theorem fanoPairXorRuntimeStack_swap_invariant
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairXorRuntimeStack a b = fanoPairXorRuntimeStack b a := by
  rw [fanoPairXorRuntimeStack_eq_pair_canonical_xor a b hab]
  rw [fanoPairXorRuntimeStack_eq_pair_canonical_xor b a (Ne.symm hab)]
  exact fanoPairCanonicalXorRuntimeStack_swap_invariant a b hab

/-- Line form: when `c` is the Fano line completion of a distinct pair, the
Plucker-derived runtime stack is the canonical XOR-only stack carrying `c`. -/
theorem fanoLine_runtime_stack_eq_canonical_xor
    (a b c : FanoPoint) (hab : a ≠ b) (hline : fanoLine a b c) :
    fanoPairXorRuntimeStack a b =
      fanoCanonicalXorRuntimeStack (fanoPairGate a b) c.state := by
  simpa [hline.2] using fanoPairXorRuntimeStack_eq_canonical_xor a b hab

theorem fanoLine_canonical_xor_payload_parity_zero
    (a b c : FanoPoint) (hab : a ≠ b) (hline : fanoLine a b c) :
    some c.state ∈ fanoCanonicalXorRuntimeStack (fanoPairGate a b) c.state ∧
      collide (collide a.state b.state) c.state = godPosition := by
  refine ⟨?_, fanoLine_xor_parity_zero a b c hline⟩
  unfold fanoCanonicalXorRuntimeStack
  cases a <;> cases b <;> cases c <;> first | contradiction | native_decide

/-- Signed shadow bundle: on a distinct Fano pair, the sorted Plucker gate is
orientation-independent, the orientation contribution is a single square-one
sign bit, and the same gate decodes through the XOR shadow to the canonical
completion with zero total carrier parity. -/
theorem fano_plucker_sign_xor_shadow_bundle (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairGate a b = fanoPairGate b a ∧
    fanoPairOrientationSign a b * fanoPairOrientationSign a b = 1 ∧
    fanoPairOrientationSign b a = -fanoPairOrientationSign a b ∧
    fanoGateXorShadow (fanoPairGate a b) = some (completePair a b).state ∧
    collide (collide a.state b.state) (completePair a b).state = godPosition := by
  have hsign := fano_plucker_sign_shadow_certificate a b hab
  exact ⟨hsign.1, fanoPairOrientationSign_square a b, hsign.2.2.2,
    fanoGateXorShadow_fanoPairGate_completion a b hab, completePair_xor_parity_zero a b hab⟩

/-- Runtime-certificate form of the Plucker-sign shadow: every distinct Fano
pair lowers to an oriented two-column label, a sorted `Gr(2,12)` gate, a
square-one orientation sign, and an XOR completion. Swapping the pair preserves
the sorted gate and completion while negating the sign. -/
theorem fano_oriented_pair_runtime_certificate (a b : FanoPoint) (hab : a ≠ b) :
    let cert := fanoOrientedPairRuntimeCertificate a b
    let swapped := fanoOrientedPairRuntimeCertificate b a
    cert.orientedGate = orientedFanoPairGate a b ∧
    cert.sortedGate ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
    cert.sortedGate = swapped.sortedGate ∧
    cert.orientationSign * cert.orientationSign = 1 ∧
    cert.positiveGate = true ∧
    swapped.positiveGate = cert.positiveGate ∧
    swapped.orientationSign = -cert.orientationSign ∧
    cert.completion = collide a.state b.state ∧
    cert.completion = swapped.completion ∧
    cert.completion = (completePair a b).state := by
  have hsign := fano_plucker_sign_shadow_certificate a b hab
  refine ⟨rfl, fanoPairGate_mem_gr_2_12 a b hab, hsign.1,
    fanoPairOrientationSign_square a b, fanoPositiveGateBit_true a b, rfl,
    hsign.2.2.2, rfl, ?_, ?_⟩
  · exact hsign.2.2.1
  · exact (completePair_state_eq_xor a b hab).symm

/-- Finite positivity shadow certificate: canonical sorted Fano gates carry a
positive gate bit, while orientation remains a separate square-one sign bit and
the completion remains the Triton XOR. This is the runtime-admissible positivity
shadow, not a claim about arbitrary positive Grassmannian cells. -/
theorem fano_positive_shadow_certificate (a b : FanoPoint) (hab : a ≠ b) :
    let cert := fanoOrientedPairRuntimeCertificate a b
    cert.sortedGate ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
    cert.positiveGate = true ∧
    cert.orientationSign * cert.orientationSign = 1 ∧
    cert.completion = (completePair a b).state ∧
    fanoGateXorShadow cert.sortedGate = some cert.completion := by
  refine ⟨fanoPairGate_mem_gr_2_12 a b hab, fanoPositiveGateBit_true a b,
    fanoPairOrientationSign_square a b, ?_, ?_⟩
  · exact (completePair_state_eq_xor a b hab).symm
  · exact fanoGateXorShadow_fanoPairGate a b

/-- Atlas-level Fano shadow inside the Aeon `Gr(2,12)` Plucker stack: the
21-gate Fano pair atlas embeds into the 66 ambient pair labels, and every
distinct Fano pair has a unique completion whose three visible states fold to
the root by total XOR parity. -/
theorem fano_grassmannian_xor_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b : FanoPoint, a ≠ b →
      ∃ c,
        c ≠ a ∧ c ≠ b ∧
        fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
        fanoLine a b c ∧
        collide (collide a.state b.state) c.state = godPosition ∧
        ∀ d, d ≠ a → d ≠ b → fanoLine a b d → d = c := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b hab
  obtain ⟨c, hc_ne_a, hc_ne_b, hline, hunique⟩ :=
    distinct_pair_has_unique_completion a b hab
  exact ⟨c, hc_ne_a, hc_ne_b, fanoPairGate_mem_gr_2_12 a b hab, hline,
    fanoLine_xor_parity_zero a b c hline, hunique⟩

/-- Atlas-level shadow decoder certificate: over the embedded Fano subatlas,
the `Gr(2,12)` pair label itself decodes to the unique Fano line completion
through `fanoGateXorShadow`, and the decoded line has zero total XOR parity. -/
theorem fano_grassmannian_xor_shadow_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b : FanoPoint, a ≠ b →
      ∃ c,
        c ≠ a ∧ c ≠ b ∧
        fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
        fanoLine a b c ∧
        fanoGateXorShadow (fanoPairGate a b) = some c.state ∧
        collide (collide a.state b.state) c.state = godPosition ∧
        ∀ d, d ≠ a → d ≠ b → fanoLine a b d → d = c := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b hab
  obtain ⟨c, hc_ne_a, hc_ne_b, hline, hunique⟩ :=
    distinct_pair_has_unique_completion a b hab
  have hshadow := fano_grassmannian_gate_shadow_recovers_line a b c hab hline
  exact ⟨c, hc_ne_a, hc_ne_b, hshadow.1, hline, hshadow.2.1, hshadow.2.2, hunique⟩

/-- Signed atlas-level shadow certificate: uniformly across the embedded
21-gate Fano subatlas, every distinct pair has a valid `Gr(2,12)` gate, a
square-one orientation bit that flips under swap, an XOR-shadow decoded
completion, and zero total carrier parity. -/
theorem fano_grassmannian_signed_xor_shadow_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b : FanoPoint, a ≠ b →
      fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
      fanoPairGate a b = fanoPairGate b a ∧
      fanoPairOrientationSign a b * fanoPairOrientationSign a b = 1 ∧
      fanoPairOrientationSign b a = -fanoPairOrientationSign a b ∧
      fanoGateXorShadow (fanoPairGate a b) = some (completePair a b).state ∧
      collide (collide a.state b.state) (completePair a b).state = godPosition := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b hab
  have hsupport := fano_pair_gate_xor_support_law a b hab
  have hbundle := fano_plucker_sign_xor_shadow_bundle a b hab
  exact ⟨hsupport.2.1, hbundle.1, hbundle.2.1, hbundle.2.2.1,
    hbundle.2.2.2.1, hbundle.2.2.2.2⟩

/-- Atlas-level Plucker-to-XOR reduction: for every distinct Fano pair in the
embedded 21-gate subatlas, the pair coordinate plane's full 66-label Plucker
stack has exactly one nonzero support gate, that gate carries only the
orientation sign, and the same gate decodes to the unique Fano XOR completion
with zero total carrier parity. -/
theorem fano_grassmannian_plucker_support_reduces_to_xor_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b : FanoPoint, a ≠ b →
      ∃ c,
        c ≠ a ∧ c ≠ b ∧
        fanoLine a b c ∧
        fanoPairGate a b ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim ∧
        pluckerCoord (fanoPairCoordinatePlane a b) (fanoPairGate a b) =
          fanoPairOrientationSign a b ∧
        (∀ cols,
          cols ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim →
            (pluckerCoord (fanoPairCoordinatePlane a b) cols ≠ 0 ↔
              cols = fanoPairGate a b)) ∧
        fanoGateXorShadow (fanoPairGate a b) = some c.state ∧
        collide (collide a.state b.state) c.state = godPosition ∧
        ∀ d, d ≠ a → d ≠ b → fanoLine a b d → d = c := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b hab
  obtain ⟨c, hc_ne_a, hc_ne_b, hline, hunique⟩ :=
    distinct_pair_has_unique_completion a b hab
  have hreduce := fanoPairCoordinatePlane_plucker_reduces_to_xor a b hab
  have hshadow := fano_grassmannian_gate_shadow_recovers_line a b c hab hline
  exact ⟨c, hc_ne_a, hc_ne_b, hline, hreduce.1, hreduce.2.1,
    hreduce.2.2.1, hshadow.2.1, hshadow.2.2, hunique⟩

/-- Atlas-level XOR runtime reduction: after erasing Plucker signs/magnitudes
to support bits, every candidate label in the 66-label stack lowers to `none`
except the unique Fano pair gate, which lowers to the line's XOR completion. -/
theorem fano_grassmannian_xor_runtime_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b : FanoPoint, a ≠ b →
      ∃ c,
        c ≠ a ∧ c ≠ b ∧
        fanoLine a b c ∧
        ∀ cols,
          cols ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim →
            fanoPairPluckerXorRuntimeShadow a b cols =
              if cols = fanoPairGate a b then some c.state else none := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b hab
  obtain ⟨c, hc_ne_a, hc_ne_b, hline, _hunique⟩ :=
    distinct_pair_has_unique_completion a b hab
  refine ⟨c, hc_ne_a, hc_ne_b, hline, ?_⟩
  intro cols hcols
  have hstate := fanoLine_state_eq_xor a b c hline
  rw [fanoPairCoordinatePlane_runtime_reduces_to_xor a b hab cols hcols]
  by_cases hgate : cols = fanoPairGate a b
  · simp [hgate, hstate, completePair_state_eq_xor a b hab]
  · simp [hgate]

/-- Runtime-certificate atlas form: the certificate's support bit is exactly
gate equality, and its XOR payload is exactly the line completion on that gate
and absent elsewhere. -/
theorem fano_grassmannian_xor_runtime_certificate_atlas :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b : FanoPoint, a ≠ b →
      ∃ c,
        c ≠ a ∧ c ≠ b ∧
        fanoLine a b c ∧
        ∀ cols,
          cols ∈ kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim →
            let cert := fanoPairXorRuntimeCertificate a b cols
            cert.support = decide (cols = fanoPairGate a b) ∧
            cert.xorShadow = if cols = fanoPairGate a b then some c.state else none := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b hab
  obtain ⟨c, hc_ne_a, hc_ne_b, hline, _hunique⟩ :=
    distinct_pair_has_unique_completion a b hab
  refine ⟨c, hc_ne_a, hc_ne_b, hline, ?_⟩
  intro cols hcols
  have hcert := fanoPairXorRuntimeCertificate_reduces_to_xor a b hab cols hcols
  have hstate := fanoLine_state_eq_xor a b c hline
  refine ⟨hcert.2.1, ?_⟩
  rw [hcert.2.2]
  by_cases hgate : cols = fanoPairGate a b
  · simp [hgate, hstate, completePair_state_eq_xor a b hab]
  · simp [hgate]

/-- Whole-stack XOR runtime atlas theorem: every distinct Fano pair lowers the
entire 66-label Plucker stack to a 66-slot runtime trace with exactly one
payload, and that payload is the Fano line's XOR completion. -/
theorem fano_grassmannian_xor_runtime_stack_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b : FanoPoint, a ≠ b →
      ∃ c,
        c ≠ a ∧ c ≠ b ∧
        fanoLine a b c ∧
        (fanoPairXorRuntimeStack a b).length = 66 ∧
        optionPayloadCount (fanoPairXorRuntimeStack a b) = 1 ∧
        some c.state ∈ fanoPairXorRuntimeStack a b ∧
        ∀ out, out ∈ fanoPairXorRuntimeStack a b → out = none ∨ out = some c.state := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b hab
  obtain ⟨c, hc_ne_a, hc_ne_b, hline, _hunique⟩ :=
    distinct_pair_has_unique_completion a b hab
  have hstate := fanoLine_state_eq_xor a b c hline
  refine ⟨c, hc_ne_a, hc_ne_b, hline, fanoPairXorRuntimeStack_length a b,
    fanoPairXorRuntimeStack_payload_count_one a b hab, ?_, ?_⟩
  · rw [hline.2]
    exact fanoPairXorRuntimeStack_gate_payload a b hab
  · intro out hout
    have h := fanoPairXorRuntimeStack_no_wrong_payload a b hab out hout
    rcases h with hnone | hsome
    · exact Or.inl hnone
    · exact Or.inr (by simpa [hline.2] using hsome)

/-- Canonical XOR-only runtime atlas theorem: every distinct Fano pair's
Plucker-derived 66-slot runtime trace is definitionally matched by the
canonical XOR-only stack selected by the pair gate and the line completion. -/
theorem fano_grassmannian_runtime_equals_canonical_xor_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b : FanoPoint, a ≠ b →
      ∃ c,
        c ≠ a ∧ c ≠ b ∧
        fanoLine a b c ∧
        fanoPairXorRuntimeStack a b =
          fanoCanonicalXorRuntimeStack (fanoPairGate a b) c.state ∧
        (fanoCanonicalXorRuntimeStack (fanoPairGate a b) c.state).length = 66 ∧
        optionPayloadCount
          (fanoCanonicalXorRuntimeStack (fanoPairGate a b) c.state) = 1 := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b hab
  obtain ⟨c, hc_ne_a, hc_ne_b, hline, _hunique⟩ :=
    distinct_pair_has_unique_completion a b hab
  refine ⟨c, hc_ne_a, hc_ne_b, hline, ?_, ?_, ?_⟩
  · simpa [hline.2] using fanoPairXorRuntimeStack_eq_canonical_xor a b hab
  · exact fanoCanonicalXorRuntimeStack_length (fanoPairGate a b) c.state
  · simpa [hline.2, ← fanoPairXorRuntimeStack_eq_canonical_xor a b hab]
      using fanoPairXorRuntimeStack_payload_count_one a b hab

/-- Pair-canonical atlas theorem: the canonical XOR-only runtime stack itself
has the same 66-slot shape, one payload, no wrong payloads, and parity closure
for every distinct Fano pair in the embedded atlas. -/
theorem fano_grassmannian_pair_canonical_xor_runtime_stack_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b : FanoPoint, a ≠ b →
      (fanoPairCanonicalXorRuntimeStack a b).length = 66 ∧
      optionPayloadCount (fanoPairCanonicalXorRuntimeStack a b) = 1 ∧
      some (completePair a b).state ∈ fanoPairCanonicalXorRuntimeStack a b ∧
      (∀ out,
        out ∈ fanoPairCanonicalXorRuntimeStack a b →
          out = none ∨ out = some (completePair a b).state) ∧
      ∀ payload,
        some payload ∈ fanoPairCanonicalXorRuntimeStack a b →
          collide (collide a.state b.state) payload = godPosition := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b hab
  exact ⟨fanoPairCanonicalXorRuntimeStack_length a b,
    fanoPairCanonicalXorRuntimeStack_payload_count_one a b hab,
    fanoPairCanonicalXorRuntimeStack_gate_payload a b hab,
    fun out hout => fanoPairCanonicalXorRuntimeStack_no_wrong_payload a b hab out hout,
    fun payload hout => fanoPairCanonicalXorRuntimeStack_payload_parity_zero a b hab payload hout⟩

/-- Swap-invariant atlas theorem: the canonical XOR-only runtime trace and the
Plucker-derived trace do not depend on pair orientation. -/
theorem fano_grassmannian_xor_runtime_swap_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b : FanoPoint, a ≠ b →
      fanoPairCanonicalXorRuntimeStack a b =
        fanoPairCanonicalXorRuntimeStack b a ∧
      fanoPairXorRuntimeStack a b = fanoPairXorRuntimeStack b a := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b hab
  exact ⟨fanoPairCanonicalXorRuntimeStack_swap_invariant a b hab,
    fanoPairXorRuntimeStack_swap_invariant a b hab⟩

/-- Line-canonical atlas theorem: every Fano incidence line gives the
canonical XOR-only runtime stack carrying the third point as its single payload,
and that payload closes total XOR parity to the root. -/
theorem fano_grassmannian_line_canonical_xor_runtime_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ a b c : FanoPoint, a ≠ b → fanoLine a b c →
      fanoPairXorRuntimeStack a b =
        fanoCanonicalXorRuntimeStack (fanoPairGate a b) c.state ∧
      some c.state ∈ fanoCanonicalXorRuntimeStack (fanoPairGate a b) c.state ∧
      collide (collide a.state b.state) c.state = godPosition := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro a b c hab hline
  have hpayload := fanoLine_canonical_xor_payload_parity_zero a b c hab hline
  exact ⟨fanoLine_runtime_stack_eq_canonical_xor a b c hab hline,
    hpayload.1, hpayload.2⟩

/-- Label-indexed canonical runtime atlas theorem: the whole embedded
`Gr(2,7)` Fano label atlas can be consumed directly as labels, decoded to Fano
endpoints, and dispatched to 66-slot canonical XOR-only runtime stacks. -/
theorem fano_grassmannian_label_canonical_xor_runtime_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ gate : List Nat,
      gate ∈ kSubsets 2 7 →
        (fanoGatePoints gate).isSome = true ∧
        (fanoLabelCanonicalXorRuntimeStack gate).isSome = true ∧
        ∀ stack,
          fanoLabelCanonicalXorRuntimeStack gate = some stack →
            stack.length = 66 := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro gate hgate
  exact ⟨fanoGatePoints_decodes_embedded_pair_label_isSome gate hgate,
    fanoLabelCanonicalXorRuntimeStack_decodes_embedded_pair_label_isSome gate hgate,
    fun stack hstack => fanoLabelCanonicalXorRuntimeStack_decoded_length gate hgate stack hstack⟩

/-- Full label-indexed XOR runtime atlas theorem: every embedded `Gr(2,7)`
label dispatches to a 66-slot canonical XOR-only stack whose single payload is
the decoded Fano pair's completion and whose payload closes total XOR parity. -/
theorem fano_grassmannian_label_canonical_xor_payload_atlas_certificate :
    (kSubsets 2 7).length = 21 ∧
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 ∧
    ∀ gate : List Nat,
      gate ∈ kSubsets 2 7 →
        (fanoLabelCanonicalXorRuntimeStack gate).isSome = true ∧
        ∀ stack,
          fanoLabelCanonicalXorRuntimeStack gate = some stack →
            stack.length = 66 ∧
            ∃ a b,
              fanoGatePoints gate = some (a, b) ∧
              a ≠ b ∧
              optionPayloadCount stack = 1 ∧
              some (completePair a b).state ∈ stack ∧
              (∀ out, out ∈ stack →
                out = none ∨ out = some (completePair a b).state) ∧
              ∀ payload,
                some payload ∈ stack →
                  collide (collide a.state b.state) payload = godPosition := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro gate hgate
  refine ⟨fanoLabelCanonicalXorRuntimeStack_decodes_embedded_pair_label_isSome gate hgate, ?_⟩
  intro stack hstack
  exact ⟨fanoLabelCanonicalXorRuntimeStack_decoded_length gate hgate stack hstack,
    fanoLabelCanonicalXorRuntimeStack_payload_law gate stack hstack⟩

/-- The concrete birthday-problem-sized Fano atlas has `C(7,2) = 21` distinct
pair gates before embedding into the 66-gate Aeon-12 Plucker stack. -/
theorem fano_pair_gate_budget_twenty_one :
    (kSubsets 2 7).length = 21 := by
  native_decide

/-- The ambient Aeon mesh still exposes the existing 66 `Gr(2,12)` pair labels. -/
theorem aeon_pair_gate_budget_sixty_six :
    (kSubsets 2 Gnosis.AeonStandingWaveCoordinateBridge.ambientDim).length = 66 := by
  exact Gnosis.AeonStandingWaveCoordinateBridge.vertexCount_2_ambientDim_eq_sixty_six

end FanoGrassmannianMesh
end Gnosis
