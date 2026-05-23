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

/-- Numeric Aeon-tier cache key for a Fano endpoint pair: the sorted pair of
embedded Fano phase columns. This is the pair form of `fanoPairGate`, intended
for runtime maps that do not want to allocate a two-element label list. -/
def fanoPairPhaseCacheKey (a b : FanoPoint) : Nat × Nat :=
  let i := fanoColumn a
  let j := fanoColumn b
  if i < j then (i, j) else (j, i)

/-- Rehydrate the numeric cache key as the sorted two-column label. -/
def fanoPhaseCacheKeyGate (key : Nat × Nat) : List Nat :=
  [key.1, key.2]

theorem fanoPairPhaseCacheKey_eq_fanoPairGate (a b : FanoPoint) :
    fanoPhaseCacheKeyGate (fanoPairPhaseCacheKey a b) = fanoPairGate a b := by
  cases a <;> cases b <;> native_decide

theorem fanoPairPhaseCacheKey_swap_invariant
    (a b : FanoPoint) :
    fanoPairPhaseCacheKey a b = fanoPairPhaseCacheKey b a := by
  cases a <;> cases b <;> native_decide

theorem fanoPairPhaseCacheKey_fst_lt_sixteen
    (a b : FanoPoint) :
    (fanoPairPhaseCacheKey a b).1 < 16 := by
  cases a <;> cases b <;> native_decide

theorem fanoPairPhaseCacheKey_snd_lt_sixteen
    (a b : FanoPoint) :
    (fanoPairPhaseCacheKey a b).2 < 16 := by
  cases a <;> cases b <;> native_decide

def fanoPairPhaseCacheKeyGate0 (a b : FanoPoint) : Fin 16 :=
  ⟨(fanoPairPhaseCacheKey a b).1,
    fanoPairPhaseCacheKey_fst_lt_sixteen a b⟩

def fanoPairPhaseCacheKeyGate1 (a b : FanoPoint) : Fin 16 :=
  ⟨(fanoPairPhaseCacheKey a b).2,
    fanoPairPhaseCacheKey_snd_lt_sixteen a b⟩

/-- The complete 21-entry direct-table keyspace for distinct unordered Fano
phase pairs embedded in the first seven Aeon columns. -/
def fanoPhaseCacheKeyTable : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
   (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
   (2, 3), (2, 4), (2, 5), (2, 6),
   (3, 4), (3, 5), (3, 6),
   (4, 5), (4, 6),
   (5, 6)]

theorem fanoPhaseCacheKeyTable_length :
    fanoPhaseCacheKeyTable.length = 21 :=
  rfl

theorem fanoPairPhaseCacheKey_mem_table
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairPhaseCacheKey a b ∈ fanoPhaseCacheKeyTable := by
  cases a <;> cases b <;> simp [fanoPairPhaseCacheKey,
    fanoPhaseCacheKeyTable, fanoColumn, pointIndex] at hab ⊢

private theorem fanoPhaseCacheKeyTable_idx_lt_all :
    fanoPhaseCacheKeyTable.all
      (fun key => decide (fanoPhaseCacheKeyTable.idxOf key < 21)) = true := by
  native_decide

theorem fanoPhaseCacheKeyTable_idx_lt_twenty_one
    (key : Nat × Nat) (hkey : key ∈ fanoPhaseCacheKeyTable) :
    fanoPhaseCacheKeyTable.idxOf key < 21 := by
  have hall := List.all_eq_true.mp fanoPhaseCacheKeyTable_idx_lt_all key hkey
  simpa using hall

/-- Total 21-slot table index for an admitted Fano phase key. -/
def fanoPhaseCacheKeyTableIndex
    (key : Nat × Nat) (hkey : key ∈ fanoPhaseCacheKeyTable) : Fin 21 :=
  ⟨fanoPhaseCacheKeyTable.idxOf key,
    fanoPhaseCacheKeyTable_idx_lt_twenty_one key hkey⟩

/-- Direct index for a distinct Fano endpoint pair. -/
def fanoPairPhaseCacheKeyTableIndex
    (a b : FanoPoint) (hab : a ≠ b) : Fin 21 :=
  fanoPhaseCacheKeyTableIndex (fanoPairPhaseCacheKey a b)
    (fanoPairPhaseCacheKey_mem_table a b hab)

theorem fanoPairPhaseCacheKeyTableIndex_swap_invariant
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoPairPhaseCacheKeyTableIndex a b hab =
      fanoPairPhaseCacheKeyTableIndex b a (Ne.symm hab) := by
  simp [fanoPairPhaseCacheKeyTableIndex, fanoPhaseCacheKeyTableIndex,
    fanoPairPhaseCacheKey_swap_invariant]

/-- Closed lexicographic rank for a sorted Fano phase key `(i,j)`,
specialized to the seven visible Fano phases. For valid keys with
`0 ≤ i < j < 7`, this is the direct 21-slot array index. -/
def fanoPhaseCacheKeyRankCore (key : Nat × Nat) : Nat :=
  key.1 * (13 - key.1) / 2 + (key.2 - (key.1 + 1))

private theorem fanoPhaseCacheKeyRankCore_eq_idxOf_all :
    fanoPhaseCacheKeyTable.all
      (fun key => decide
        (fanoPhaseCacheKeyRankCore key = fanoPhaseCacheKeyTable.idxOf key)) =
      true := by
  native_decide

theorem fanoPhaseCacheKeyRankCore_eq_idxOf
    (key : Nat × Nat) (hkey : key ∈ fanoPhaseCacheKeyTable) :
    fanoPhaseCacheKeyRankCore key = fanoPhaseCacheKeyTable.idxOf key := by
  have hall := List.all_eq_true.mp fanoPhaseCacheKeyRankCore_eq_idxOf_all key hkey
  simpa using hall

theorem fanoPhaseCacheKeyRankCore_lt_twenty_one
    (key : Nat × Nat) (hkey : key ∈ fanoPhaseCacheKeyTable) :
    fanoPhaseCacheKeyRankCore key < 21 := by
  rw [fanoPhaseCacheKeyRankCore_eq_idxOf key hkey]
  exact fanoPhaseCacheKeyTable_idx_lt_twenty_one key hkey

/-- Closed-form `Fin 21` index for an admitted Fano phase key. -/
def fanoPhaseCacheKeyRank
    (key : Nat × Nat) (hkey : key ∈ fanoPhaseCacheKeyTable) : Fin 21 :=
  ⟨fanoPhaseCacheKeyRankCore key,
    fanoPhaseCacheKeyRankCore_lt_twenty_one key hkey⟩

theorem fanoPhaseCacheKeyRank_eq_table_index
    (key : Nat × Nat) (hkey : key ∈ fanoPhaseCacheKeyTable) :
    fanoPhaseCacheKeyRank key hkey = fanoPhaseCacheKeyTableIndex key hkey := by
  apply Fin.ext
  exact fanoPhaseCacheKeyRankCore_eq_idxOf key hkey

theorem fanoPairPhaseCacheKeyRank_swap_invariant
    (a b : FanoPoint) (hab : a ≠ b) :
    fanoPhaseCacheKeyRank (fanoPairPhaseCacheKey a b)
        (fanoPairPhaseCacheKey_mem_table a b hab) =
      fanoPhaseCacheKeyRank (fanoPairPhaseCacheKey b a)
        (fanoPairPhaseCacheKey_mem_table b a (Ne.symm hab)) := by
  simp [fanoPairPhaseCacheKey_swap_invariant]

def monsterAeonFanoCanonicalCertificate
    (m n : Nat) (a b : FanoPoint) : MonsterAeonFanoCertificate where
  monsterColumns := [m, n]
  aeonPhases := [fanoColumn a, fanoColumn b]
  aeonGate := fanoPairGate a b
  fanoStates := [a.state, b.state]
  completion := collide a.state b.state
  orientationSign := if fanoColumn a < fanoColumn b then 1 else -1
  positiveGate := true
  residualValidated := true
  fingerprintVerified := true

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

theorem fanoColumnPoint_eq_some_implies_column
    (phase : Nat) (p : FanoPoint)
    (h : fanoColumnPoint phase = some p) :
    phase = fanoColumn p := by
  revert p h
  cases phase with
  | zero =>
      intro p h
      cases p <;> simp [fanoColumnPoint, fanoColumn, pointIndex] at h ⊢
  | succ phase =>
      cases phase with
      | zero =>
          intro p h
          cases p <;> simp [fanoColumnPoint, fanoColumn, pointIndex] at h ⊢
      | succ phase =>
          cases phase with
          | zero =>
              intro p h
              cases p <;> simp [fanoColumnPoint, fanoColumn, pointIndex] at h ⊢
          | succ phase =>
              cases phase with
              | zero =>
                  intro p h
                  cases p <;> simp [fanoColumnPoint, fanoColumn, pointIndex] at h ⊢
              | succ phase =>
                  cases phase with
                  | zero =>
                      intro p h
                      cases p <;> simp [fanoColumnPoint, fanoColumn, pointIndex] at h ⊢
                  | succ phase =>
                      cases phase with
                      | zero =>
                          intro p h
                          cases p <;> simp [fanoColumnPoint, fanoColumn, pointIndex] at h ⊢
                      | succ phase =>
                          cases phase with
                          | zero =>
                              intro p h
                              cases p <;> simp [fanoColumnPoint, fanoColumn, pointIndex] at h ⊢
                          | succ phase =>
                              intro p h
                              cases p <;> simp [fanoColumnPoint] at h

theorem aeonPhaseFanoState_isSome_eq_fanoColumnPoint_isSome
    (phase : Nat) :
    (aeonPhaseFanoState phase).isSome = (fanoColumnPoint phase).isSome := by
  cases phase with
  | zero => rfl
  | succ phase =>
      cases phase with
      | zero => rfl
      | succ phase =>
          cases phase with
          | zero => rfl
          | succ phase =>
              cases phase with
              | zero => rfl
              | succ phase =>
                  cases phase with
                  | zero => rfl
                  | succ phase =>
                      cases phase with
                      | zero => rfl
                      | succ phase =>
                          cases phase with
                          | zero => rfl
                          | succ phase => rfl

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

/-- Monster-side numeric Aeon-tier cache key after Fano projection. It is
defined exactly when both Monster columns decode to distinct embedded Fano
endpoints, and it forgets the original Monster column addresses. -/
def monsterPairFanoPhaseCacheKey (a b : Nat) : Option (Nat × Nat) :=
  match monsterPairFanoPoints a b with
  | some (x, y) => if x ≠ y then some (fanoPairPhaseCacheKey x y) else none
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

theorem monsterPairFanoPoints_eq_some_implies_phases
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) :
    monsterColumnPhase m = fanoColumn a ∧
      monsterColumnPhase n = fanoColumn b := by
  unfold monsterPairFanoPoints monsterColumnFanoPoint at hdecode
  cases hm : fanoColumnPoint (monsterColumnPhase m) with
  | none => simp [hm] at hdecode
  | some lhs =>
      cases hn : fanoColumnPoint (monsterColumnPhase n) with
      | none => simp [hm, hn] at hdecode
      | some rhs =>
          simp [hm, hn] at hdecode
          rcases hdecode with ⟨hlhs, hrhs⟩
          subst lhs
          subst rhs
          exact ⟨fanoColumnPoint_eq_some_implies_column (monsterColumnPhase m) a hm,
            fanoColumnPoint_eq_some_implies_column (monsterColumnPhase n) b hn⟩

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

/-- Monster-side fast payload dispatch through the Fano subatlas. This is the
stack-free version of `monsterPairFanoXorRuntimeStack` for callers that only
need the unique XOR completion payload. -/
def monsterPairFanoXorPayload (a b : Nat) : Option TritonState :=
  match monsterPairFanoPoints a b with
  | some (x, y) =>
      if x ≠ y then some (collide x.state y.state) else none
  | none => none

/-- Status bits for the compact stack-free Monster/Fano XOR route. This is the
Lean mirror of the Rust packed `u16` route status field: admitted payload,
same Aeon phase, outside the Fano subatlas, or shadow validation required. -/
inductive PackedFanoXorRouteStatus
  | admitted
  | samePhase
  | outsideFanoSubatlas
  | shadowValidationRequired
  deriving DecidableEq, Repr

/-- Compact route record before bit-packing. Runtime implementations may pack
`status`, `payload`, and the two gate columns into a small integer; this
structure states the semantic payload that the packed bits must preserve. -/
structure PackedFanoXorRoute where
  status : PackedFanoXorRouteStatus
  payload : Option TritonState
  aeonGate : List Nat
deriving DecidableEq, Repr

def packedFanoXorRoutePayload (route : PackedFanoXorRoute) : Option TritonState :=
  match route.status with
  | PackedFanoXorRouteStatus.admitted => route.payload
  | _ => none

def packedFanoXorRouteStatusCode : PackedFanoXorRouteStatus → Nat
  | PackedFanoXorRouteStatus.admitted => 0
  | PackedFanoXorRouteStatus.samePhase => 1
  | PackedFanoXorRouteStatus.outsideFanoSubatlas => 2
  | PackedFanoXorRouteStatus.shadowValidationRequired => 3

/-- Arithmetic mirror of the Rust `u16` packed route:
`status:2 | gate1:4 | gate0:4 | value:3`. -/
def packedFanoXorRouteWord
    (status : PackedFanoXorRouteStatus) (value : Fin 8)
    (gate0 gate1 : Fin 16) : Nat :=
  packedFanoXorRouteStatusCode status * 2048 +
    gate1.val * 128 + gate0.val * 8 + value.val

def packedFanoXorRouteWordStatusCode (word : Nat) : Nat :=
  (word / 2048) % 4

def packedFanoXorRouteWordValue (word : Nat) : Nat :=
  word % 8

def packedFanoXorRouteWordGate0 (word : Nat) : Nat :=
  (word / 8) % 16

def packedFanoXorRouteWordGate1 (word : Nat) : Nat :=
  (word / 128) % 16

theorem packedFanoXorRouteWord_status_round_trip
    (status : PackedFanoXorRouteStatus) (value : Fin 8)
    (gate0 gate1 : Fin 16) :
    packedFanoXorRouteWordStatusCode
        (packedFanoXorRouteWord status value gate0 gate1) =
      packedFanoXorRouteStatusCode status := by
  unfold packedFanoXorRouteWordStatusCode
  have h_rem : gate1.val * 128 + gate0.val * 8 + value.val < 2048 := by
    calc gate1.val * 128 + gate0.val * 8 + value.val
        ≤ 15 * 128 + 15 * 8 + 7 := by
          apply Nat.add_le_add
          · apply Nat.add_le_add
            · exact Nat.mul_le_mul_right 128 (Nat.le_of_lt_succ gate1.is_lt)
            · exact Nat.mul_le_mul_right 8 (Nat.le_of_lt_succ gate0.is_lt)
          · exact Nat.le_of_lt_succ value.is_lt
      _ = 2047 := by decide
      _ < 2048 := by decide
  have hdiv :
      packedFanoXorRouteWord status value gate0 gate1 / 2048 =
        packedFanoXorRouteStatusCode status := by
      unfold packedFanoXorRouteWord
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm (packedFanoXorRouteStatusCode status * 2048)]
      rw [Nat.mul_comm (packedFanoXorRouteStatusCode status) 2048]
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2048)]
      rw [← Nat.add_assoc]
      rw [Nat.div_eq_of_lt h_rem]
      rw [Nat.zero_add]
  rw [hdiv]
  exact Nat.mod_eq_of_lt (by
    cases status <;> simp [packedFanoXorRouteStatusCode] <;> decide)

theorem packedFanoXorRouteWord_value_round_trip
    (status : PackedFanoXorRouteStatus) (value : Fin 8)
    (gate0 gate1 : Fin 16) :
    packedFanoXorRouteWordValue
        (packedFanoXorRouteWord status value gate0 gate1) =
      value.val := by
  unfold packedFanoXorRouteWordValue packedFanoXorRouteWord
  rw [Nat.add_mod]
  have h_mul : (packedFanoXorRouteStatusCode status * 2048 + gate1.val * 128 + gate0.val * 8) % 8 = 0 := by
    rw [Nat.add_mod]
    rw [Nat.add_mod (packedFanoXorRouteStatusCode status * 2048) (gate1.val * 128) 8]
    have h1 : (packedFanoXorRouteStatusCode status * 2048) % 8 = 0 := by
      rw [show 2048 = 256 * 8 from rfl, ← Nat.mul_assoc]
      rw [Nat.mul_comm (packedFanoXorRouteStatusCode status * 256) 8]
      exact Nat.mul_mod_right 8 (packedFanoXorRouteStatusCode status * 256)
    have h2 : (gate1.val * 128) % 8 = 0 := by
      rw [show 128 = 16 * 8 from rfl, ← Nat.mul_assoc]
      rw [Nat.mul_comm (gate1.val * 16) 8]
      exact Nat.mul_mod_right 8 (gate1.val * 16)
    have h3 : (gate0.val * 8) % 8 = 0 := by
      rw [Nat.mul_comm gate0.val 8]
      exact Nat.mul_mod_right 8 gate0.val
    rw [h1, h2, h3]
  rw [h_mul, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt value.is_lt

theorem packedFanoXorRouteWord_gate0_round_trip
    (status : PackedFanoXorRouteStatus) (value : Fin 8)
    (gate0 gate1 : Fin 16) :
    packedFanoXorRouteWordGate0
        (packedFanoXorRouteWord status value gate0 gate1) =
      gate0.val := by
  unfold packedFanoXorRouteWordGate0 packedFanoXorRouteWord
  have h_split : packedFanoXorRouteStatusCode status * 2048 + gate1.val * 128 + gate0.val * 8 + value.val
      = (packedFanoXorRouteStatusCode status * 256 + gate1.val * 16 + gate0.val) * 8 + value.val := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  rw [h_split]
  rw [Nat.add_comm ((packedFanoXorRouteStatusCode status * 256 + gate1.val * 16 + gate0.val) * 8) value.val]
  rw [Nat.mul_comm (packedFanoXorRouteStatusCode status * 256 + gate1.val * 16 + gate0.val) 8]
  rw [Nat.add_mul_div_left _ _ (by decide : 0 < 8)]
  rw [Nat.div_eq_of_lt value.is_lt]
  rw [Nat.zero_add]
  have h_mod : (packedFanoXorRouteStatusCode status * 256 + gate1.val * 16 + gate0.val)
      = (packedFanoXorRouteStatusCode status * 16 + gate1.val) * 16 + gate0.val := by
    rw [Nat.add_mul, Nat.mul_assoc]
  rw [h_mod]
  rw [Nat.add_comm]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt gate0.is_lt

theorem packedFanoXorRouteWord_gate1_round_trip
    (status : PackedFanoXorRouteStatus) (value : Fin 8)
    (gate0 gate1 : Fin 16) :
    packedFanoXorRouteWordGate1
        (packedFanoXorRouteWord status value gate0 gate1) =
      gate1.val := by
  unfold packedFanoXorRouteWordGate1 packedFanoXorRouteWord
  have h_split : packedFanoXorRouteStatusCode status * 2048 + gate1.val * 128 + gate0.val * 8 + value.val
      = (packedFanoXorRouteStatusCode status * 16 + gate1.val) * 128 + (gate0.val * 8 + value.val) := by
    rw [Nat.add_mul, Nat.mul_assoc, show 16 * 128 = 2048 from rfl]
    rw [Nat.add_assoc]
  rw [h_split]
  rw [Nat.add_comm ((packedFanoXorRouteStatusCode status * 16 + gate1.val) * 128) (gate0.val * 8 + value.val)]
  rw [Nat.mul_comm (packedFanoXorRouteStatusCode status * 16 + gate1.val) 128]
  rw [Nat.add_mul_div_left _ _ (by decide : 0 < 128)]
  have h_rem : gate0.val * 8 + value.val < 128 := by
    calc gate0.val * 8 + value.val
        ≤ 15 * 8 + 7 := Nat.add_le_add (Nat.mul_le_mul_right 8 (Nat.le_of_lt_succ gate0.is_lt)) (Nat.le_of_lt_succ value.is_lt)
      _ = 127 := by decide
      _ < 128 := by decide
  rw [Nat.div_eq_of_lt h_rem]
  rw [Nat.zero_add]
  rw [Nat.add_comm]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt gate1.is_lt

def packedFanoXorRouteHotWord (a b : FanoPoint) : Nat :=
  packedFanoXorRouteWord
    PackedFanoXorRouteStatus.admitted
    (collide a.state b.state)
    (fanoPairPhaseCacheKeyGate0 a b)
    (fanoPairPhaseCacheKeyGate1 a b)

def packedFanoXorRouteHintPositiveWord (word : Nat) : Nat :=
  word + 8192

def packedFanoXorRouteHotPositiveHintWord (a b : FanoPoint) : Nat :=
  packedFanoXorRouteHintPositiveWord (packedFanoXorRouteHotWord a b)

theorem packedFanoXorRouteHotWord_extractors
    (a b : FanoPoint) :
    packedFanoXorRouteWordStatusCode
        (packedFanoXorRouteHotWord a b) =
      packedFanoXorRouteStatusCode PackedFanoXorRouteStatus.admitted ∧
    packedFanoXorRouteWordValue
        (packedFanoXorRouteHotWord a b) =
      (collide a.state b.state).val ∧
    packedFanoXorRouteWordGate0
        (packedFanoXorRouteHotWord a b) =
      (fanoPairPhaseCacheKey a b).1 ∧
    packedFanoXorRouteWordGate1
        (packedFanoXorRouteHotWord a b) =
      (fanoPairPhaseCacheKey a b).2 := by
  unfold packedFanoXorRouteHotWord
  exact ⟨
    packedFanoXorRouteWord_status_round_trip
      PackedFanoXorRouteStatus.admitted
      (collide a.state b.state)
      (fanoPairPhaseCacheKeyGate0 a b)
      (fanoPairPhaseCacheKeyGate1 a b),
    packedFanoXorRouteWord_value_round_trip
      PackedFanoXorRouteStatus.admitted
      (collide a.state b.state)
      (fanoPairPhaseCacheKeyGate0 a b)
      (fanoPairPhaseCacheKeyGate1 a b),
    packedFanoXorRouteWord_gate0_round_trip
      PackedFanoXorRouteStatus.admitted
      (collide a.state b.state)
      (fanoPairPhaseCacheKeyGate0 a b)
      (fanoPairPhaseCacheKeyGate1 a b),
    packedFanoXorRouteWord_gate1_round_trip
      PackedFanoXorRouteStatus.admitted
      (collide a.state b.state)
      (fanoPairPhaseCacheKeyGate0 a b)
      (fanoPairPhaseCacheKeyGate1 a b)⟩

/-- Stack-free compact Monster/Fano dispatch. The admitted branch is exactly
the existing `monsterPairFanoXorPayload`; the other branches retain the
runtime reason needed by the wire adapter without materializing the 66-stack. -/
def monsterPairFanoXorPackedRoute
    (a b : Nat) (residualValidated fingerprintVerified : Bool) :
    PackedFanoXorRoute :=
  let i := monsterColumnPhase a
  let j := monsterColumnPhase b
  let gate := if i < j then [i, j] else [j, i]
  match monsterPairFanoPoints a b with
  | some (x, y) =>
      if x ≠ y then
        if residualValidated && fingerprintVerified then
          { status := PackedFanoXorRouteStatus.admitted
            payload := some (collide x.state y.state)
            aeonGate := fanoPairGate x y }
        else
          { status := PackedFanoXorRouteStatus.shadowValidationRequired
            payload := none
            aeonGate := gate }
      else
        { status := PackedFanoXorRouteStatus.samePhase
          payload := none
          aeonGate := gate }
  | none =>
      { status := PackedFanoXorRouteStatus.outsideFanoSubatlas
        payload := none
        aeonGate := gate }

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

theorem monsterPairFanoPhaseCacheKey_eq_of_decode
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    monsterPairFanoPhaseCacheKey m n = some (fanoPairPhaseCacheKey a b) := by
  simp [monsterPairFanoPhaseCacheKey, hdecode, hab]

theorem monsterPairFanoPhaseCacheKey_mem_table_of_decode
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    ∃ key,
      monsterPairFanoPhaseCacheKey m n = some key ∧
      key ∈ fanoPhaseCacheKeyTable := by
  exact ⟨fanoPairPhaseCacheKey a b,
    monsterPairFanoPhaseCacheKey_eq_of_decode m n a b hdecode hab,
    fanoPairPhaseCacheKey_mem_table a b hab⟩

theorem monsterPairFanoGate_eq_phase_cache_key_gate_of_decode
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    monsterPairFanoGate m n =
      some (fanoPhaseCacheKeyGate (fanoPairPhaseCacheKey a b)) := by
  rw [monsterPairFanoGate_eq_fanoPairGate_of_decode m n a b hdecode hab,
    fanoPairPhaseCacheKey_eq_fanoPairGate a b]

theorem monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    monsterPairFanoXorRuntimeStack m n =
      some (fanoPairCanonicalXorRuntimeStack a b) := by
  simp [monsterPairFanoXorRuntimeStack, hdecode, hab]

theorem monsterPairFanoXorPayload_eq_completion_of_decode
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    monsterPairFanoXorPayload m n = some (completePair a b).state := by
  simp [monsterPairFanoXorPayload, hdecode, hab, completePair_state_eq_xor a b hab]

theorem monsterPairFanoXorPackedRoute_payload_eq_stack_free
    (m n : Nat) :
    packedFanoXorRoutePayload (monsterPairFanoXorPackedRoute m n true true) =
      monsterPairFanoXorPayload m n := by
  unfold monsterPairFanoXorPackedRoute monsterPairFanoXorPayload
  unfold monsterPairFanoPoints monsterColumnFanoPoint
  cases fanoColumnPoint (monsterColumnPhase m) with
  | none => simp [packedFanoXorRoutePayload]
  | some a =>
      cases fanoColumnPoint (monsterColumnPhase n) with
      | none => simp [packedFanoXorRoutePayload]
      | some b =>
          by_cases hab : a ≠ b
          · simp [packedFanoXorRoutePayload, hab]
          · simp [packedFanoXorRoutePayload, hab]

theorem monsterPairFanoXorPackedRoute_admitted_eq_completion_of_decode
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    packedFanoXorRoutePayload (monsterPairFanoXorPackedRoute m n true true) =
      some (completePair a b).state := by
  rw [monsterPairFanoXorPackedRoute_payload_eq_stack_free m n]
  exact monsterPairFanoXorPayload_eq_completion_of_decode m n a b hdecode hab

theorem monsterPairFanoXorPayload_eq_stack_unique_payload
    (m n : Nat) (stack : List (Option TritonState))
    (hstack : monsterPairFanoXorRuntimeStack m n = some stack) :
    ∃ payload,
      monsterPairFanoXorPayload m n = some payload ∧
      some payload ∈ stack ∧
      optionPayloadCount stack = 1 ∧
      (∀ out, out ∈ stack → out = none ∨ out = some payload) ∧
      ∀ a b,
        monsterPairFanoPoints m n = some (a, b) →
        a ≠ b →
        collide (collide a.state b.state) payload = godPosition := by
  obtain ⟨a, b, hdecode, hab, hcount, hpayload, hnowrong, _hparity⟩ :=
    monsterPairFanoXorRuntimeStack_payload_law m n stack hstack
  refine ⟨(completePair a b).state, ?_, hpayload, hcount, hnowrong, ?_⟩
  · exact monsterPairFanoXorPayload_eq_completion_of_decode m n a b hdecode hab
  · intro a' b' hdecode' _hab'
    have hpair : (a', b') = (a, b) := by
      rw [hdecode] at hdecode'
      exact (Option.some.inj hdecode').symm
    cases hpair
    exact completePair_xor_parity_zero a b hab

theorem monsterPairFanoXorPayload_some_iff_stack_unique_payload
    (m n : Nat) (payload : TritonState) :
    monsterPairFanoXorPayload m n = some payload ↔
      ∃ stack,
        monsterPairFanoXorRuntimeStack m n = some stack ∧
        some payload ∈ stack ∧
        optionPayloadCount stack = 1 ∧
        (∀ out, out ∈ stack → out = none ∨ out = some payload) := by
  constructor
  · intro hpayload
    unfold monsterPairFanoXorPayload at hpayload
    cases hdecode : monsterPairFanoPoints m n with
    | none => simp [hdecode] at hpayload
    | some pair =>
        cases pair with
        | mk a b =>
            by_cases hab : a ≠ b
            · simp [hdecode, hab] at hpayload
              have hpayload_eq : payload = (completePair a b).state := by
                rw [← hpayload]
                exact (completePair_state_eq_xor a b hab).symm
              refine ⟨fanoPairCanonicalXorRuntimeStack a b,
                monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode m n a b hdecode hab,
                ?_, ?_, ?_⟩
              · rw [hpayload_eq]
                exact fanoPairCanonicalXorRuntimeStack_gate_payload a b hab
              · exact fanoPairCanonicalXorRuntimeStack_payload_count_one a b hab
              · intro out hout
                have hwrong := fanoPairCanonicalXorRuntimeStack_no_wrong_payload a b hab out hout
                rcases hwrong with hnone | hsome
                · exact Or.inl hnone
                · exact Or.inr (by simpa [hpayload_eq] using hsome)
            · simp [hdecode, hab] at hpayload
  · intro hstack
    obtain ⟨stack, hstack, hpayload_mem, _hcount, hnowrong⟩ := hstack
    obtain ⟨fastPayload, hfast, _hfast_mem, _hfast_count, _hfast_nowrong, _hparity⟩ :=
      monsterPairFanoXorPayload_eq_stack_unique_payload m n stack hstack
    have hpayload_eq : payload = fastPayload := by
      have h := hnowrong (some fastPayload) _hfast_mem
      rcases h with hnone | hsome
      · cases hnone
      · exact Option.some.inj hsome.symm
    rw [hpayload_eq]
    exact hfast

theorem monsterPairFanoXorPayload_swap_invariant_of_phases
    (m n : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b) (hab : a ≠ b) :
    monsterPairFanoXorPayload m n = monsterPairFanoXorPayload n m := by
  rw [monsterPairFanoXorPayload_eq_completion_of_decode m n a b
      (monsterPairFanoPoints_eq_some_of_phases m n a b hm hn) hab,
    monsterPairFanoXorPayload_eq_completion_of_decode n m b a
      (monsterPairFanoPoints_eq_some_of_phases n m b a hn hm) (Ne.symm hab)]
  exact congrArg (fun p => some p.state) (fano_plucker_sign_shadow_certificate a b hab).2.1

theorem monsterPairFanoXorPayload_exists_iff_decoded_distinct
    (m n : Nat) :
    (∃ payload, monsterPairFanoXorPayload m n = some payload) ↔
      ∃ a b, monsterPairFanoPoints m n = some (a, b) ∧ a ≠ b := by
  constructor
  · intro hpayload
    obtain ⟨payload, hpayload⟩ := hpayload
    unfold monsterPairFanoXorPayload at hpayload
    cases hdecode : monsterPairFanoPoints m n with
    | none => simp [hdecode] at hpayload
    | some pair =>
        cases pair with
        | mk a b =>
            by_cases hab : a ≠ b
            · exact ⟨a, b, by simp, hab⟩
            · simp [hdecode, hab] at hpayload
  · intro hdecode
    obtain ⟨a, b, hdecode, hab⟩ := hdecode
    exact ⟨(completePair a b).state,
      monsterPairFanoXorPayload_eq_completion_of_decode m n a b hdecode hab⟩

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

/-- Validated Monster/Aeon/Fano certificates and direct Monster/Fano XOR stack
dispatch agree on the same visible phase pairs. -/
theorem monsterAeonFanoCertificate_validated_dispatches_to_xor_stack_of_phases
    (m n : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b) (hab : a ≠ b) :
    (monsterAeonFanoCertificate m n true true).isSome = true ∧
      monsterPairFanoXorRuntimeStack m n =
        some (fanoPairCanonicalXorRuntimeStack a b) := by
  constructor
  · unfold monsterAeonFanoCertificate monsterPairAeonGate
    rw [hm, hn]
    cases a <;> cases b <;> simp [fanoColumn, pointIndex, aeonPhaseFanoState] at hab ⊢
  · exact monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode m n a b
      (monsterPairFanoPoints_eq_some_of_phases m n a b hm hn) hab

/-- Phase-indexed inverse runtime gate: whenever direct Monster/Fano XOR stack
dispatch returns a stack for explicitly identified visible Fano phases, the
validated Monster/Aeon/Fano certificate path is also open and carries the same
phase-pair completion as the unique runtime payload. -/
theorem monsterPairFanoXorRuntimeStack_dispatch_implies_validated_certificate_of_phases
    (m n : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b) (hab : a ≠ b)
    (stack : List (Option TritonState))
    (hstack : monsterPairFanoXorRuntimeStack m n = some stack) :
    (monsterAeonFanoCertificate m n true true).isSome = true ∧
      optionPayloadCount stack = 1 ∧
      some (completePair a b).state ∈ stack ∧
      (∀ out, out ∈ stack → out = none ∨ out = some (completePair a b).state) ∧
      ∀ payload,
        some payload ∈ stack →
          collide (collide a.state b.state) payload = godPosition := by
  have hcert :=
    monsterAeonFanoCertificate_validated_dispatches_to_xor_stack_of_phases m n a b hm hn hab
  rw [hcert.2] at hstack
  have hstack_eq : stack = fanoPairCanonicalXorRuntimeStack a b := by
    exact (Option.some.inj hstack).symm
  subst stack
  exact ⟨hcert.1,
    fanoPairCanonicalXorRuntimeStack_payload_count_one a b hab,
    fanoPairCanonicalXorRuntimeStack_gate_payload a b hab,
    fanoPairCanonicalXorRuntimeStack_no_wrong_payload a b hab,
    fun payload hout => fanoPairCanonicalXorRuntimeStack_payload_parity_zero a b hab payload hout⟩

theorem monsterPairFanoXorRuntimeStack_dispatch_implies_phase_evidence
    (m n : Nat) (stack : List (Option TritonState))
    (hstack : monsterPairFanoXorRuntimeStack m n = some stack) :
    ∃ a b,
      monsterPairFanoPoints m n = some (a, b) ∧
      monsterColumnPhase m = fanoColumn a ∧
      monsterColumnPhase n = fanoColumn b ∧
      a ≠ b := by
  obtain ⟨a, b, hdecode, hab, _hcount, _hpayload, _hnowrong, _hparity⟩ :=
    monsterPairFanoXorRuntimeStack_payload_law m n stack hstack
  have hphases := monsterPairFanoPoints_eq_some_implies_phases m n a b hdecode
  exact ⟨a, b, hdecode, hphases.1, hphases.2, hab⟩

/-- Full inverse runtime gate: whenever direct Monster/Fano XOR stack dispatch
returns a stack, the validated Monster/Aeon/Fano certificate path is also open
and carries the decoded-pair completion as the unique parity-closing payload. -/
theorem monsterPairFanoXorRuntimeStack_dispatch_implies_validated_certificate
    (m n : Nat) (stack : List (Option TritonState))
    (hstack : monsterPairFanoXorRuntimeStack m n = some stack) :
    (monsterAeonFanoCertificate m n true true).isSome = true ∧
      ∃ a b,
        monsterPairFanoPoints m n = some (a, b) ∧
        a ≠ b ∧
        optionPayloadCount stack = 1 ∧
        some (completePair a b).state ∈ stack ∧
        (∀ out, out ∈ stack → out = none ∨ out = some (completePair a b).state) ∧
        ∀ payload,
          some payload ∈ stack →
            collide (collide a.state b.state) payload = godPosition := by
  obtain ⟨a, b, hdecode, hm, hn, hab⟩ :=
    monsterPairFanoXorRuntimeStack_dispatch_implies_phase_evidence m n stack hstack
  have hinv :=
    monsterPairFanoXorRuntimeStack_dispatch_implies_validated_certificate_of_phases
      m n a b hm hn hab stack hstack
  exact ⟨hinv.1, a, b, hdecode, hab, hinv.2.1, hinv.2.2.1,
    hinv.2.2.2.1, hinv.2.2.2.2⟩

/-- Bidirectional runtime contract: a Monster/Fano XOR stack is returned
exactly when the Monster pair decodes to distinct embedded Fano endpoints whose
validated certificate path is open, and the returned stack is the canonical
one-payload XOR stack for that decoded pair. -/
theorem monsterPairFanoXorRuntimeStack_some_iff_validated_certificate_payload
    (m n : Nat) (stack : List (Option TritonState)) :
    monsterPairFanoXorRuntimeStack m n = some stack ↔
      ∃ a b,
        monsterPairFanoPoints m n = some (a, b) ∧
        a ≠ b ∧
        (monsterAeonFanoCertificate m n true true).isSome = true ∧
        stack = fanoPairCanonicalXorRuntimeStack a b ∧
        optionPayloadCount stack = 1 ∧
        some (completePair a b).state ∈ stack ∧
        (∀ out, out ∈ stack → out = none ∨ out = some (completePair a b).state) ∧
        ∀ payload,
          some payload ∈ stack →
            collide (collide a.state b.state) payload = godPosition := by
  constructor
  · intro hstack
    obtain ⟨a, b, hdecode, hm, hn, hab⟩ :=
      monsterPairFanoXorRuntimeStack_dispatch_implies_phase_evidence m n stack hstack
    have hcert :=
      monsterAeonFanoCertificate_validated_dispatches_to_xor_stack_of_phases m n a b hm hn hab
    rw [hcert.2] at hstack
    have hstack_eq : stack = fanoPairCanonicalXorRuntimeStack a b := by
      exact (Option.some.inj hstack).symm
    subst stack
    exact ⟨a, b, hdecode, hab, hcert.1, rfl,
      fanoPairCanonicalXorRuntimeStack_payload_count_one a b hab,
      fanoPairCanonicalXorRuntimeStack_gate_payload a b hab,
      fanoPairCanonicalXorRuntimeStack_no_wrong_payload a b hab,
      fun payload hout => fanoPairCanonicalXorRuntimeStack_payload_parity_zero a b hab payload hout⟩
  · intro hcontract
    obtain ⟨a, b, hdecode, hab, _hcert, hstack_eq, _hcount, _hpayload,
      _hnowrong, _hparity⟩ := hcontract
    rw [hstack_eq]
    exact monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode m n a b hdecode hab

theorem monsterPairFanoXorRuntimeStack_exists_iff_decoded_distinct
    (m n : Nat) :
    (∃ stack, monsterPairFanoXorRuntimeStack m n = some stack) ↔
      ∃ a b, monsterPairFanoPoints m n = some (a, b) ∧ a ≠ b := by
  constructor
  · intro hstack
    obtain ⟨stack, hstack⟩ := hstack
    obtain ⟨a, b, hdecode, _hm, _hn, hab⟩ :=
      monsterPairFanoXorRuntimeStack_dispatch_implies_phase_evidence m n stack hstack
    exact ⟨a, b, hdecode, hab⟩
  · intro hdecode
    obtain ⟨a, b, hdecode, hab⟩ := hdecode
    exact ⟨fanoPairCanonicalXorRuntimeStack a b,
      monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode m n a b hdecode hab⟩

/-- Aeon-tier cache reuse law: once two Monster-side pairs decode to the same
distinct embedded Fano endpoint pair, both the 66-slot runtime stack and the
stack-free payload are identical.  The Monster columns themselves have no
remaining influence after this projection. -/
theorem monsterPairFanoXorRuntimeStack_same_decoded_pair_cache_key
    (m n m' n' : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b))
    (hdecode' : monsterPairFanoPoints m' n' = some (a, b))
    (hab : a ≠ b) :
    monsterPairFanoXorRuntimeStack m n =
      monsterPairFanoXorRuntimeStack m' n' ∧
    monsterPairFanoXorPayload m n =
      monsterPairFanoXorPayload m' n' := by
  rw [monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode m n a b hdecode hab,
    monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode m' n' a b hdecode' hab,
    monsterPairFanoXorPayload_eq_completion_of_decode m n a b hdecode hab,
    monsterPairFanoXorPayload_eq_completion_of_decode m' n' a b hdecode' hab]
  exact ⟨rfl, rfl⟩

/-- Numeric key form of the Aeon-tier cache reuse law. The stored key is the
sorted Fano phase pair, so equal decoded endpoints force equal runtime keys. -/
theorem monsterPairFanoPhaseCacheKey_same_decoded_pair
    (m n m' n' : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b))
    (hdecode' : monsterPairFanoPoints m' n' = some (a, b))
    (hab : a ≠ b) :
    monsterPairFanoPhaseCacheKey m n =
      monsterPairFanoPhaseCacheKey m' n' := by
  rw [monsterPairFanoPhaseCacheKey_eq_of_decode m n a b hdecode hab,
    monsterPairFanoPhaseCacheKey_eq_of_decode m' n' a b hdecode' hab]

/-- Phase form of the same cache law: Monster columns with the same two
Fano-visible Aeon phases share the same decoded-pair cache key. -/
theorem monsterPairFanoXorRuntimeStack_same_fano_phases_cache_key
    (m n m' n' : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b)
    (hm' : monsterColumnPhase m' = fanoColumn a)
    (hn' : monsterColumnPhase n' = fanoColumn b)
    (hab : a ≠ b) :
    monsterPairFanoXorRuntimeStack m n =
      monsterPairFanoXorRuntimeStack m' n' ∧
    monsterPairFanoXorPayload m n =
      monsterPairFanoXorPayload m' n' := by
  exact monsterPairFanoXorRuntimeStack_same_decoded_pair_cache_key m n m' n' a b
    (monsterPairFanoPoints_eq_some_of_phases m n a b hm hn)
    (monsterPairFanoPoints_eq_some_of_phases m' n' a b hm' hn') hab

/-- Numeric phase-key form: Monster columns with the same two Fano-visible
Aeon phases reduce to the same sorted `(Nat × Nat)` cache key. -/
theorem monsterPairFanoPhaseCacheKey_same_fano_phases
    (m n m' n' : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b)
    (hm' : monsterColumnPhase m' = fanoColumn a)
    (hn' : monsterColumnPhase n' = fanoColumn b)
    (hab : a ≠ b) :
    monsterPairFanoPhaseCacheKey m n =
      monsterPairFanoPhaseCacheKey m' n' := by
  exact monsterPairFanoPhaseCacheKey_same_decoded_pair m n m' n' a b
    (monsterPairFanoPoints_eq_some_of_phases m n a b hm hn)
    (monsterPairFanoPoints_eq_some_of_phases m' n' a b hm' hn') hab

/-- Direct-table admission: every emitted Monster/Fano phase cache key belongs
to the finite 21-key Fano table. -/
theorem monsterPairFanoPhaseCacheKey_emits_only_table_keys
    (m n : Nat) (key : Nat × Nat)
    (hkey : monsterPairFanoPhaseCacheKey m n = some key) :
    key ∈ fanoPhaseCacheKeyTable := by
  unfold monsterPairFanoPhaseCacheKey at hkey
  cases hdecode : monsterPairFanoPoints m n with
  | none => simp [hdecode] at hkey
  | some pair =>
      cases pair with
      | mk a b =>
          by_cases hab : a ≠ b
          · simp [hdecode, hab] at hkey
            rw [← hkey]
            exact fanoPairPhaseCacheKey_mem_table a b hab
          · simp [hdecode, hab] at hkey

/-- Existence form for runtime adapters: if a Monster/Fano numeric phase key
is emitted, then it is one of exactly the 21 direct-table entries. -/
theorem monsterPairFanoPhaseCacheKey_direct_table_admission
    (m n : Nat) :
    (∃ key, monsterPairFanoPhaseCacheKey m n = some key) →
      ∃ key,
        monsterPairFanoPhaseCacheKey m n = some key ∧
        key ∈ fanoPhaseCacheKeyTable ∧
        fanoPhaseCacheKeyTable.length = 21 := by
  intro hemits
  obtain ⟨key, hkey⟩ := hemits
  exact ⟨key, hkey,
    monsterPairFanoPhaseCacheKey_emits_only_table_keys m n key hkey,
    fanoPhaseCacheKeyTable_length⟩

/-- Array-index admission: every emitted Monster/Fano phase key resolves to a
total `Fin 21` direct-table index. -/
theorem monsterPairFanoPhaseCacheKey_direct_table_index_admission
    (m n : Nat) (key : Nat × Nat)
    (hkey : monsterPairFanoPhaseCacheKey m n = some key) :
    ∃ idx : Fin 21,
      idx =
        fanoPhaseCacheKeyTableIndex key
          (monsterPairFanoPhaseCacheKey_emits_only_table_keys m n key hkey) := by
  exact ⟨fanoPhaseCacheKeyTableIndex key
    (monsterPairFanoPhaseCacheKey_emits_only_table_keys m n key hkey), rfl⟩

/-- Decoded-pair form of the array-index admission. -/
theorem monsterPairFanoPhaseCacheKey_index_eq_pair_index_of_decode
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    ∃ key,
      ∃ hkey : monsterPairFanoPhaseCacheKey m n = some key,
        fanoPhaseCacheKeyTableIndex key
          (monsterPairFanoPhaseCacheKey_emits_only_table_keys m n key hkey) =
        fanoPairPhaseCacheKeyTableIndex a b hab := by
  refine ⟨fanoPairPhaseCacheKey a b, ?_⟩
  refine ⟨monsterPairFanoPhaseCacheKey_eq_of_decode m n a b hdecode hab, ?_⟩
  simp [fanoPairPhaseCacheKeyTableIndex, fanoPhaseCacheKeyTableIndex]

/-- Closed-form rank admission: every emitted Monster/Fano phase key has a
`Fin 21` index computed by arithmetic, and that rank agrees with the table
index. -/
theorem monsterPairFanoPhaseCacheKey_closed_rank_admission
    (m n : Nat) (key : Nat × Nat)
    (hkey : monsterPairFanoPhaseCacheKey m n = some key) :
    ∃ idx : Fin 21,
      idx =
        fanoPhaseCacheKeyRank key
          (monsterPairFanoPhaseCacheKey_emits_only_table_keys m n key hkey) ∧
      idx =
        fanoPhaseCacheKeyTableIndex key
          (monsterPairFanoPhaseCacheKey_emits_only_table_keys m n key hkey) := by
  let hmem := monsterPairFanoPhaseCacheKey_emits_only_table_keys m n key hkey
  refine ⟨fanoPhaseCacheKeyRank key hmem, rfl, ?_⟩
  exact fanoPhaseCacheKeyRank_eq_table_index key hmem

/-- Exact-hot packed runtime contract: once a Monster pair decodes to distinct
Fano endpoints, the default packed route is keyed by the finite 21-entry Fano
rank table and its word extractors recover admitted status, XOR payload, and
the sorted Fano phase gate. This is the Lean boundary mirrored by the Rust
`route_monster_fano_xor_payload_default_packed` hotpath. -/
theorem monsterPairFanoXorPackedRoute_exact_hot_cache_rank_word
    (m n : Nat) (a b : FanoPoint)
    (hdecode : monsterPairFanoPoints m n = some (a, b)) (hab : a ≠ b) :
    ∃ key,
      ∃ hkey : monsterPairFanoPhaseCacheKey m n = some key,
        key ∈ fanoPhaseCacheKeyTable ∧
        (∃ idx : Fin 21,
          idx =
            fanoPhaseCacheKeyRank key
              (monsterPairFanoPhaseCacheKey_emits_only_table_keys m n key hkey) ∧
          idx =
            fanoPhaseCacheKeyTableIndex key
              (monsterPairFanoPhaseCacheKey_emits_only_table_keys m n key hkey)) ∧
        packedFanoXorRouteWordStatusCode
            (packedFanoXorRouteHotWord a b) =
          packedFanoXorRouteStatusCode PackedFanoXorRouteStatus.admitted ∧
        packedFanoXorRouteWordValue
            (packedFanoXorRouteHotWord a b) =
          (collide a.state b.state).val ∧
        packedFanoXorRouteWordGate0
            (packedFanoXorRouteHotWord a b) =
          key.1 ∧
        packedFanoXorRouteWordGate1
            (packedFanoXorRouteHotWord a b) =
          key.2 := by
  let key := fanoPairPhaseCacheKey a b
  let hkey := monsterPairFanoPhaseCacheKey_eq_of_decode m n a b hdecode hab
  have hmem : key ∈ fanoPhaseCacheKeyTable :=
    fanoPairPhaseCacheKey_mem_table a b hab
  have hrank :=
    monsterPairFanoPhaseCacheKey_closed_rank_admission m n key hkey
  have hword := packedFanoXorRouteHotWord_extractors a b
  refine ⟨key, hkey, hmem, hrank, hword.1, hword.2.1, ?_, ?_⟩
  · exact hword.2.2.1
  · exact hword.2.2.2

theorem monsterAeonFanoCertificate_isSome_iff_decoded_distinct
    (m n : Nat) :
    (monsterAeonFanoCertificate m n true true).isSome = true ↔
      ∃ a b, monsterPairFanoPoints m n = some (a, b) ∧ a ≠ b := by
  constructor
  · intro hcert
    unfold monsterAeonFanoCertificate monsterPairAeonGate at hcert
    unfold monsterPairFanoPoints monsterColumnFanoPoint
    cases hm : fanoColumnPoint (monsterColumnPhase m) with
    | none =>
        cases hs : aeonPhaseFanoState (monsterColumnPhase m)
        · simp [hs] at hcert
        · have hsome : (aeonPhaseFanoState (monsterColumnPhase m)).isSome = true := by
            simp [hs]
          rw [aeonPhaseFanoState_isSome_eq_fanoColumnPoint_isSome, hm] at hsome
          cases hsome
    | some a =>
        cases hn : fanoColumnPoint (monsterColumnPhase n) with
        | none =>
            cases hs : aeonPhaseFanoState (monsterColumnPhase n)
            · simp [hs] at hcert
            · have hsome : (aeonPhaseFanoState (monsterColumnPhase n)).isSome = true := by
                simp [hs]
              rw [aeonPhaseFanoState_isSome_eq_fanoColumnPoint_isSome, hn] at hsome
              cases hsome
        | some b =>
            refine ⟨a, b, rfl, ?_⟩
            intro hab
            subst b
            have hmcol := fanoColumnPoint_eq_some_implies_column (monsterColumnPhase m) a hm
            have hncol := fanoColumnPoint_eq_some_implies_column (monsterColumnPhase n) a hn
            have hphase : monsterColumnPhase m = monsterColumnPhase n := by
              rw [hmcol, hncol]
            simp [hphase] at hcert
  · intro hdecode
    obtain ⟨a, b, hdecode, hab⟩ := hdecode
    have hphases := monsterPairFanoPoints_eq_some_implies_phases m n a b hdecode
    exact (monsterAeonFanoCertificate_validated_dispatches_to_xor_stack_of_phases
      m n a b hphases.1 hphases.2 hab).1

theorem monsterAeonFanoCertificate_isSome_iff_fano_xor_stack_exists
    (m n : Nat) :
    (monsterAeonFanoCertificate m n true true).isSome = true ↔
      ∃ stack, monsterPairFanoXorRuntimeStack m n = some stack := by
  constructor
  · intro hcert
    have hdecoded :=
      (monsterAeonFanoCertificate_isSome_iff_decoded_distinct m n).mp hcert
    exact (monsterPairFanoXorRuntimeStack_exists_iff_decoded_distinct m n).mpr hdecoded
  · intro hstack
    have hdecoded :=
      (monsterPairFanoXorRuntimeStack_exists_iff_decoded_distinct m n).mp hstack
    exact (monsterAeonFanoCertificate_isSome_iff_decoded_distinct m n).mpr hdecoded

theorem monsterAeonFanoCertificate_eq_canonical_of_phases
    (m n : Nat) (a b : FanoPoint)
    (hm : monsterColumnPhase m = fanoColumn a)
    (hn : monsterColumnPhase n = fanoColumn b) (hab : a ≠ b) :
    monsterAeonFanoCertificate m n true true =
      some (monsterAeonFanoCanonicalCertificate m n a b) := by
  unfold monsterAeonFanoCertificate monsterPairAeonGate
    monsterAeonFanoCanonicalCertificate fanoPairGate
  rw [hm, hn]
  cases a <;> cases b <;>
    simp [fanoColumn, pointIndex, aeonPhaseFanoState, FanoPoint.state, collide,
      tritonXor, xorNat] at hab ⊢

/-- Exact certificate/payload contract: an emitted Monster/Aeon/Fano
certificate is exactly the canonical record for decoded distinct Fano endpoints,
and that record's completion is the unique payload in the canonical XOR stack. -/
theorem monsterAeonFanoCertificate_eq_some_iff_canonical_xor_payload
    (m n : Nat) (cert : MonsterAeonFanoCertificate) :
    monsterAeonFanoCertificate m n true true = some cert ↔
      ∃ a b stack,
        monsterPairFanoPoints m n = some (a, b) ∧
        a ≠ b ∧
        cert = monsterAeonFanoCanonicalCertificate m n a b ∧
        monsterPairFanoXorRuntimeStack m n = some stack ∧
        stack = fanoPairCanonicalXorRuntimeStack a b ∧
        some cert.completion ∈ stack ∧
        collide (collide a.state b.state) cert.completion = godPosition := by
  constructor
  · intro hcert
    have hcertSome : (monsterAeonFanoCertificate m n true true).isSome = true := by
      rw [hcert]
      rfl
    obtain ⟨a, b, hdecode, hab⟩ :=
      (monsterAeonFanoCertificate_isSome_iff_decoded_distinct m n).mp hcertSome
    have hphases := monsterPairFanoPoints_eq_some_implies_phases m n a b hdecode
    have hcanonical :=
      monsterAeonFanoCertificate_eq_canonical_of_phases m n a b hphases.1 hphases.2 hab
    have hcert_eq : cert = monsterAeonFanoCanonicalCertificate m n a b := by
      rw [hcanonical] at hcert
      exact (Option.some.inj hcert).symm
    let stack := fanoPairCanonicalXorRuntimeStack a b
    have hstack : monsterPairFanoXorRuntimeStack m n = some stack :=
      monsterPairFanoXorRuntimeStack_eq_pair_canonical_of_decode m n a b hdecode hab
    refine ⟨a, b, stack, hdecode, hab, hcert_eq, hstack, rfl, ?_, ?_⟩
    · subst cert
      dsimp [monsterAeonFanoCanonicalCertificate]
      rw [← completePair_state_eq_xor a b hab]
      exact fanoPairCanonicalXorRuntimeStack_gate_payload a b hab
    · subst cert
      dsimp [monsterAeonFanoCanonicalCertificate]
      cases a <;> cases b <;>
        simp [godPosition, collide, tritonXor, xorNat, FanoPoint.state] at hab ⊢
  · intro hpayload
    obtain ⟨a, b, _stack, hdecode, hab, hcert_eq, _hstack, _hstack_eq,
      _hpayload, _hparity⟩ := hpayload
    have hphases := monsterPairFanoPoints_eq_some_implies_phases m n a b hdecode
    rw [hcert_eq]
    exact monsterAeonFanoCertificate_eq_canonical_of_phases m n a b
      hphases.1 hphases.2 hab

theorem monsterPairFanoXorPayload_isSome_iff_validated_certificate
    (m n : Nat) :
    (monsterPairFanoXorPayload m n).isSome = true ↔
      (monsterAeonFanoCertificate m n true true).isSome = true := by
  constructor
  · intro hpayload
    have hdecoded :=
      (monsterPairFanoXorPayload_exists_iff_decoded_distinct m n).mp
        (Option.isSome_iff_exists.mp hpayload)
    exact (monsterAeonFanoCertificate_isSome_iff_decoded_distinct m n).mpr hdecoded
  · intro hcert
    have hdecoded :=
      (monsterAeonFanoCertificate_isSome_iff_decoded_distinct m n).mp hcert
    exact Option.isSome_iff_exists.mpr
      ((monsterPairFanoXorPayload_exists_iff_decoded_distinct m n).mpr hdecoded)

theorem monsterPairFanoXorPayload_eq_certificate_completion
    (m n : Nat) (cert : MonsterAeonFanoCertificate)
    (hcert : monsterAeonFanoCertificate m n true true = some cert) :
    monsterPairFanoXorPayload m n = some cert.completion := by
  obtain ⟨a, b, _stack, hdecode, hab, hcert_eq, _hstack, _hstack_eq,
    _hpayload, _hparity⟩ :=
    (monsterAeonFanoCertificate_eq_some_iff_canonical_xor_payload m n cert).mp hcert
  rw [hcert_eq]
  dsimp [monsterAeonFanoCanonicalCertificate]
  rw [← completePair_state_eq_xor a b hab]
  exact monsterPairFanoXorPayload_eq_completion_of_decode m n a b hdecode hab

theorem monsterPairFanoXorPackedRoute_preserves_validated_certificate_payload
    (m n : Nat) (cert : MonsterAeonFanoCertificate)
    (hcert : monsterAeonFanoCertificate m n true true = some cert) :
    packedFanoXorRoutePayload (monsterPairFanoXorPackedRoute m n true true) =
      some cert.completion := by
  rw [monsterPairFanoXorPackedRoute_payload_eq_stack_free m n]
  exact monsterPairFanoXorPayload_eq_certificate_completion m n cert hcert

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

theorem monsterAeonFanoCanonicalCertificate_swap_xor_invariant
    (m n : Nat) (a b : FanoPoint) (hab : a ≠ b) :
    let cert := monsterAeonFanoCanonicalCertificate m n a b
    let swapped := monsterAeonFanoCanonicalCertificate n m b a
    cert.aeonGate = swapped.aeonGate ∧
      cert.completion = swapped.completion ∧
      cert.positiveGate = swapped.positiveGate ∧
      swapped.orientationSign = -cert.orientationSign ∧
      fanoPairCanonicalXorRuntimeStack a b =
        fanoPairCanonicalXorRuntimeStack b a ∧
      some cert.completion ∈ fanoPairCanonicalXorRuntimeStack a b ∧
      some swapped.completion ∈ fanoPairCanonicalXorRuntimeStack b a := by
  dsimp [monsterAeonFanoCanonicalCertificate]
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · exact (fano_plucker_sign_shadow_certificate a b hab).1
  · exact (fano_plucker_sign_shadow_certificate a b hab).2.2.1
  · exact (fano_plucker_sign_shadow_certificate a b hab).2.2.2
  · cases a <;> cases b <;> first | contradiction | native_decide
  · rw [← completePair_state_eq_xor a b hab]
    exact fanoPairCanonicalXorRuntimeStack_gate_payload a b hab
  · rw [← completePair_state_eq_xor b a (Ne.symm hab)]
    exact fanoPairCanonicalXorRuntimeStack_gate_payload b a (Ne.symm hab)

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
        (monsterAeonFanoCertificate m n true true).isSome = true ∧
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
  have hvalidated :=
    monsterAeonFanoCertificate_validated_dispatches_to_xor_stack_of_phases m n a b hm hn hab
  have hcert :=
    monster_aeon_projection_to_fano_xor_runtime_certificate_of_phases m n a b hm hn hab
  exact ⟨hvalidated.1, hcert.1, hcert.2.1, hcert.2.2.1, hcert.2.2.2.1,
    hcert.2.2.2.2.1, hcert.2.2.2.2.2.1, hcert.2.2.2.2.2.2.1,
    hcert.2.2.2.2.2.2.2.1, hcert.2.2.2.2.2.2.2.2.1,
    hcert.2.2.2.2.2.2.2.2.2.1, hcert.2.2.2.2.2.2.2.2.2.2⟩

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

/-- Compact runtime wire magic for the FANO transport payload. These are the
ASCII bytes `FANO`, modeled as natural bytes so the theorem can mirror the
TypeScript/Rust wire contract without importing an IO byte-array layer. -/
def fanoWireMagic : List Nat :=
  [70, 65, 78, 79]

def u24WireBytes (n : Nat) : List Nat :=
  [n / 65536, (n % 65536) / 256, n % 256]

def u24WireDecode (hi mid lo : Nat) : Nat :=
  hi * 65536 + mid * 256 + lo

/-- The eleven-byte FANO transport payload:
`FANO || lhs:u24 || rhs:u24 || flags`. The default flag byte `3` means both
finite residual and fingerprint checks have already admitted the XOR route. -/
def fanoWirePayload (lhs rhs : Nat) : List Nat :=
  fanoWireMagic ++ u24WireBytes lhs ++ u24WireBytes rhs ++ [3]

def fanoWireDecodeColumns : List Nat → Option (Nat × Nat × Bool × Bool)
  | [70, 65, 78, 79, a2, a1, a0, b2, b1, b0, flags] =>
      if a2 < 256 ∧ a1 < 256 ∧ a0 < 256 ∧
          b2 < 256 ∧ b1 < 256 ∧ b0 < 256 ∧ flags < 256 then
        some (
          u24WireDecode a2 a1 a0,
          u24WireDecode b2 b1 b0,
          flags % 2 = 1,
          (flags / 2) % 2 = 1
        )
      else none
  | _ => none

def fanoWireRouteCertificate (payload : List Nat) :
    Option MonsterAeonFanoCertificate :=
  match fanoWireDecodeColumns payload with
  | some (lhs, rhs, residualValidated, fingerprintVerified) =>
      monsterAeonFanoCertificate lhs rhs residualValidated fingerprintVerified
  | none => none

def u16WireBytes (n : Nat) : List Nat :=
  [(n / 256) % 256, n % 256]

def u16WireDecode (payload : List Nat) : Option Nat :=
  match payload with
  | [hi, lo] =>
      if hi < 256 ∧ lo < 256 then
        some (hi * 256 + lo)
      else none
  | _ => none

theorem u16WireBytes_decode_round_trip (n : Nat) (h : n < 65536) :
    u16WireDecode (u16WireBytes n) = some n := by
  unfold u16WireDecode u16WireBytes
  have hhi : (n / 256) % 256 < 256 := Nat.mod_lt _ (by decide)
  have hlo : n % 256 < 256 := Nat.mod_lt _ (by decide)
  simp [hhi, hlo]
  rw [Nat.mod_eq_of_lt (show n / 256 < 256 from Nat.div_lt_of_lt_mul h)]
  rw [Nat.mul_comm (n / 256) 256]
  exact Nat.div_add_mod n 256

theorem packedFanoXorRouteWord_u16WireBytes_decode_round_trip
    (status : PackedFanoXorRouteStatus) (value : Fin 8)
    (gate0 gate1 : Fin 16) :
    u16WireDecode
        (u16WireBytes (packedFanoXorRouteWord status value gate0 gate1)) =
      some (packedFanoXorRouteWord status value gate0 gate1) := by
  apply u16WireBytes_decode_round_trip
  have hstatus : packedFanoXorRouteStatusCode status ≤ 3 := by
    cases status <;> simp [packedFanoXorRouteStatusCode]
  have hvalue : value.val ≤ 7 := Nat.le_of_lt_succ value.isLt
  have hgate0 : gate0.val ≤ 15 := Nat.le_of_lt_succ gate0.isLt
  have hgate1 : gate1.val ≤ 15 := Nat.le_of_lt_succ gate1.isLt
  unfold packedFanoXorRouteWord
  calc packedFanoXorRouteStatusCode status * 2048 + gate1.val * 128 + gate0.val * 8 + value.val
      ≤ 3 * 2048 + 15 * 128 + 15 * 8 + 7 := by
        apply Nat.add_le_add
        · apply Nat.add_le_add
          · apply Nat.add_le_add
            · exact Nat.mul_le_mul_right 2048 hstatus
            · exact Nat.mul_le_mul_right 128 hgate1
          · exact Nat.mul_le_mul_right 8 hgate0
        · exact hvalue
    _ = 8191 := by decide
    _ < 65536 := by decide

theorem packedFanoXorRouteWord_lt_u16
    (status : PackedFanoXorRouteStatus) (value : Fin 8)
    (gate0 gate1 : Fin 16) :
    packedFanoXorRouteWord status value gate0 gate1 < 65536 := by
  have hstatus : packedFanoXorRouteStatusCode status ≤ 3 := by
    cases status <;> simp [packedFanoXorRouteStatusCode]
  have hvalue : value.val ≤ 7 := Nat.le_of_lt_succ value.isLt
  have hgate0 : gate0.val ≤ 15 := Nat.le_of_lt_succ gate0.isLt
  have hgate1 : gate1.val ≤ 15 := Nat.le_of_lt_succ gate1.isLt
  unfold packedFanoXorRouteWord
  calc packedFanoXorRouteStatusCode status * 2048 + gate1.val * 128 + gate0.val * 8 + value.val
      ≤ 3 * 2048 + 15 * 128 + 15 * 8 + 7 := by
        apply Nat.add_le_add
        · apply Nat.add_le_add
          · apply Nat.add_le_add
            · exact Nat.mul_le_mul_right 2048 hstatus
            · exact Nat.mul_le_mul_right 128 hgate1
          · exact Nat.mul_le_mul_right 8 hgate0
        · exact hvalue
    _ = 8191 := by decide
    _ < 65536 := by decide

def packedFanoXorRouteWireWord (route : PackedFanoXorRoute) : Option Nat :=
  match route.payload with
  | some value =>
      match route.aeonGate with
      | [gate0, gate1] =>
          some (packedFanoXorRouteWord route.status value
            ⟨gate0 % 16, Nat.mod_lt _ (by decide)⟩
            ⟨gate1 % 16, Nat.mod_lt _ (by decide)⟩)
      | _ => none
  | none =>
      match route.aeonGate with
      | [gate0, gate1] =>
          some (packedFanoXorRouteWord route.status ⟨0, by decide⟩
            ⟨gate0 % 16, Nat.mod_lt _ (by decide)⟩
            ⟨gate1 % 16, Nat.mod_lt _ (by decide)⟩)
      | [] =>
          some (packedFanoXorRouteWord route.status ⟨0, by decide⟩
            ⟨0, by decide⟩ ⟨0, by decide⟩)
      | _ => none

def fanoWireRouteWord (payload : List Nat) : Option Nat :=
  match fanoWireDecodeColumns payload with
  | some (lhs, rhs, residualValidated, fingerprintVerified) =>
      packedFanoXorRouteWireWord
        (monsterPairFanoXorPackedRoute lhs rhs residualValidated fingerprintVerified)
  | none => none

def fanoWirePackedRouteResponse (payload : List Nat) : List Nat :=
  match fanoWireRouteWord payload with
  | some word => [1] ++ u16WireBytes word
  | none => [0, 255, 255]

def fanoWirePackedRouteResponseWord : List Nat → Option Nat
  | [1, hi, lo] => u16WireDecode [hi, lo]
  | _ => none

theorem packedFanoXorRouteHotPositiveHint_canonical_wire :
    packedFanoXorRouteHotWord FanoPoint.b001 FanoPoint.b010 = 131 ∧
    packedFanoXorRouteHotPositiveHintWord FanoPoint.b001 FanoPoint.b010 =
      8323 ∧
    packedFanoXorRouteWordStatusCode
        (packedFanoXorRouteHotPositiveHintWord FanoPoint.b001 FanoPoint.b010) =
      packedFanoXorRouteStatusCode PackedFanoXorRouteStatus.admitted ∧
    packedFanoXorRouteWordValue
        (packedFanoXorRouteHotPositiveHintWord FanoPoint.b001 FanoPoint.b010) =
      3 ∧
    packedFanoXorRouteWordGate0
        (packedFanoXorRouteHotPositiveHintWord FanoPoint.b001 FanoPoint.b010) =
      0 ∧
    packedFanoXorRouteWordGate1
        (packedFanoXorRouteHotPositiveHintWord FanoPoint.b001 FanoPoint.b010) =
      1 ∧
    fanoWirePackedRouteResponseWord [1, 32, 131] = some 8323 := by
  native_decide

theorem packedFanoXorRouteWireWord_lt_u16
    (route : PackedFanoXorRoute) (word : Nat)
    (hword : packedFanoXorRouteWireWord route = some word) :
    word < 65536 := by
  unfold packedFanoXorRouteWireWord at hword
  cases hpayload : route.payload with
  | some value =>
      cases hgate : route.aeonGate with
      | nil => simp [hpayload, hgate] at hword
      | cons gate0 gateTail =>
          cases gateTail with
          | nil => simp [hpayload, hgate] at hword
          | cons gate1 rest =>
              cases rest with
              | nil =>
                  simp [hpayload, hgate] at hword
                  rw [← hword]
                  exact packedFanoXorRouteWord_lt_u16 route.status value
                    ⟨gate0 % 16, Nat.mod_lt _ (by decide)⟩
                    ⟨gate1 % 16, Nat.mod_lt _ (by decide)⟩
              | cons _ _ => simp [hpayload, hgate] at hword
  | none =>
      cases hgate : route.aeonGate with
      | nil =>
          simp [hpayload, hgate] at hword
          rw [← hword]
          exact packedFanoXorRouteWord_lt_u16 route.status ⟨0, by decide⟩
            ⟨0, by decide⟩ ⟨0, by decide⟩
      | cons gate0 gateTail =>
          cases gateTail with
          | nil => simp [hpayload, hgate] at hword
          | cons gate1 rest =>
              cases rest with
              | nil =>
                  simp [hpayload, hgate] at hword
                  rw [← hword]
                  exact packedFanoXorRouteWord_lt_u16 route.status ⟨0, by decide⟩
                    ⟨gate0 % 16, Nat.mod_lt _ (by decide)⟩
                    ⟨gate1 % 16, Nat.mod_lt _ (by decide)⟩
              | cons _ _ => simp [hpayload, hgate] at hword

theorem fanoWireRouteWord_lt_u16
    (payload : List Nat) (word : Nat)
    (hword : fanoWireRouteWord payload = some word) :
    word < 65536 := by
  unfold fanoWireRouteWord at hword
  cases hdecoded : fanoWireDecodeColumns payload with
  | none =>
      simp [hdecoded] at hword
  | some decoded =>
      rcases decoded with ⟨lhs, rhs, residualValidated, fingerprintVerified⟩
      simp [hdecoded] at hword
      exact packedFanoXorRouteWireWord_lt_u16
        (monsterPairFanoXorPackedRoute lhs rhs residualValidated fingerprintVerified)
        word hword

theorem fanoWirePackedRouteResponse_decode_round_trip
    (payload : List Nat) (word : Nat)
    (hword : fanoWireRouteWord payload = some word) :
    fanoWirePackedRouteResponseWord
        (fanoWirePackedRouteResponse payload) = some word := by
  unfold fanoWirePackedRouteResponse fanoWirePackedRouteResponseWord
  rw [hword]
  exact u16WireBytes_decode_round_trip word
    (fanoWireRouteWord_lt_u16 payload word hword)

theorem fano_wire_payload_routes_visible_monster_pair :
    fanoWirePayload 0 13 = [70, 65, 78, 79, 0, 0, 0, 0, 0, 13, 3] ∧
    fanoWireDecodeColumns (fanoWirePayload 0 13) =
      some (0, 13, true, true) ∧
    fanoWireRouteCertificate (fanoWirePayload 0 13) =
      monsterAeonFanoCertificate 0 13 true true ∧
    fanoWireRouteCertificate (fanoWirePayload 0 13) =
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
      } := by
  native_decide

theorem fano_wire_payload_emits_packed_route_word :
    fanoWireRouteWord (fanoWirePayload 0 13) =
      some (packedFanoXorRouteHotWord FanoPoint.b001 FanoPoint.b010) ∧
    fanoWirePackedRouteResponse (fanoWirePayload 0 13) =
      [1, 0, 131] ∧
    packedFanoXorRouteWordStatusCode
        (packedFanoXorRouteHotWord FanoPoint.b001 FanoPoint.b010) =
      packedFanoXorRouteStatusCode PackedFanoXorRouteStatus.admitted ∧
    packedFanoXorRouteWordValue
        (packedFanoXorRouteHotWord FanoPoint.b001 FanoPoint.b010) = 3 ∧
    packedFanoXorRouteWordGate0
        (packedFanoXorRouteHotWord FanoPoint.b001 FanoPoint.b010) = 0 ∧
    packedFanoXorRouteWordGate1
        (packedFanoXorRouteHotWord FanoPoint.b001 FanoPoint.b010) = 1 := by
  native_decide

theorem fano_wire_payload_rejects_unadmitted_shadow :
    fanoWireRouteCertificate [70, 65, 78, 79, 0, 0, 0, 0, 0, 13, 1] = none ∧
    fanoWireRouteCertificate [70, 65, 78, 79, 0, 0, 0, 0, 0, 13, 2] = none ∧
    fanoWireRouteCertificate [70, 65, 78, 79, 0, 0, 0, 0, 0, 13, 0] = none := by
  native_decide

/-- Bounded runtime atlas witness: each adjacent visible Aeon phase pair can be
encoded as compact FANO wire and decoded back to the same Monster certificate.
This keeps the executable contract finite while the general u24 arithmetic
round-trip is promoted into its own theorem target. -/
theorem fano_wire_visible_phase_runtime_atlas :
    fanoWireRouteCertificate (fanoWirePayload 0 13) =
      monsterAeonFanoCertificate 0 13 true true ∧
    fanoWireRouteCertificate (fanoWirePayload 1 14) =
      monsterAeonFanoCertificate 1 14 true true ∧
    fanoWireRouteCertificate (fanoWirePayload 2 15) =
      monsterAeonFanoCertificate 2 15 true true ∧
    fanoWireRouteCertificate (fanoWirePayload 3 16) =
      monsterAeonFanoCertificate 3 16 true true ∧
    fanoWireRouteCertificate (fanoWirePayload 4 17) =
      monsterAeonFanoCertificate 4 17 true true ∧
    fanoWireRouteCertificate (fanoWirePayload 5 18) =
      monsterAeonFanoCertificate 5 18 true true := by
  native_decide

theorem fano_wire_same_phase_runtime_rejects :
    fanoWireRouteCertificate (fanoWirePayload 0 12) = none ∧
    fanoWireRouteCertificate (fanoWirePayload 1 13) = none ∧
    fanoWireRouteCertificate (fanoWirePayload 6 18) = none := by
  native_decide

end FanoGrassmannianMesh
end Gnosis
