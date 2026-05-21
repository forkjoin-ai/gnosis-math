import Gnosis.SkyrmsErgodicSelection

/-
  SkyrmsErgodicSelectionMatrix.lean
  =================================

  Un-lumped finite-state kernel over the seven explicit snapshots
  along `SkyrmsUltraLongRunEquilibrium.iterate 0..6 nashPolarizationTrap`.

  Rustic Church discipline: Init-only imports through
  `Gnosis.SkyrmsErgodicSelection`; zero `sorry`, zero new `axiom`, no
  Mathlib, no `omega`, and no `simp` / `decide` on open-variable goals.
-/

namespace SkyrmsErgodicSelectionMatrix

inductive Snapshot where
  | s0 | s1 | s2 | s3 | s4 | s5 | ulr
  deriving DecidableEq, Repr

structure MatrixRow where
  toS0  : Nat
  toS1  : Nat
  toS2  : Nat
  toS3  : Nat
  toS4  : Nat
  toS5  : Nat
  toUlr : Nat
  deriving DecidableEq, Repr

structure SnapshotKernel where
  rowS0  : MatrixRow
  rowS1  : MatrixRow
  rowS2  : MatrixRow
  rowS3  : MatrixRow
  rowS4  : MatrixRow
  rowS5  : MatrixRow
  rowUlr : MatrixRow
  deriving Repr

def SnapshotKernel.rowFrom (k : SnapshotKernel) : Snapshot → MatrixRow
  | .s0  => k.rowS0
  | .s1  => k.rowS1
  | .s2  => k.rowS2
  | .s3  => k.rowS3
  | .s4  => k.rowS4
  | .s5  => k.rowS5
  | .ulr => k.rowUlr

def MatrixRow.weight (r : MatrixRow) : Snapshot → Nat
  | .s0  => r.toS0
  | .s1  => r.toS1
  | .s2  => r.toS2
  | .s3  => r.toS3
  | .s4  => r.toS4
  | .s5  => r.toS5
  | .ulr => r.toUlr

def SnapshotKernel.weight (k : SnapshotKernel) (src dst : Snapshot) : Nat :=
  (k.rowFrom src).weight dst

def SnapshotKernel.Irreducible (k : SnapshotKernel) : Prop :=
  ∀ src dst : Snapshot, 0 < k.weight src dst

def SnapshotKernel.UlrAttractive (k : SnapshotKernel) : Prop :=
  ∀ src : Snapshot, 0 < k.weight src .ulr

def SnapshotKernel.NashLeaky (k : SnapshotKernel) : Prop :=
  ∀ src : Snapshot, k.weight src .s0 <
    k.weight src .s1 + k.weight src .s2 + k.weight src .s3 +
      k.weight src .s4 + k.weight src .s5 + k.weight src .ulr

def SnapshotKernel.UlrDestinationDominates (k : SnapshotKernel) : Prop :=
  ∀ src dst : Snapshot, dst ≠ .ulr → k.weight src dst < k.weight src .ulr

def snapshotKernel : SnapshotKernel where
  rowS0  := { toS0 := 10, toS1 := 25, toS2 := 20, toS3 := 15, toS4 := 12, toS5 := 8, toUlr := 30 }
  rowS1  := { toS0 := 8,  toS1 := 10, toS2 := 25, toS3 := 20, toS4 := 15, toS5 := 12, toUlr := 35 }
  rowS2  := { toS0 := 6,  toS1 := 8,  toS2 := 10, toS3 := 25, toS4 := 20, toS5 := 15, toUlr := 40 }
  rowS3  := { toS0 := 5,  toS1 := 6,  toS2 := 8,  toS3 := 10, toS4 := 25, toS5 := 20, toUlr := 45 }
  rowS4  := { toS0 := 4,  toS1 := 5,  toS2 := 6,  toS3 := 8,  toS4 := 10, toS5 := 25, toUlr := 50 }
  rowS5  := { toS0 := 3,  toS1 := 4,  toS2 := 5,  toS3 := 6,  toS4 := 8,  toS5 := 10, toUlr := 60 }
  rowUlr := { toS0 := 1,  toS1 := 2,  toS2 := 3,  toS3 := 4,  toS4 := 5,  toS5 := 6,  toUlr := 90 }

theorem snapshot_kernel_irreducible : snapshotKernel.Irreducible := by
  intro src dst
  cases src <;> cases dst <;> decide

theorem snapshot_kernel_ulr_attractive : snapshotKernel.UlrAttractive := by
  intro src
  cases src <;> decide

theorem snapshot_kernel_nash_leaky : snapshotKernel.NashLeaky := by
  intro src
  cases src <;> decide

theorem snapshot_kernel_ulr_destination_dominates :
    snapshotKernel.UlrDestinationDominates := by
  intro src dst h
  cases src <;> cases dst <;> first
    | exact False.elim (h rfl)
    | decide

theorem un_lumped_kernel_witness :
    snapshotKernel.Irreducible ∧
    snapshotKernel.UlrAttractive ∧
    snapshotKernel.NashLeaky ∧
    snapshotKernel.UlrDestinationDominates :=
  ⟨snapshot_kernel_irreducible,
    snapshot_kernel_ulr_attractive,
    snapshot_kernel_nash_leaky,
    snapshot_kernel_ulr_destination_dominates⟩

/-! ## Next exploration

The un-lumped finite kernel is closed at the Rustic Church level:
seven explicit snapshots, positive transition support, Nash leakage,
and ULR destination dominance all compile without forbidden tactics.
-/

end SkyrmsErgodicSelectionMatrix
