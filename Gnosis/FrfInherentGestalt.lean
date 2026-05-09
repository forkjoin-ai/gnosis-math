import Init
import Gnosis.RankingFrfBridge

/-!
# FRF inherent gestalt (Init-only)

**Gestalt.** Fork/race/fold is not an optional annotation layered onto unstructured bits: every `Nat`
already occupies a *unique* one-step triton position `n = 3·k + r` with `r < 3`. That quotient/fiber
split is the arithmetic shadow of the triangle.

**Quotient side (GF(2) metaphor).** Bitwise XOR merges commute with partitioning data: folding XOR over
a concatenation is XOR of folds (`xorMerge_append`). That is the formal “schedule-blind” glue quoted in
parallel reductions.

**Fiber side (triadic lanes).** Independent triadic accumulators compose with `triadAdd`: a five-lane
`Fin 5 → Fin 3` witness vector combines pointwise as `combineFiveTriads` — same associative/commutative
monoid laws as a single lane, but retaining component witnesses.

This module stays minimal: no Mathlib, no `sorry`. It connects `RankingFrfBridge`’s spine with explicit
uniqueness (fiber coordinates are data already carried by `Nat`) and with XOR-style quotient merging.

See `Gnosis.FrfWitnessTower` for the dependent witness subsingleton, base‑3 digit tower isomorphism with
`Nat`, triadic word merge, and the combined observation monoid (`Bool × (Fin 5 → Fin 3)`).
-/

namespace Gnosis
namespace FrfInherentGestalt

open Gnosis.RankingFrfBridge

/-! ## Triangle coordinates are unique (intrinsic to `Nat`) -/

theorem frf_fork_unique (k k' : Nat) (r r' : Fin 3)
    (h : frfFork k r.val = frfFork k' r'.val) : k = k' ∧ r = r' := by
  unfold frfFork at h
  have hr : r.val < 3 := r.isLt
  have hr' : r'.val < 3 := r'.isLt
  have hl : (3 * k + r.val) % 3 = r.val % 3 := by
    simp [Nat.mul_comm 3 k, Nat.add_comm]
  have hrEq : r.val = r'.val := by
    calc
      r.val = r.val % 3 := (Nat.mod_eq_of_lt hr).symm
      _ = (3 * k + r.val) % 3 := hl.symm
      _ = (3 * k' + r'.val) % 3 := congrArg (fun n => n % 3) h
      _ = r'.val % 3 := by
            simp [Nat.mul_comm 3 k', Nat.add_comm]
      _ = r'.val := Nat.mod_eq_of_lt hr'
  have hrFin : r = r' := Fin.ext hrEq
  subst hrFin
  have hk : 3 * k = 3 * k' := Nat.add_right_cancel h
  exact ⟨Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) hk, rfl⟩

/-- Division algorithm: every `Nat` is literally one triton fork step from its quotient (intrinsic shape). -/
theorem nat_is_fr_fork (n : Nat) : n = frfFork (n / 3) (n % 3) := by
  unfold frfFork
  exact (Nat.div_add_mod n 3).symm

theorem nat_mod_remainder_lt_three (n : Nat) : n % 3 < 3 :=
  Nat.mod_lt n (by decide : 0 < 3)

/-! ## Triadic lane combine (parallel-safe on each lane) -/

def triadAdd (a b : Fin 3) : Fin 3 :=
  ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by decide : 0 < 3)⟩

theorem triadAdd_comm (a b : Fin 3) : triadAdd a b = triadAdd b a := by
  unfold triadAdd
  apply Fin.ext
  simp [Nat.add_comm]

theorem triadAdd_assoc (a b c : Fin 3) : triadAdd (triadAdd a b) c = triadAdd a (triadAdd b c) := by
  apply Fin.ext
  dsimp [triadAdd]
  rw [Nat.mod_add_mod (a.val + b.val) 3 c.val]
  rw [Nat.add_mod_mod a.val (b.val + c.val) 3]
  rw [Nat.add_assoc]

/-! ### Five independent triadic lanes (Fin 5 → Fin 3) -/

abbrev FiveTriadWitness := Fin 5 → Fin 3

def combineFiveTriads (v w : FiveTriadWitness) : FiveTriadWitness :=
  fun i => triadAdd (v i) (w i)

theorem combineFiveTriads_comm (v w : FiveTriadWitness) :
    combineFiveTriads v w = combineFiveTriads w v := by
  funext i
  simp [combineFiveTriads, triadAdd_comm]

theorem combineFiveTriads_assoc (u v w : FiveTriadWitness) :
    combineFiveTriads (combineFiveTriads u v) w = combineFiveTriads u (combineFiveTriads v w) := by
  funext i
  simp [combineFiveTriads, triadAdd_assoc]

/-! ## XOR quotient: merge-invariant under partition (schedule-blind fold) -/

def xorMerge : List Bool → Bool
  | [] => false
  | b :: bs => b.xor (xorMerge bs)

theorem xorMerge_nil : xorMerge [] = false :=
  rfl

theorem xorMerge_append (xs ys : List Bool) :
    xorMerge (xs ++ ys) = (xorMerge xs).xor (xorMerge ys) := by
  induction xs with
  | nil =>
      simp [xorMerge]
  | cons x xs ih =>
      simp [xorMerge, ih]

/-! ## Certificates bundled for downstream citation -/

/-- Single certificate: triangle coordinates are unique; XOR merges split across `++`; five triads associate. -/
theorem frf_gestalt_core_certificate (k k' : Nat) (r r' : Fin 3) (xs ys : List Bool) (u v w : FiveTriadWitness)
    (hfork : frfFork k r.val = frfFork k' r'.val) :
    (k = k' ∧ r = r') ∧
      xorMerge (xs ++ ys) = (xorMerge xs).xor (xorMerge ys) ∧
        combineFiveTriads (combineFiveTriads u v) w =
          combineFiveTriads u (combineFiveTriads v w) :=
  ⟨frf_fork_unique k k' r r' hfork, xorMerge_append xs ys, combineFiveTriads_assoc u v w⟩

end FrfInherentGestalt
end Gnosis
