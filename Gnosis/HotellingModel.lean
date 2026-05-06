import Init
import Gnosis.GodFormula

namespace Gnosis
namespace HotellingModel

open Gnosis (godWeight)

/-!
# Hotelling’s linear city — discrete core + FRF reading

**Classical map.** Hotelling’s spatial duopoly places two sellers on a line segment,
with consumers distributed along it and transportation cost proportional to
distance. Under mill pricing (fixed prices, equal across firms), the textbook
Nash outcome is **minimum differentiation** (both cluster at the median /
market center), while richer variants (price competition, more than two firms,
different distributions) change the equilibrium set.

This module does **not** import real analysis or calibrated demand. It mechanizes
the **discrete** comparison “which firm is nearer to an integer address `c`?” and
packages the standard **midpoint / majority split** characterization:

  with firms at `a < b` and a consumer at `c` **between** them (`a ≤ c ≤ b`),
  the consumer is strictly nearer to `a` than to `b` iff `2 * c < a + b`.

## FRF (fork–race–fold–vent) ledger reading

- **Fork** — the two independent location choices (`a` vs `b`): duplicated
  strategic openings on the same carrier segment.
- **Race** — demand rivalry along the 1D address line: each consumer “votes” for
  the nearer outlet (nearest-neighbor routing).
- **Fold** — the market aggregates at the **indifferent** address; the ledger
  fold is the partition induced by the order comparison `2 * c` vs `a + b`.
- **Vent** — transportation / distance acts as **lost surplus** (friction).
  We relate pairwise spatial separation `natDist a b` to `godWeight` by treating
  the segment scale `L` as the reconciliation budget `R` and the *clamped*
  differentiation `min (natDist a b) L` as **rejection mass** `v` in the God
  formula. Co-located firms have `v = 0` (maximum retained weight at that
  scale); far-apart firms push `v` toward `L`, driving `godWeight L v` toward the
  clinamen floor `1` — a discrete mirror of “competition stress consumes the
  fold margin” without claiming a literal economic identity with vNM payoffs.

Downstream narrative uses the same **honest separation** as ProspectTheory:
structural hooks are *not* proofs that agents maximize Hotelling profits in the
field—only that the formal layer matches the classical discrete geometry the
industry model names.
-/

/-! ## 1D distance on a Nat segment -/

/-- Unsigned distance between two addresses (symmetric `Nat` subtraction). -/
def natDist (x y : Nat) : Nat :=
  if _ : x ≤ y then y - x else x - y

theorem natDist_comm (x y : Nat) : natDist x y = natDist y x := by
  unfold natDist
  by_cases hxy : x ≤ y <;> by_cases hyx : y ≤ x
  · have : x = y := Nat.le_antisymm hxy hyx
    subst this
    rfl
  · -- x < y: both sides are `y - x`
    have _hlt : x < y := Nat.lt_of_le_of_ne hxy fun he => hyx (Nat.le_of_eq he.symm)
    simp [hxy, hyx]
  · -- y < x: both sides are `x - y`
    have _hlt : y < x := Nat.lt_of_le_of_ne hyx fun he => hxy (Nat.le_of_eq he.symm)
    simp [hxy, hyx]
  · have h₁ : y < x := Nat.lt_of_not_ge hxy
    have h₂ : x < y := Nat.lt_of_not_ge hyx
    exact (Nat.lt_irrefl x (Nat.lt_trans h₂ h₁)).elim

theorem natDist_self (x : Nat) : natDist x x = 0 := by
  unfold natDist
  simp

theorem natDist_pos_of_ne {x y : Nat} (h : x ≠ y) : 0 < natDist x y := by
  unfold natDist
  by_cases hxy : x ≤ y
  · have hlt : x < y := Nat.lt_of_le_of_ne hxy h
    simp [hxy, Nat.sub_pos_of_lt hlt]
  · have hlt : y < x := Nat.lt_of_not_ge hxy
    simp [hxy, Nat.sub_pos_of_lt hlt]

/-! ## Between two firms: strictly nearer to left ⇔ `2 * c < a + b` -/

theorem between_closer_left_iff_two_mul {a b c : Nat} (hac : a ≤ c) (hcb : c ≤ b) :
    c - a < b - c ↔ 2 * c < a + b := by
  have hab : a + b = a + (b - c) + c := by
    calc
      a + b = a + ((b - c) + c) := by rw [Nat.sub_add_cancel hcb]
      _ = a + (b - c) + c := by rw [Nat.add_assoc]
  constructor
  · intro h
    have hmid := (Nat.sub_lt_iff_lt_add' hac).mp h
    have hsum := Nat.add_lt_add_right hmid c
    rw [← Nat.two_mul c] at hsum
    rwa [← hab] at hsum
  · intro h
    rw [hab] at h
    -- use `c + c` on the left for `lt_of_add_lt_add_right`
    have hcc : c + c < a + (b - c) + c := by
      rw [Nat.two_mul c] at h
      exact h
    exact (Nat.sub_lt_iff_lt_add' hac).mpr (Nat.lt_of_add_lt_add_right hcc)

/-! ## God-form hook: differentiation as clamped rejection on scale `L` -/

/-- Map spatial separation onto rejections **clamped** to the city length `L`
(scale / budget for the accounting line). -/
def hotellingVent (L a b : Nat) : Nat :=
  min (natDist a b) L

theorem hotellingVent_le_L (L a b : Nat) : hotellingVent L a b ≤ L :=
  Nat.min_le_right _ _

theorem hotellingVent_le_dist (L a b : Nat) : hotellingVent L a b ≤ natDist a b :=
  Nat.min_le_left _ _

theorem godWeight_hotelling_colocation (L : Nat) :
    godWeight L (hotellingVent L 0 0) = L + 1 := by
  unfold hotellingVent natDist
  simp
  exact Gnosis.godWeight_ceiling L

theorem godWeight_hotelling_endpoint_separation (L : Nat) (_hL : 0 < L) :
    godWeight L (hotellingVent L 0 L) = 1 := by
  unfold hotellingVent natDist
  have h01 : (0 : Nat) ≤ L := Nat.zero_le L
  simp [h01, Nat.sub_zero]
  exact Gnosis.godWeight_floor L

/-! ## Small executable witnesses (Init-level checks) -/

theorem witness_two_mul_midpoint : 2 * 2 < 1 + 4 := by
  decide

theorem witness_between_compare :
    (2 : Nat) - 1 < 4 - 2 ↔ 2 * 2 < 1 + 4 := by
  exact between_closer_left_iff_two_mul (by decide) (by decide)

/-! ## N-dimensional discrete city (product lattice) -/

/-- L1 distance on two coordinate lists.
If lengths differ, extra coordinates are ignored by construction; downstream
uses should enforce equal-length vectors. -/
def l1Dist : List Nat → List Nat → Nat
  | [], [] => 0
  | x :: xs, y :: ys => natDist x y + l1Dist xs ys
  | _, _ => 0

theorem l1Dist_nil_left (ys : List Nat) : l1Dist [] ys = 0 := by
  cases ys <;> rfl

theorem l1Dist_nil_right (xs : List Nat) : l1Dist xs [] = 0 := by
  cases xs <;> rfl

theorem l1Dist_comm (xs ys : List Nat) : l1Dist xs ys = l1Dist ys xs := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp [l1Dist]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [l1Dist]
      | cons y ys =>
          simp [l1Dist, natDist_comm, ih, Nat.add_comm]

theorem l1Dist_self (xs : List Nat) : l1Dist xs xs = 0 := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [l1Dist, natDist_self, ih]

theorem l1Dist_pos_of_ne {xs ys : List Nat} (hlen : xs.length = ys.length) (hne : xs ≠ ys) :
    0 < l1Dist xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          cases hne rfl
      | cons _ _ =>
          cases hlen
  | cons x xs ih =>
      cases ys with
      | nil =>
          cases hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := Nat.succ.inj hlen
          by_cases hxy : x = y
          · subst hxy
            have htail : xs ≠ ys := by
              intro hEq
              exact hne (by simp [hEq])
            have hposTail : 0 < l1Dist xs ys := ih hlen' htail
            simp [l1Dist, natDist_self, hposTail]
          · have hposHead : 0 < natDist x y := natDist_pos_of_ne hxy
            exact Nat.add_pos_left hposHead _

/-- N-D Hotelling vent: clamp L1 differentiation to city budget `L`. -/
def hotellingVentN (L : Nat) (a b : List Nat) : Nat :=
  min (l1Dist a b) L

theorem hotellingVentN_le_L (L : Nat) (a b : List Nat) : hotellingVentN L a b ≤ L :=
  Nat.min_le_right _ _

theorem hotellingVentN_le_dist (L : Nat) (a b : List Nat) : hotellingVentN L a b ≤ l1Dist a b :=
  Nat.min_le_left _ _

theorem godWeight_hotellingN_colocation (L : Nat) (x : List Nat) :
    godWeight L (hotellingVentN L x x) = L + 1 := by
  unfold hotellingVentN
  simp [l1Dist_self]
  exact Gnosis.godWeight_ceiling L

/-- 1D embeds into N-D as singleton vectors. -/
theorem l1Dist_singleton (a b : Nat) : l1Dist [a] [b] = natDist a b := by
  simp [l1Dist]

theorem hotellingVent_singleton_eq (L a b : Nat) :
    hotellingVentN L [a] [b] = hotellingVent L a b := by
  simp [hotellingVentN, hotellingVent, l1Dist_singleton]

/-! ## Finite-city best responses and Nash witness (Level-2 game layer) -/

/-- Consumer `c` goes to the left firm at `x` if left distance is not larger. -/
def choosesLeft (x y c : Nat) : Bool :=
  decide (natDist c x ≤ natDist c y)

/-- Bool indicator as natural count mass. -/
def bit (b : Bool) : Nat :=
  cond b 1 0

/-- Left-firm demand mass on a fixed city with addresses `0..4`. -/
def leftDemand4 (x y : Nat) : Nat :=
  bit (choosesLeft x y 0) +
  bit (choosesLeft x y 1) +
  bit (choosesLeft x y 2) +
  bit (choosesLeft x y 3) +
  bit (choosesLeft x y 4)

/-- Strategy admissibility in the 5-point city. -/
def InCity4 (x : Nat) : Prop := x ≤ 4

/-- Best response for left firm against right location `y` in the finite city. -/
def IsBestResponse4 (y x : Nat) : Prop :=
  InCity4 x ∧
  leftDemand4 0 y ≤ leftDemand4 x y ∧
  leftDemand4 1 y ≤ leftDemand4 x y ∧
  leftDemand4 2 y ≤ leftDemand4 x y ∧
  leftDemand4 3 y ≤ leftDemand4 x y ∧
  leftDemand4 4 y ≤ leftDemand4 x y

/-- Symmetric Nash condition in the finite city. -/
def IsNash4 (x y : Nat) : Prop :=
  IsBestResponse4 y x ∧ IsBestResponse4 x y

/-- Concrete witness: center-center is a finite-city Nash profile. -/
theorem center_is_nash4 : IsNash4 2 2 := by
  unfold IsNash4 IsBestResponse4 InCity4
  constructor
  · repeat' constructor <;> native_decide
  · repeat' constructor <;> native_decide

/-- At the center profile, each firm carries full city mass under `≤` tie policy. -/
theorem center_left_demand4_full : leftDemand4 2 2 = 5 := by
  native_decide

end HotellingModel
end Gnosis
