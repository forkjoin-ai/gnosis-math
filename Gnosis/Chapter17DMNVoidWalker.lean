/-!
# Chapter 17 DMN Void Walker

Init-only arithmetic witnesses for the Chapter 17 DMN/VGI ledger rows.

The deleted executable companion used decimal tolerances.  This module keeps
the falsifiable arithmetic in integer-scaled form: permyriad percentages for
DMN energy and mind-wandering, permille VGI, and exact rational CVI.
-/

namespace Gnosis.Chapter17DMNVoidWalker

def KEnv : Nat := 22
def KTotal : Nat := 20
def KConsciousTenths : Nat := 86

def permyriad (numerator denominator : Nat) : Nat :=
  numerator * 10000 / denominator

def permille (numerator denominator : Nat) : Nat :=
  numerator * 1000 / denominator

/-- DMN energy allocation `(K-1)/K` at `K=22`, scaled by 10,000. -/
def dmnEnergyPermyriad : Nat :=
  permyriad (KEnv - 1) KEnv

/-- Mind-wandering duty cycle `(K-1)/(2K-1)` at `K=22`, scaled by 10,000. -/
def mindWanderingPermyriad : Nat :=
  permyriad (KEnv - 1) (2 * KEnv - 1)

/-- VGI `(K_total-1)/(K_env-1)` for K_total=20 and K_env=22, scaled by 1,000. -/
def voidGainIndexPermille : Nat :=
  permille (KTotal - 1) (KEnv - 1)

/-- Conscious visibility index `(8.6-1)/(20-1)`, represented in tenths. -/
def consciousVisibilityNumerator : Nat := KConsciousTenths - 10
def consciousVisibilityDenominator : Nat := (KTotal - 1) * 10

theorem dmn_energy_matches_95_percent_band :
    dmnEnergyPermyriad = 9545 := by
  native_decide

theorem dmn_energy_within_45_basis_points_of_raichle :
    dmnEnergyPermyriad - 9500 ≤ 45 := by
  native_decide

theorem mind_wandering_matches_kg_band :
    mindWanderingPermyriad = 4883 := by
  native_decide

theorem mind_wandering_within_200_basis_points_of_kg :
    mindWanderingPermyriad - 4690 ≤ 200 := by
  native_decide

theorem void_gain_index_matches_ledger_floor :
    voidGainIndexPermille = 904 := by
  native_decide

theorem conscious_visibility_is_two_fifths :
    consciousVisibilityNumerator * 5 =
      consciousVisibilityDenominator * 2 := by
  native_decide

/-- The visible/conscious slice is strictly smaller than the total void-walking carrier. -/
theorem conscious_slice_strictly_subtotal :
    consciousVisibilityNumerator < consciousVisibilityDenominator := by
  native_decide

inductive NeuroProfile where
  | neurotypical
  | autistic
  | adhd
  | audhd
deriving DecidableEq, Repr

inductive SupportEnvironment where
  | narrow
  | autismMatched
  | adhdMatched
  | audhdMatched
deriving DecidableEq, Repr

def perceivedK : NeuroProfile → Nat
  | .neurotypical => 3
  | .autistic => 8
  | .adhd => 3
  | .audhd => 8

def actualK : SupportEnvironment → Nat
  | .narrow => 3
  | .autismMatched => 8
  | .adhdMatched => 3
  | .audhdMatched => 8

def matchedEnvironment : NeuroProfile → SupportEnvironment
  | .neurotypical => .narrow
  | .autistic => .autismMatched
  | .adhd => .adhdMatched
  | .audhd => .audhdMatched

theorem matched_environment_equalizes_k
    (profile : NeuroProfile) :
    perceivedK profile = actualK (matchedEnvironment profile) := by
  cases profile <;> rfl

theorem autistic_has_wider_aperture_than_neurotypical :
    perceivedK .neurotypical < perceivedK .autistic := by
  decide

theorem audhd_matches_wide_environment :
    perceivedK .audhd = actualK .audhdMatched := by
  rfl

end Gnosis.Chapter17DMNVoidWalker
