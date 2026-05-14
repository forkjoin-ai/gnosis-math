import Init

namespace Gnosis
namespace PhilosophicalAllegories

/-!
# Philosophical Allegories

An Init-compatible restoration of the allegory layer.  The old module stated
many domain-specific philosophical applications against unavailable APIs; this
core keeps the reusable typed machinery: allegory carriers, non-identity
morphisms, composition, and distortion accounting.
-/

inductive AllegoryCarrier where
  | caveShadow
  | dividedLine
  | socraticElenchus
  | shipIdentity
  | twoTruths
deriving DecidableEq, Repr

structure AllegoryMorphism where
  source : AllegoryCarrier
  target : AllegoryCarrier
  bearing : Nat
  distortion : Nat

namespace AllegoryMorphism

def NonIdentity (morphism : AllegoryMorphism) : Prop :=
  morphism.source ≠ morphism.target

def informationGain (morphism : AllegoryMorphism) : Nat :=
  morphism.bearing - morphism.distortion

def compose (first second : AllegoryMorphism)
    (_hMatch : first.target = second.source) :
    AllegoryMorphism where
  source := first.source
  target := second.target
  bearing := first.bearing + second.bearing
  distortion := first.distortion + second.distortion

theorem compose_source
    (first second : AllegoryMorphism)
    (hMatch : first.target = second.source) :
    (first.compose second hMatch).source = first.source := by
  rfl

theorem compose_target
    (first second : AllegoryMorphism)
    (hMatch : first.target = second.source) :
    (first.compose second hMatch).target = second.target := by
  rfl

theorem compose_bearing_additive
    (first second : AllegoryMorphism)
    (hMatch : first.target = second.source) :
    (first.compose second hMatch).bearing =
      first.bearing + second.bearing := by
  rfl

theorem compose_distortion_additive
    (first second : AllegoryMorphism)
    (hMatch : first.target = second.source) :
    (first.compose second hMatch).distortion =
      first.distortion + second.distortion := by
  rfl

theorem positive_gain_when_distortion_bounded
    (morphism : AllegoryMorphism)
    (_hBearing : 0 < morphism.bearing)
    (hDistortion : morphism.distortion < morphism.bearing) :
    0 < morphism.informationGain := by
  unfold informationGain
  exact Nat.sub_pos_of_lt hDistortion

theorem identity_not_nonidentity
    (carrier : AllegoryCarrier)
    (bearing distortion : Nat) :
    ¬ ({ source := carrier
         target := carrier
         bearing := bearing
         distortion := distortion } : AllegoryMorphism).NonIdentity := by
  intro h
  exact h rfl

theorem nonidentity_source_target_distinct
    (morphism : AllegoryMorphism)
    (h : morphism.NonIdentity) :
    morphism.source ≠ morphism.target := h

end AllegoryMorphism

def caveToLine : AllegoryMorphism where
  source := .caveShadow
  target := .dividedLine
  bearing := 3
  distortion := 1

def lineToElenchus : AllegoryMorphism where
  source := .dividedLine
  target := .socraticElenchus
  bearing := 2
  distortion := 1

def shipToTwoTruths : AllegoryMorphism where
  source := .shipIdentity
  target := .twoTruths
  bearing := 4
  distortion := 2

theorem cave_to_line_nonidentity :
    caveToLine.NonIdentity := by
  intro h
  cases h

theorem line_to_elenchus_nonidentity :
    lineToElenchus.NonIdentity := by
  intro h
  cases h

theorem ship_to_two_truths_nonidentity :
    shipToTwoTruths.NonIdentity := by
  intro h
  cases h

def caveToElenchus : AllegoryMorphism :=
  caveToLine.compose lineToElenchus rfl

theorem cave_to_elenchus_bearing :
    caveToElenchus.bearing = 5 := by
  rfl

theorem cave_to_elenchus_distortion :
    caveToElenchus.distortion = 2 := by
  rfl

theorem cave_to_elenchus_positive_gain :
    0 < caveToElenchus.informationGain := by
  exact
    caveToElenchus.positive_gain_when_distortion_bounded
      (by decide)
      (by decide)

structure AllegoryCertificate where
  morphism : AllegoryMorphism
  nonIdentity : morphism.NonIdentity
  positiveBearing : 0 < morphism.bearing
  boundedDistortion : morphism.distortion < morphism.bearing

namespace AllegoryCertificate

theorem positive_information_gain
    (certificate : AllegoryCertificate) :
    0 < certificate.morphism.informationGain := by
  exact
    certificate.morphism.positive_gain_when_distortion_bounded
      certificate.positiveBearing
      certificate.boundedDistortion

end AllegoryCertificate

def caveLineCertificate : AllegoryCertificate where
  morphism := caveToLine
  nonIdentity := cave_to_line_nonidentity
  positiveBearing := by decide
  boundedDistortion := by decide

theorem cave_line_certificate_gain :
    0 < caveLineCertificate.morphism.informationGain := by
  exact caveLineCertificate.positive_information_gain

theorem philosophical_allegories_restored_master :
    caveToLine.NonIdentity ∧
      lineToElenchus.NonIdentity ∧
      shipToTwoTruths.NonIdentity ∧
      0 < caveToElenchus.informationGain ∧
      0 < caveLineCertificate.morphism.informationGain := by
  exact
    ⟨cave_to_line_nonidentity,
      line_to_elenchus_nonidentity,
      ship_to_two_truths_nonidentity,
      cave_to_elenchus_positive_gain,
      cave_line_certificate_gain⟩

end PhilosophicalAllegories
end Gnosis
