import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansSchoolmasterUnityWitness

/-!
# Galatians 3:19-29 -- Schoolmaster Boundary and Unity Heirship

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93764-93786`.

The law is not erased; it is bounded. Galatians assigns it a custodial function
until faith comes, then marks the post-schoolmaster state as a unity field where
former partitions no longer define heirship.

No `sorry`, no new `axiom`.
-/

structure LawCustody where
  lawAddedBecauseOfTransgressions : Bool := true
  lawUntilSeedShouldCome : Bool := true
  lawNotAgainstPromises : Bool := true
  lawCouldNotGiveLife : Bool := true
  scriptureConcludedAllUnderSin : Bool := true
  lawSchoolmasterToChrist : Bool := true
  afterFaithNoLongerSchoolmaster : Bool := true
deriving DecidableEq, Repr

def lawCustody : LawCustody := {}

def schoolmasterBoundary (c : LawCustody) : Prop :=
  c.lawAddedBecauseOfTransgressions = true ∧
  c.lawUntilSeedShouldCome = true ∧
  c.lawNotAgainstPromises = true ∧
  c.lawCouldNotGiveLife = true ∧
  c.scriptureConcludedAllUnderSin = true ∧
  c.lawSchoolmasterToChrist = true ∧
  c.afterFaithNoLongerSchoolmaster = true

structure UnityHeirship where
  childrenOfGodByFaith : Bool := true
  baptizedIntoChristPutOnChrist : Bool := true
  jewGreekBoundaryCollapsed : Bool := true
  bondFreeBoundaryCollapsed : Bool := true
  maleFemaleBoundaryCollapsed : Bool := true
  oneInChrist : Bool := true
  abrahamSeedAndHeirsByPromise : Bool := true
deriving DecidableEq, Repr

def unityHeirship : UnityHeirship := {}

def unityHeirshipByPromise (u : UnityHeirship) : Prop :=
  u.childrenOfGodByFaith = true ∧
  u.baptizedIntoChristPutOnChrist = true ∧
  u.jewGreekBoundaryCollapsed = true ∧
  u.bondFreeBoundaryCollapsed = true ∧
  u.maleFemaleBoundaryCollapsed = true ∧
  u.oneInChrist = true ∧
  u.abrahamSeedAndHeirsByPromise = true

theorem galatians_schoolmaster_boundary :
    schoolmasterBoundary lawCustody := by
  unfold schoolmasterBoundary lawCustody
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_unity_heirship_by_promise :
    unityHeirshipByPromise unityHeirship := by
  unfold unityHeirshipByPromise unityHeirship
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_schoolmaster_unity_witness :
    schoolmasterBoundary lawCustody ∧
    unityHeirshipByPromise unityHeirship := by
  exact ⟨galatians_schoolmaster_boundary,
    galatians_unity_heirship_by_promise⟩

end GalatiansSchoolmasterUnityWitness
end Gnosis.Witnesses.Bible.Galatians
