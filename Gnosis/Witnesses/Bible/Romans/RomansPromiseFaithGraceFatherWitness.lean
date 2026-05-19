import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansPromiseFaithGraceFatherWitness

/-!
# Romans 4:13-17 (KJV) -- Promise Through Faith and Grace

This unit gives one bounded promise topology:

  * the promise to Abraham and his seed is not through law but through
    righteousness of faith;
  * law-heirship voids faith and nullifies promise;
  * law works wrath, and no law means no transgression;
  * promise is of faith by grace and sure to all the seed;
  * Abraham is father of many nations before the God who quickens the dead.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 4:13-17 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_4_13_17_quote : String :=
  "4:13 For the promise, that he should be the heir of the world, was " ++
  "not to Abraham, or to his seed, through the law, but through the " ++
  "righteousness of faith. 4:14 For if they which are of the law be " ++
  "heirs, faith is made void, and the promise made of none effect: 4:15 " ++
  "Because the law worketh wrath: for where no law is, there is no " ++
  "transgression. 4:16 Therefore it is of faith, that it might be by " ++
  "grace; to the end the promise might be sure to all the seed; not to " ++
  "that only which is of the law, but to that also which is of the faith " ++
  "of Abraham; who is the father of us all, 4:17 (As it is written, I " ++
  "have made thee a father of many nations,) before him whom he believed, " ++
  "even God, who quickeneth the dead, and calleth those things which be " ++
  "not as though they were."

/-- The promise/law contrast in Romans 4:13-15. -/
structure PromiseLawContrast where
  heirOfWorldPromise : Bool
  notThroughLaw : Bool
  throughRighteousnessOfFaith : Bool
  lawHeirsMakeFaithVoid : Bool
  lawWorksWrath : Bool
  noLawNoTransgression : Bool
deriving DecidableEq, Repr

/-- The promise is through righteousness of faith, not law. -/
def promiseLawContrast : PromiseLawContrast where
  heirOfWorldPromise := true
  notThroughLaw := true
  throughRighteousnessOfFaith := true
  lawHeirsMakeFaithVoid := true
  lawWorksWrath := true
  noLawNoTransgression := true

/-- The faith/grace certainty pattern in Romans 4:16-17. -/
structure FaithGraceFatherPattern where
  ofFaithByGrace : Bool
  promiseSureToAllSeed : Bool
  includesLawAndFaithSeed : Bool
  abrahamFatherOfUsAll : Bool
  fatherOfManyNations : Bool
  godQuickensDead : Bool
  callsThingsNotAsThoughTheyWere : Bool
deriving DecidableEq, Repr

/-- Faith by grace makes the promise sure to Abraham's seed. -/
def faithGraceFatherPattern : FaithGraceFatherPattern where
  ofFaithByGrace := true
  promiseSureToAllSeed := true
  includesLawAndFaithSeed := true
  abrahamFatherOfUsAll := true
  fatherOfManyNations := true
  godQuickensDead := true
  callsThingsNotAsThoughTheyWere := true

/-- The bounded Romans 4:13-17 witness. -/
theorem romans_promise_faith_grace_father_witness :
    promiseLawContrast.heirOfWorldPromise = true
    ∧ promiseLawContrast.notThroughLaw = true
    ∧ promiseLawContrast.throughRighteousnessOfFaith = true
    ∧ promiseLawContrast.lawHeirsMakeFaithVoid = true
    ∧ promiseLawContrast.lawWorksWrath = true
    ∧ promiseLawContrast.noLawNoTransgression = true
    ∧ faithGraceFatherPattern.ofFaithByGrace = true
    ∧ faithGraceFatherPattern.promiseSureToAllSeed = true
    ∧ faithGraceFatherPattern.includesLawAndFaithSeed = true
    ∧ faithGraceFatherPattern.abrahamFatherOfUsAll = true
    ∧ faithGraceFatherPattern.fatherOfManyNations = true
    ∧ faithGraceFatherPattern.godQuickensDead = true
    ∧ faithGraceFatherPattern.callsThingsNotAsThoughTheyWere = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end RomansPromiseFaithGraceFatherWitness
end Gnosis.Witnesses.Bible.Romans
