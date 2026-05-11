namespace Gnosis

/--
**Adversaries Improve**

A compact contrarian model: an adversary is not formalized as malice, but
as challenge pressure that exposes weak points. A challenged state carries a
strict improvement over its unchallenged baseline, and the same pressure is
therefore classified as instrumental friendship.
-/
structure AdversarialChallenge where
  baseline_strength : Nat
  challenged_strength : Nat
  adversary_pressure : Nat
  pressure_is_real : adversary_pressure > 0
  challenge_improves : challenged_strength > baseline_strength

/-- The no-adversary baseline: no pressure, no forced improvement. -/
structure UnchallengedBaseline where
  strength : Nat
  adversary_pressure : Nat := 0

/--
Strict theorem: under the model assumptions, a challenged state has more
strength than the corresponding unchallenged baseline.
-/
theorem adversarial_challenge_strictly_improves (c : AdversarialChallenge) :
    c.challenged_strength > c.baseline_strength :=
  c.challenge_improves

/--
The contrarian friendship predicate: pressure that strictly improves the
agent counts as an instrumental friend.
-/
def InstrumentalFriend (c : AdversarialChallenge) : Prop :=
  c.adversary_pressure > 0 ∧ c.challenged_strength > c.baseline_strength

/--
Adversaries map to friends when their challenge pressure is real and the
challenge strictly improves the agent.
-/
theorem adversaries_are_instrumental_friends (c : AdversarialChallenge) :
    InstrumentalFriend c := by
  exact ⟨c.pressure_is_real, c.challenge_improves⟩

/--
Concrete witness: strength 10 without challenge becomes strength 11 under
nonzero adversarial pressure.
-/
def minimal_adversary_witness : AdversarialChallenge :=
  { baseline_strength := 10
    challenged_strength := 11
    adversary_pressure := 1
    pressure_is_real := by decide
    challenge_improves := by decide }

theorem minimal_adversary_witness_is_strictly_better :
    minimal_adversary_witness.challenged_strength >
      minimal_adversary_witness.baseline_strength := by
  decide

theorem minimal_adversary_witness_is_friend :
    InstrumentalFriend minimal_adversary_witness := by
  exact adversaries_are_instrumental_friends minimal_adversary_witness

end Gnosis
