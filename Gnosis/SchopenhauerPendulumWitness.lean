/-
  SchopenhauerPendulumWitness.lean
  =================================

  Arthur Schopenhauer, *The World as Will and Representation* (**1818**; later
  editions expand the system — the **1818** anchor marks the first book appearance),
  pendulum sentence (one English gloss):

    “Life swings like a pendulum backward and forward between pain and boredom.”

  **No-win invariant (prose):** **Desire** is typed here as a **resource leak** in the
  folk sense of a restless state machine: **pain** names **unsatisfied want** (high
  stress / search); **boredom** names the **post-satisfaction** idle where the object
  fails to plug the inner **void** (the want was “filled,” but the hole was
  mis-sized). “Happiness” is not a **stationary** attractor — only the **thin** instants
  where the pendulum **crosses** the center line (tag those moments as your own `Prop`s).

  **Chaotic-neutral thread:** after `CioranTroubleWithBeingBornWitness` (**loyalty** to
  the void), Schopenhauer names the **kinetics of wanting** — the void does not
  disappear; the machine just **changes error codes** between search and idle-disgust.

  **Repo cousins:** `SchopenhauerHorizonFallacyWitness` (horizon fallacy / cognitive sandbox —
  **same** *Wille und Vorstellung* spine, **different** sting than the pendulum);
  `CioranTroubleWithBeingBornWitness`; `EpicurusTetrapharmakosWitness`
  (fear / scarcity stories); `LocalizedOverflowConsciousness` (conscious-local overflow
  as different formal carrier); `GoodhartsLaw` (metric under pressure — distant cousin:
  optimization breaks readouts); `MenckenConscienceShadowWitness` (social telemetry).

  Init only. Zero `sorry`, zero new `axiom`.
-/

import Init

namespace SchopenhauerPendulumWitness

/-- High-stress search mode: **unsatisfied** want (pain register). -/
abbrev UnsatisfiedWant (painStory : Prop) : Prop :=
  painStory

/-- Post-satisfaction idle: want was met, yet restlessness remains (boredom register). -/
abbrev SatisfiedButIdle (boredomStory : Prop) : Prop :=
  boredomStory

/-- Not a sustained “peace state” — only a **crossing** instant you name yourself. -/
abbrev CenterCrossing (moment : Prop) : Prop :=
  moment

inductive PendulumPhase where
  | pain
  | boredom
  deriving DecidableEq, Repr

def swing (p : PendulumPhase) : PendulumPhase :=
  match p with
  | .pain => .boredom
  | .boredom => .pain

theorem swing_involutive (p : PendulumPhase) : swing (swing p) = p := by
  cases p <;> rfl

/--
  Bundle: you admit **both** registers at once (pain story + boredom story) — no fake
  collapse into a permanent third `Prop` unless you supply it.
-/
structure PendulumWitness (pain boredom : Prop) where
  painRegister : UnsatisfiedWant pain
  boredomRegister : SatisfiedButIdle boredom

theorem both_poles (P B : Prop) (w : PendulumWitness P B) : P ∧ B :=
  And.intro w.painRegister w.boredomRegister

def buildWitness (P B : Prop) (hP : P) (hB : B) : PendulumWitness P B :=
  ⟨hP, hB⟩

end SchopenhauerPendulumWitness
