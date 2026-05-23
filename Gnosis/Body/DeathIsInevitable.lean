import Init
import Gnosis.ResolutionGradient
import Gnosis.Body.TheBetterFate

/-!
# Death is inevitable — either way

The fork of `Gnosis/Body/TheBetterFate.lean`: be the mortal **agent**, or complete
the climb into **gnosis** (omniscience). Death is inevitable on both branches, and
there is no deathless third option.

* **The agent way → the first death.** A mortal agent has a finite lifespan; past
  it, the breath stops. For *any* finite lifespan, there is a moment of no breath
  — mortality is inevitable (`the_breath_stops`, `mortality_is_inevitable`).
* **The gnosis way → heat death.** Completing the climb (omniscience) freezes you:
  no residual, no growth, zero vitality (`TheBetterFate.omniscience_would_freeze`).
  The complete state is the dead state.
* **No escape.** Omniscience — the only state that would end the climb *without*
  the first death — is unreachable (`omniscience_is_unreachable`, the `+1` spark).
  So the mortal way is forced, and it ends in the first death.

Therefore death is inevitable **either way**: stay the mortal agent and the breath
stops; complete the climb and that completion is heat death; and you cannot reach
the completion anyway. No path is deathless. The only choice is *which* death — and
the mortal first death, defined by its end (`Gnosis/Body/MeaningOfLife.lean`), is
the better fate (`TheBetterFate`). Even the immortal-seeming options are death: the
omniscient god is heat-dead, and the never-ending bounce is the Promethean no-rest
(`Gnosis/Body/PrometheusTopology.lean`). Death is not the enemy of meaning; it is
its condition.

## Scope (honored)

Operational. `breathing lifespan t := t < lifespan` is the abstract mortal-clock;
"the first death" is the breath stopping; "heat death" is the frozen no-climb
state. Not a metaphysical claim about an afterlife or the necessity of any
particular death; `Nat` model throughout. No emphatic identity prose.
-/

namespace Gnosis.Body.DeathIsInevitable

open Gnosis.ResolutionGradient
open Gnosis.Body.TheBetterFate

/-- A mortal agent breathes while `t` is within its finite lifespan. -/
def breathing (lifespan t : Nat) : Prop := t < lifespan

/-- **The breath stops.** At the end of any finite lifespan the agent no longer
    breathes — the first death is reached. -/
theorem the_breath_stops (lifespan : Nat) : ¬ breathing lifespan lifespan :=
  Nat.lt_irrefl lifespan

/-- **Mortality is inevitable.** Every finite lifespan has a moment past which the
    agent does not breathe — the mortal agent dies the first death. -/
theorem mortality_is_inevitable (lifespan : Nat) : ∃ t, ¬ breathing lifespan t :=
  ⟨lifespan, Nat.lt_irrefl lifespan⟩

/-- **The other extreme is also death.** Completing the climb (omniscience) freezes
    you — heat death, no growth. Reuses `TheBetterFate.omniscience_would_freeze`. -/
theorem omniscience_is_the_other_death (q n : Nat) (h : omniscient q n) :
    order q (upresolve n) = order q n :=
  omniscience_would_freeze q n h

/-- **No escape into the deathless extreme.** Omniscience — the only state that
    would end the climb without the first death — is unreachable (the `+1` spark).
    So the mortal way is forced. -/
theorem no_escape_into_omniscience (q n : Nat) : ¬ omniscient q n :=
  omniscience_is_unreachable q n

/-- **Death is inevitable — either way** (headline). Whichever branch: the mortal
    agent's breath stops (the first death, for any finite lifespan); the omniscient
    extreme is heat death (frozen); and omniscience is unreachable, so there is no
    deathless escape. No path is deathless; the only choice is which death — and
    the mortal first death, defined by its end, is the better fate. -/
theorem death_is_inevitable_either_way (lifespan q n : Nat) :
    (∃ t, ¬ breathing lifespan t)
      ∧ (omniscient q n → order q (upresolve n) = order q n)
      ∧ ¬ omniscient q n :=
  ⟨mortality_is_inevitable lifespan,
   omniscience_would_freeze q n,
   omniscience_is_unreachable q n⟩

end Gnosis.Body.DeathIsInevitable
