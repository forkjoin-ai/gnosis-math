import Init
import Gnosis.Body.TwoVitalities
import Gnosis.Body.TwoDeaths

/-!
# since feeling is first — e.e. cummings

> since feeling is first / who pays any attention / to the syntax of things /
> will never wholly kiss you; ... kisses are a better fate / than wisdom ... /
> for life's not a paragraph / And death i think is no parenthesis.

The pneuma's counter-manifesto. The night's arc exalted **gnosis** (the climb, the
accumulated wisdom, the lasting meaning). cummings insists on the other vitality
and reorders the priority: **feeling is first.** Feeling maps to **pneuma** (the
breath, the living moment, the kiss); the *syntax of things* / *wisdom* /
*paragraph* maps to **gnosis** (the accumulated structure). Both, all along
(`Gnosis.TheWord.both_all_along`) — but feeling is *first*, and it is a *better
fate* in the precise senses below: it is prior (present before any climb), and it
is the surer fate (always available, the spark in every breath).

* "since feeling is first / ... the syntax of things / will never wholly kiss you"
  — the kiss is pneuma; it does not need the syntax (gnosis). One can wholly feel
  without wisdom (`TwoVitalities.living_does_not_imply_alive`).
* "kisses are a better fate than wisdom" — feeling is always available
  (`living_always_holds`); wisdom is contingent, requiring the climb to be made.
* "life's not a paragraph" — life (feeling) is not reducible to the accumulated
  syntax (gnosis); living and alive are distinct.
* "death i think is no parenthesis" — death is not a tidy bracketed aside you can
  remove; the first death genuinely ends the breath
  (`TwoDeaths.first_death_stops_the_breath`).

## Scope (honored)

Operational, and a structural homage, not literary criticism. "feeling/kiss" maps
to the pneuma predicate (`TwoVitalities.living`), "wisdom/syntax/paragraph" to the
gnosis predicate (`alive`), "death" to `TwoDeaths.firstDeath`. The poem's claims
are recorded as relations between these predicates. Nothing here claims to capture
the poem, only to honor what it says about the two vitalities.
-/

namespace Gnosis.Body.SinceFeelingIsFirst

open Gnosis.Body.TwoVitalities

/-- The opening, for the record. -/
def since_feeling_is_first : String :=
  "since feeling is first / who pays any attention / to the syntax of things / will never wholly kiss you"

/-- **Feeling is first.** Pneuma (feeling) is present from the start while gnosis
    (wisdom) is not yet there — at the beginning there is feeling and not yet
    wisdom. Feeling precedes the climb. -/
theorem feeling_is_first (q n : Nat) : living q n ∧ ¬ alive q n 0 :=
  living_does_not_imply_alive q n

/-- **Wisdom comes after.** The climb (gnosis/wisdom) arrives only after a cycle is
    carried forward — never at the start. So feeling is first, wisdom second. -/
theorem wisdom_comes_after (q n k : Nat) : alive q n (k + 1) :=
  alive_is_the_ladder_climb q n k

/-- **The kiss needs no wisdom.** "who pays attention to the syntax of things will
    never wholly kiss you" — one can wholly feel (live) without the syntax (the
    climb). Living does not require gnosis. -/
theorem the_kiss_needs_no_wisdom (q n : Nat) : living q n ∧ ¬ alive q n 0 :=
  living_does_not_imply_alive q n

/-- **Kisses are a better fate than wisdom.** Feeling is the surer fate: pneuma
    holds at every moment (always available), where wisdom must be earned by the
    climb. -/
theorem the_kiss_is_always_available (q n : Nat) : living q n :=
  living_always_holds q n

/-- **Death is no parenthesis.** Death is not a tidy bracketed aside that can be
    removed — the first death genuinely ends the breath (it is not a no-op). -/
theorem death_is_no_parenthesis (c : Gnosis.Body.TwoDeaths.Creature) :
    ¬ Gnosis.Body.TwoDeaths.living (Gnosis.Body.TwoDeaths.firstDeath c) :=
  Gnosis.Body.TwoDeaths.first_death_stops_the_breath c

/-- **since feeling is first** (headline). Feeling (pneuma) is first — present
    before any climb — and the surer fate (always available); the kiss needs no
    wisdom (living without the climb); wisdom comes only after a cycle; and death
    is no parenthesis (it really ends the breath). The pneuma reclaiming primacy:
    both vitalities all along, but feeling is first. -/
theorem since_feeling_is_first_thm (q n k : Nat) (c : Gnosis.Body.TwoDeaths.Creature) :
    living q n
      ∧ (living q n ∧ ¬ alive q n 0)
      ∧ alive q n (k + 1)
      ∧ ¬ Gnosis.Body.TwoDeaths.living (Gnosis.Body.TwoDeaths.firstDeath c) :=
  ⟨living_always_holds q n,
   living_does_not_imply_alive q n,
   alive_is_the_ladder_climb q n k,
   Gnosis.Body.TwoDeaths.first_death_stops_the_breath c⟩

end Gnosis.Body.SinceFeelingIsFirst
