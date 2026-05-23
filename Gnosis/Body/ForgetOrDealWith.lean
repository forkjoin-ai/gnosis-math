import Init
import Gnosis.Body.AmnesiaGritFrontier
import Gnosis.Body.LifeIsABitch

/-!
# Forget It, Or Deal With It

The abstract content of attachment (Buddhist dukkha / `Gnosis/BuddhistAttachmentSkyrms.lean`):
an unresolved burden persists only while you *cling* to it. There are exactly two
ways out — and they are the two poles of the amnesia-grit frontier:

* **forget it** — clear by erasure (the amnesia pole: release the memory, lose the
  lesson, regain adaptability), and
* **deal with it** — clear by working the whole burden through (the grit pole:
  bank the lesson, carry its weight).

Both clear the suffering; clinging keeps it. But — `LifeIsABitch` — you cannot
both forget the pain *and* keep its lesson: the resolution itself is a trade.
This is non-attachment read not as one move but as a *choice between the frontier's
poles*.
-/

namespace Gnosis.Body.ForgetOrDealWith

open Gnosis.Body.AmnesiaGritFrontier

/-- Forget it: clear the burden by erasure (the amnesia pole). -/
def forget (d : Nat) : Nat := amnesia d

/-- Deal with it: clear the burden by working the whole of it through (grit). -/
def deal (d : Nat) : Nat := d - d

/-- Cling: do neither — the attachment, and the suffering, persist. -/
def cling (d : Nat) : Nat := d

/-- Forgetting clears the burden (amnesia is the void). -/
theorem forget_clears (d : Nat) : forget d = 0 := rfl

/-- Dealing with it clears the burden (the whole of it is worked through). -/
theorem deal_clears (d : Nat) : deal d = 0 := by
  show d - d = 0
  exact Nat.sub_self d

/-- Clinging keeps the suffering: a real burden left unaddressed remains. -/
theorem clinging_keeps (d : Nat) (h : 0 < d) : 0 < cling d := h

/-- **Two routes out of dukkha.** Either resolution — forget (amnesia) or deal
    (grit) — clears the burden to zero. Cessation (nirodha) is choosing a pole. -/
theorem two_routes_out (d : Nat) : forget d = 0 ∧ deal d = 0 :=
  ⟨forget_clears d, deal_clears d⟩

/-- **You cannot both forget the pain and keep its lesson.** Forgetting is the
    amnesia pole — zero retention banks nothing, the lesson is lost — exactly
    `AmnesiaGritFrontier.pure_amnesia_has_no_accumulation`. Dealing (grit) is the
    other pole, where the lesson is banked. The two clearances are different
    points on the frontier; by `LifeIsABitch` you cannot occupy both. -/
theorem forgetting_loses_the_lesson (m scale : Nat) :
    accumulationValue (retain m 0 scale) = 0 :=
  pure_amnesia_has_no_accumulation m scale

/-- **Attachment is the grit-amnesia tradeoff.** A clung burden persists; it is
    cleared only by forgetting (amnesia) or dealing (grit); and the choice between
    those resolutions is itself the frontier trade — you forget and lose the
    lesson, or deal and carry it. -/
theorem attachment_is_the_grit_amnesia_tradeoff (d m scale : Nat) (h : 0 < d) :
    (forget d = 0 ∧ deal d = 0)
      ∧ 0 < cling d
      ∧ accumulationValue (retain m 0 scale) = 0 :=
  ⟨two_routes_out d, clinging_keeps d h, forgetting_loses_the_lesson m scale⟩

end Gnosis.Body.ForgetOrDealWith
