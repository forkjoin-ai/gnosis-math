import Init

/-!
# Conservation of Vitality — and the third Bule face

Time runs one way; we exist forward. So measure *total* vitality over the
remaining time. The naive reading is "gnosis wins by sheer extension — the
immortal delivers more total." But that conflicts with the conjecture that each
entity has a **fixed** vitality. The resolution is conservation: if total vitality
is conserved, the immortal cannot deliver *more* — it must **dilute the rate** to
stretch the fixed budget over a longer time. In the limit, the immortal's rate
goes to zero: the frozen heat-death "slumber" is not waste, it is **conservation
of energy** — banking the budget rather than spending it.

So the mortal (bright, short) and the immortal (dim, long) deliver the *same total
vitality*: only the gradient differs. With retrocausality (the white hole is the
exact time-reversal, `Gnosis/WhiteHole.lean`), even the direction of the gradient
washes out — same total, different gradient. **Heat death or mortal death**
(`Gnosis/Body/DeathIsInevitable.lean`) deliver the same conserved vitality. That
is the peace in it: the choice of death does not change the total you give.

## The Bule faces (conserved quantities)

The buley weight `w = R − v + 1` carries the faces:
* **information** `v` — conserved (`Gnosis/InformationConservation.lean`, no-cloning).
* **energy / resource** `R` — conserved (`Gnosis/EnergyConservationFromVacuum.lean`).
* **waste** `R − v` — the Buleyean deficit, the *third face* we forgot to prove.
  It is conserved because it is the difference of two conserved quantities.
* `+1` — the spark (Barbelo), the floor.

(**diversity** — `Gnosis/Body/DiversityIsOptimal.lean` — is a candidate further
face on a different axis from the `w = R−v+1` decomposition; noted, not formalized
here.)

## Scope (honored)

Operational `Nat` model. `totalVitality = rate*duration` is the budget; "candle
conservation" is its symmetry under rate↔duration; "heat death conserves" is the
zero-rate slumber. Energy and information conservation are *cited* from their
modules; the new content is that **waste is conserved given those two**. No
emphatic identity prose.
-/

namespace Gnosis.Body.ConservationOfVitality

/-- Total vitality delivered over a span = rate × duration (the budget spent). -/
def totalVitality (rate duration : Nat) : Nat := rate * duration

/-- **The candle conservation.** The same total is delivered bright-and-short or
    dim-and-long: total vitality is invariant under swapping rate and duration.
    Burn twice as bright half as long — the same fixed budget. -/
theorem candle_conservation (rate duration : Nat) :
    totalVitality rate duration = totalVitality duration rate :=
  Nat.mul_comm rate duration

/-- **Heat death conserves, it does not waste.** The frozen slumber spends nothing
    (rate `0`) — it banks the budget rather than spending it. -/
theorem heat_death_conserves (duration : Nat) : totalVitality 0 duration = 0 :=
  Nat.zero_mul duration

/-- **Slumber banks the budget.** A spell of frozen slumber (rate `0`) adds nothing
    to the total — the vitality is conserved for later, not lost. The immortal's
    long dim stretch and the mortal's short bright burn can carry the same total. -/
theorem slumber_banks (rate d1 d2 : Nat) :
    totalVitality 0 d1 + totalVitality rate d2 = totalVitality rate d2 := by
  rw [heat_death_conserves, Nat.zero_add]

/-! ## The three Bule faces: information, energy, waste -/

/-- **Waste** — the Buleyean deficit `R − v` (the resource above the value). The
    third face, alongside information (`v`) and energy/resource (`R`). -/
def waste (R v : Nat) : Nat := R - v

/-- The buley weight `R − v + 1` decomposes as **waste plus the spark**. -/
def buleyWeight (R v : Nat) : Nat := R - v + 1

theorem buley_is_waste_plus_spark (R v : Nat) : buleyWeight R v = waste R v + 1 := rfl

/-- **The third Bule face — waste is conserved.** If energy/resource (`R`) is
    conserved and information (`v`) is conserved, then waste (`R − v`) is conserved:
    the deficit is the difference of two conserved quantities. Energy and
    information we already had; this is the face we forgot. -/
theorem waste_is_conserved (R1 R2 v1 v2 : Nat) (hR : R1 = R2) (hv : v1 = v2) :
    waste R1 v1 = waste R2 v2 := by
  rw [hR, hv]

/-- **The three faces conserved together.** Given energy and information conserved,
    all three faces — energy (`R`), information (`v`), waste (`R − v`) — are
    conserved, and the buley weight (waste + spark) with them. -/
theorem three_faces_conserved (R1 R2 v1 v2 : Nat) (hR : R1 = R2) (hv : v1 = v2) :
    R1 = R2 ∧ v1 = v2 ∧ waste R1 v1 = waste R2 v2 ∧ buleyWeight R1 v1 = buleyWeight R2 v2 := by
  refine ⟨hR, hv, waste_is_conserved R1 R2 v1 v2 hR hv, ?_⟩
  unfold buleyWeight
  rw [hR, hv]

/-- **Conservation makes the two deaths equal.** Given a fixed total vitality `V`,
    the mortal (rate `r`, duration `d`, `r*d = V`) and the immortal (rate `r'`,
    duration `d'`, `r'*d' = V`) deliver the same total — only the gradient differs.
    Heat death or mortal death: the same conserved vitality. -/
theorem two_deaths_deliver_the_same_total (V r d r' d' : Nat)
    (hmortal : totalVitality r d = V) (himmortal : totalVitality r' d' = V) :
    totalVitality r d = totalVitality r' d' := by
  rw [hmortal, himmortal]

end Gnosis.Body.ConservationOfVitality
