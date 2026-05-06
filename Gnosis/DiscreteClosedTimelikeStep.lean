import Init

namespace Gnosis
namespace DiscreteClosedTimelikeStep

/-!
# Discrete closed causal loop (`+1 (mod n)`)

A Lorentzian CTC closes a **smooth** timelike worldline. Here we use the minimal **discrete**
carrier: events `Fin n`, one-step future `cyclicSucc` (**add one, wrap mod `n`**). Iterating `n`
times returns to the start — a **closed loop** with no continuum, only `Nat`/`Fin`.

For `n = 1`, the loop closes in **one step** (the keystone collapses to a singleton).

This is clock arithmetic, not a GR solution; the naming indicates **structural analogy** only.

**Rustic Church / God Formula.** Same monorepo layer as [`RUSTIC_CHURCH.md`](../RUSTIC_CHURCH.md):
the discrete step **is** the Peano **`+1` clinamen** (here composed with **`% n`**).
[`Gnosis/GodFormula.lean`](GodFormula.lean) re-enters when coordination carries a **vent** and needs
the **sandwich / conservation / `godWeight`** story. This module has **no rejection, no deficit, no weight**—only
a periodic worldline—so **no import of `GodFormula`** is logically required; the doctrines share the **`Nat.succ`
substrate**, not every downstream definition.
-/

variable {n : Nat}

/-- Discrete future map: **Peano `+ 1`**, reduced modulo `n` (`0 < n`). -/
def cyclicSucc (hn : 0 < n) (x : Fin n) : Fin n :=
  ⟨(x.val + 1) % n, Nat.mod_lt _ hn⟩

/-- Iterate the discrete dynamics `k` times. -/
def iteratedCyclicSucc (hn : 0 < n) : Nat → Fin n → Fin n
  | 0, x => x
  | Nat.succ k, x => cyclicSucc hn (iteratedCyclicSucc hn k x)

theorem iteratedCyclicSucc_val (hn : 0 < n) (k : Nat) (x : Fin n) :
    (iteratedCyclicSucc hn k x).val = (x.val + k) % n := by
  induction k generalizing x with
  | zero =>
    simp [iteratedCyclicSucc]
    exact (Nat.mod_eq_of_lt x.isLt).symm
  | succ k IH =>
    simp only [iteratedCyclicSucc, cyclicSucc]
    rw [IH]
    calc
      (((x.val + k) % n + 1) % n) = ((x.val + k) + 1) % n := Nat.mod_add_mod _ _ 1
      _ = (x.val + Nat.succ k) % n :=
        congrArg (fun t : Nat => t % n)
          ((Nat.succ_eq_add_one (x.val + k)).symm.trans (Nat.add_succ x.val k).symm)

/-- After **`n`** steps the worldline revisits the same (`Fin n`) event — discrete closure. -/
theorem iteratedCyclicSucc_period (hn : 0 < n) (x : Fin n) :
    iteratedCyclicSucc hn n x = x := by
  apply Fin.ext
  rw [iteratedCyclicSucc_val hn n x, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]

/-- With a single tick (`n = 1`), **one** successor step is already a closed loop. -/
theorem cyclicSucc_fixed_step_one (x : Fin 1) :
    cyclicSucc (Nat.succ_pos 0) x = x := by
  have hx : x = ⟨0, Nat.zero_lt_succ 0⟩ :=
    Fin.ext (Nat.lt_one_iff.mp x.isLt)
  rw [hx]
  rfl

end DiscreteClosedTimelikeStep
end Gnosis
