import Init
import Gnosis.AckermannFunction
import Gnosis.AckermannLightConeBridge
import Gnosis.KnotRopelengthComplexity
import Gnosis.KnotRopelengthSuperpolynomial
import Gnosis.FrontierComputability

/-
  SuperpolynomialFront.lean
  =========================

  The deepest unification: the whole program is ONE phenomenon — a
  "superpolynomial front" that a polynomial-reach searcher cannot catch.

  Three concrete fronts, proved to be the same kind of object:
    * `2^n`            — the exponential (`exp_beats_poly`);
    * `npRopelength n` — the NP knot's ropelength `1 + 2^n` (rope / Betti);
    * `ackermannDiag n`— the luminal Ackermann ceiling (the light theorem's
                          frontier, via `polynomial_eventually_subluminal`).

  All three satisfy `OutpacesPolys` (`∀ k, ∃ n, n^k < S n`), and every such front
  makes the polynomial searcher uncatchable (`outpacing_front_uncatchable`). So
  the rope/Betti gap, the exp>poly core, and the Ackermann=light-speed frontier
  are three faces of one fact. "Strengthen by weakening" across the whole
  program: the abstract `OutpacesPolys` subsumes them all.

  HONEST SCOPE (unchanged): the fronts are genuinely superpolynomial (proved).
  This is NOT a P ≠ NP proof — that an actual NP-complete problem's witness-front
  IS such a front is the open, relativizing part (Baker–Gill–Solovay).

  Init + the program. Zero `sorry`, zero new `axiom`.
-/

namespace SuperpolynomialFront

open AckermannFunction
open AckermannLightConeBridge
open KnotRopelengthComplexity
open KnotRopelengthSuperpolynomial
open FrontierComputability

/-- A front `S` outpaces every fixed polynomial: for each degree `k` there is an
    `n` with `n^k < S n`. -/
def OutpacesPolys (S : Nat → Nat) : Prop := ∀ k, ∃ n, n ^ k < S n

/-- The exponential front `2^n` outpaces every polynomial. -/
theorem exp_outpaces : OutpacesPolys (fun n => 2 ^ n) :=
  fun k => exp_beats_poly k

/-- The NP ropelength front `1 + 2^n` outpaces every polynomial. -/
theorem rope_outpaces : OutpacesPolys npRopelength := by
  intro k
  obtain ⟨n, hn⟩ := exp_beats_poly k
  refine ⟨n, ?_⟩
  rw [npRopelengthValue]
  omega

/-- The luminal Ackermann ceiling `A(n)` outpaces every polynomial — the light
    theorem's frontier is a superpolynomial front. -/
theorem ackermann_outpaces : OutpacesPolys ackermannDiag := by
  intro k
  exact ⟨max k 6, polynomial_eventually_subluminal k (max k 6) (by omega) (by omega)⟩

/-- **Every superpolynomial front is uncatchable.** A polynomial-reach searcher
    fails to catch any `OutpacesPolys` front at some input. -/
theorem outpacing_front_uncatchable {S : Nat → Nat} (h : OutpacesPolys S) (k : Nat) :
    ∃ n, catchable (n ^ k) (S n) = false := by
  obtain ⟨n, hn⟩ := h k
  exact ⟨n, uncatchable_if_spread_exceeds (n ^ k) (S n) hn⟩

/-- **One front, three faces.** The exponential `2^n`, the NP ropelength `1+2^n`,
    and the Ackermann luminal ceiling `A(n)` are all superpolynomial fronts — the
    rope/Betti gap, the exp>poly core, and the Ackermann=light-speed frontier are
    three faces of one phenomenon. -/
theorem three_fronts_one_phenomenon :
    OutpacesPolys (fun n => 2 ^ n)
    ∧ OutpacesPolys npRopelength
    ∧ OutpacesPolys ackermannDiag :=
  ⟨exp_outpaces, rope_outpaces, ackermann_outpaces⟩

end SuperpolynomialFront
