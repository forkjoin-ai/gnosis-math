import Init
import Gnosis.KhovanovCategorifiesJones

/-!
# Periodic element ↔ link diagram atlas (discrete B₂ closure + Jones readout)

This module **targets three formal layers**:

1. **B₂ braid closure (discrete) + Markov-II shadow**  
   Words in one Artin generator `σ` on two strands are modeled by an exponent
   `n : Nat`. A **palette index** `n % 4` fixes a canonical `Diagram` from the
   Khovanov catalog. **Markov stabilization** is modeled by `n ↦ n + 4`: the
   palette — and hence the chosen diagram — is unchanged. On `B₂` the braid
   group is `ℤ`, so **Markov I conjugation is trivially absorbed**: there is no
   nontrivial conjugacy class movement on a one-generator classification scheme.

2. **Jones functor invariance**  
   `KhovanovCategorifiesJones.jonesPoly` is a function `Diagram → LaurentPoly`.
   It respects equality of diagrams (`congrArg`) and induces an explicit equivalence
   relation `jonesEquiv` on diagrams (equality of polynomials).

3. **Impossibility / coarse readout**  
   The IUPAC-row atlas below is **4-periodic** on `Z mod 4`. Hence the composite
   `Fin 118 → LaurentPoly` landing in `{unknot, trefoil, Hopf±}` cannot be
   injective: indices `0` and `4` already collide. This is the Jones-side analogue
   of the pigeonhole phenomena in `Gnosis.PeriodicBraidMatterJugular`.

**Extension (same file):** a **parametric** `mod p` palette index with period-`p`
Markov stability, collision witnesses for every `p < 118`, **injective**
row-tagged bundles `(diagram × row)` / `(Jones poly × row)`, and an **injective
`Fin 118 → Diagram` codec** that smuggles the row index as an extra formal
resolution-table entry (Kauffman bookkeeping — not an isotopy claim).

**Not claimed:** ambient-isotopy correctness of `σⁿ ↦ diagram`; chemical law; any
identification of physical atoms with knot types beyond this bookkeeping atlas.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PeriodicElementLinkAtlas

open KhovanovCategorifiesJones

/-! ## Canonical 4-diagram palette (Khovanov catalog) -/

/-- Map the finite residue class to one of four stored diagram witnesses. -/
def canonicalPalette (k : Fin 4) : Diagram :=
  match k with
  | ⟨0, _⟩ => unknot
  | ⟨1, _⟩ => trefoilPlus
  | ⟨2, _⟩ => hopfPlus
  | ⟨3, _⟩ => hopfMinus

/-! ## B₂: single-generator exponent → closure palette index -/

/-- **Discrete B₂ closure statistic:** `σⁿ` projects to `Fin 4` via `n % 4`. -/
def b2ClosurePaletteIndex (n : Nat) : Fin 4 :=
  ⟨n % 4, Nat.mod_lt _ (by decide : (0 : Nat) < 4)⟩

/-- Closed diagram picked out by the B₂ exponent model. -/
def b2ClosureDiagram (n : Nat) : Diagram :=
  canonicalPalette (b2ClosurePaletteIndex n)

/-! ## Markov moves (toy slice, rigorous for *this* encoding) -/

/-- **Markov II shadow:** adding four crossings worth of stabilization does not
change the 4-way palette, hence does not change `b2ClosureDiagram`. -/
theorem markov_two_stabilization (n : Nat) :
    b2ClosurePaletteIndex (n + 4) = b2ClosurePaletteIndex n := by
  apply Fin.ext
  show (n + 4) % 4 = n % 4
  rw [Nat.add_mod_right]

theorem markov_two_stabilization_diagram (n : Nat) :
    b2ClosureDiagram (n + 4) = b2ClosureDiagram n := by
  unfold b2ClosureDiagram
  rw [markov_two_stabilization n]

/-! ## IUPAC `Fin 118` atlas (ties rows to `σᶻ` exponent shadow = atomic number) -/

/-- Element row `i` uses the **same** B₂ palette as exponent `i.val` (0-based Z). -/
def elementDiagram (row : Fin 118) : Diagram :=
  b2ClosureDiagram row.val

theorem element_diagram_eq_of_val_mod (i j : Fin 118) (h : i.val % 4 = j.val % 4) :
    elementDiagram i = elementDiagram j := by
  unfold elementDiagram b2ClosureDiagram
  have hp : b2ClosurePaletteIndex i.val = b2ClosurePaletteIndex j.val := Fin.ext h
  rw [hp]

theorem element_diagram_idx_zero_four :
    elementDiagram ⟨0, by decide⟩ = elementDiagram ⟨4, by decide⟩ := by
  apply element_diagram_eq_of_val_mod
  decide

/-! ## Jones polynomial layer: functoriality + equivalence relation -/

/-- Equality of `jonesPoly` outputs — the only notion of “same Jones invariant”
available without importing a full Laurent-polynomial normalization quotient. -/
def jonesEquiv (d₁ d₂ : Diagram) : Prop :=
  jonesPoly d₁ = jonesPoly d₂

theorem jonesEquiv_refl (d : Diagram) : jonesEquiv d d := rfl

theorem jonesEquiv_symm {d₁ d₂ : Diagram} (h : jonesEquiv d₁ d₂) : jonesEquiv d₂ d₁ :=
  Eq.symm h

theorem jonesEquiv_trans {d₁ d₂ d₃ : Diagram}
    (h₁ : jonesEquiv d₁ d₂) (h₂ : jonesEquiv d₂ d₃) : jonesEquiv d₁ d₃ :=
  Eq.trans h₁ h₂

theorem jonesPoly_congr {d₁ d₂ : Diagram} (h : d₁ = d₂) : jonesPoly d₁ = jonesPoly d₂ :=
  congrArg jonesPoly h

theorem jonesEquiv_congr {d₁ d₂ : Diagram} (h : d₁ = d₂) : jonesEquiv d₁ d₂ :=
  congrArg jonesPoly h

/-! ## Non-injectivity: 118 rows into a 4-palette Jones readout -/

theorem atlas_rows_zero_and_four_distinct :
    (⟨0, by decide⟩ : Fin 118) ≠ ⟨4, by decide⟩ := by
  intro h
  have h0 : (0 : Nat) = 4 := congrArg Fin.val h
  exact absurd h0 (by decide)

theorem element_jones_readout_not_injective :
    ¬Function.Injective (fun i : Fin 118 => jonesPoly (elementDiagram i)) := by
  intro hInj
  have hEqPoly : jonesPoly (elementDiagram ⟨0, by decide⟩) =
      jonesPoly (elementDiagram ⟨4, by decide⟩) :=
    jonesPoly_congr element_diagram_idx_zero_four
  have hRow := hInj hEqPoly
  exact atlas_rows_zero_and_four_distinct hRow

/-- Scalar readout at `q = 1` also cannot distinguish `0` and `4` here. -/
theorem element_jones_eval_at_one_not_injective :
    ¬Function.Injective (fun i : Fin 118 => (jonesPoly (elementDiagram i)).evalAtOne) := by
  intro hInj
  have hEq :
      (jonesPoly (elementDiagram ⟨0, by decide⟩)).evalAtOne =
        (jonesPoly (elementDiagram ⟨4, by decide⟩)).evalAtOne :=
    congrArg LaurentPoly.evalAtOne (jonesPoly_congr element_diagram_idx_zero_four)
  exact atlas_rows_zero_and_four_distinct (hInj hEq)

/-! ## Bridge to coarse `Fin k` readouts (`k < 118`) -/

/-- If two rows agree modulo `k`, the quotient readout agrees — specialization of
the same collision mechanism as `PeriodicBraidMatterJugular.mod_k_bucket_readout`. -/
theorem mod_k_readout_eq_of_mod_val {k : Nat} (hk0 : 0 < k) {i j : Fin 118}
    (h : i.val % k = j.val % k) :
    (⟨i.val % k, Nat.mod_lt i.val hk0⟩ : Fin k) =
      (⟨j.val % k, Nat.mod_lt j.val hk0⟩ : Fin k) := by
  apply Fin.ext
  exact h

/-! ## Parametric `Fin p` palette index + period-`p` Markov stability -/

/-- Mod-`p` reduction into `Fin p` — generic bucket for any alphabet size `p`. -/
def modPaletteIndex (p : Nat) (hp : 0 < p) (n : Nat) : Fin p :=
  ⟨n % p, Nat.mod_lt n hp⟩

/-- **Markov II (general period):** `n ↦ n + p` fixes the mod-`p` residue class. -/
theorem markov_stabilization_period (p : Nat) (hp : 0 < p) (n : Nat) :
    modPaletteIndex p hp (n + p) = modPaletteIndex p hp n := by
  apply Fin.ext
  show (n + p) % p = n % p
  rw [Nat.add_mod_right]

/-! ## Parametric mod-`p` readouts are never injective on `Fin 118` when `p < 118` -/

theorem atlas_rows_zero_and_p_distinct (p : Nat) (hp0 : 0 < p) (hp118 : p < 118) :
    (⟨0, by decide⟩ : Fin 118) ≠ ⟨p, hp118⟩ := by
  intro h
  have hz : (0 : Nat) = p := congrArg Fin.val h
  rw [← hz] at hp0
  exact Nat.lt_irrefl 0 hp0

theorem mod_p_bucket_values_equal (p : Nat) (hp0 : 0 < p) (hp118 : p < 118) :
    modPaletteIndex p hp0 (⟨0, by decide⟩ : Fin 118).val =
      modPaletteIndex p hp0 (⟨p, hp118⟩ : Fin 118).val := by
  apply Fin.ext
  show (0 : Nat) % p = p % p
  rw [Nat.zero_mod, Nat.mod_self]

theorem mod_palette_bucket_readout_not_injective (p : Nat) (hp0 : 0 < p) (hp118 : p < 118) :
    ¬Function.Injective (fun i : Fin 118 => modPaletteIndex p hp0 i.val) := by
  intro hInj
  exact atlas_rows_zero_and_p_distinct p hp0 hp118 (hInj (mod_p_bucket_values_equal p hp0 hp118))

/-! ## Injective “tagged” atlases: disambiguate the periodic projection -/

/-- Pair each row with its own index — **injective** regardless of palette collapse. -/
def rowTaggedDiagram (i : Fin 118) : Diagram × Fin 118 :=
  (elementDiagram i, i)

theorem rowTaggedDiagram_injective : Function.Injective rowTaggedDiagram := by
  intro i j h
  exact congrArg Prod.snd h

/-- Jones polynomial paired with the row index — injective on `Fin 118`. -/
def rowTaggedJones (i : Fin 118) : LaurentPoly × Nat :=
  (jonesPoly (elementDiagram i), i.val)

theorem rowTaggedJones_injective : Function.Injective rowTaggedJones := by
  intro i j h
  exact Fin.ext (congrArg Prod.snd h)

/-! ## Injective `Fin 118 → Diagram` codec (118 distinct diagram *terms*) -/

/-- Extend the unknot’s resolution list with a formal tag `(row, 0)`.

The resulting `Diagram` is a **codec carrier**: Kauffman summands acquire an
extra formal term keyed by `row.val`. **Not** an assertion that IUPAC row `Z`
is ambient-isotopic to a distinguished classical link — this only forces
`DecidableEq` injectivity on the `Diagram` type. -/
def diagramCodecRow (row : Fin 118) : Diagram :=
  ⟨0, 0, [(0, 1), (row.val, 0)]⟩

theorem diagramCodecRow_injective : Function.Injective diagramCodecRow := by
  intro i j heq
  apply Fin.ext
  have hres : [(0, 1), (i.val, 0)] = [(0, 1), (j.val, 0)] :=
    congrArg Diagram.resolutions heq
  have ht : [(i.val, 0)] = [(j.val, 0)] := by
    simpa [List.tail_cons] using congrArg List.tail hres
  have hi : i.val = j.val := by
    have hg := congrArg
        (fun (l : List (Nat × Nat)) => match l with | [] => 0 | p :: _ => p.1) ht
    simpa using hg
  exact hi

end PeriodicElementLinkAtlas
end Gnosis
