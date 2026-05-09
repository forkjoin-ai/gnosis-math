import Init
import Gnosis.FrfInherentGestalt

/-!
# FRF witness tower — dependent spine, digit isomorphism, dual homomorphism jugular

**The jugular.** The fork spine is not metadata: `FrfOneStep n` is a dependent witness bundle,

and it is *subsingleton* — triangle coordinates are unique (`frf_one_step_subsingleton`). That is the
formal “intrinsic FRF” claim at dependent-type strength.

**Tower / dilation retract.** `frfDigits` unfolds `Nat` into little-endian base‑3 digits (`Fin 3`).
`frfFromDigits` folds back. The round-trip `frf_from_digits_fr_digits` is the algebraic spine saying:
every natural is **literally** a finite iterated fork (`frf_jugular_round_trip`).

**Telescope / iterated quotient.** `Nat.repeat frfFold` composes `RankingFrfBridge.frfFold`; its iteration count
matches `(frfDigits n).length` (`repeat_frFold_length_digits`). Greedy digits telescope one fold step at a time
(`frf_digits_fr_mod_fold`); the same step splits `triadMerge (frfDigits n)` into head digit plus quotient tail
(`triad_merge_frDigits_succ`), packaged beside length/`Nat.repeat` algebra (`frf_telescope_quotient_step`). **GF(2)
parity track:** map each digit to odd/even (`finThreeParityBit`), fold with `xorMerge`; one quotient step matches the same
spine (`frf_digits_xor_parity_merge_succ`, bundled as `frf_telescope_braid_quotient_step`). **Tumble / “multiset” merge:**
Init has no `Multiset`, but `List.Perm` witnesses same multiset of digits; `triad_merge_perm` proves `triadMerge` factors
through that quotient (“Race blender”). **`++` bridges into `Perm`:** swapping concatenated blocks is literally
`List.perm_append_comm`, hence `triad_merge_append_perm_comm`; block-wise shuffles lift through `triad_merge_append`
(`triad_merge_perm_append_blocks`). **XorMerge** mirrors the same picture (`xor_merge_perm`,
`xor_merge_append_perm_comm`, `xor_merge_perm_append_blocks`). The **first** greedy residue still reads **native**
`n % 3` (`frf_first_residual_eq_nat_mod`), while the global triadic merge is the digit-sum monoid (`triadAdd`), not Horner
value — relate `n % 3` through Horner/`frfFromDigits` mod‑3, not digit-sum confusion. **Gestalt vs clock:** commutative
monoid merges (`triadMerge`, `xorMerge`) forget digit/bit order along `List.Perm`; Horner reconstruction (`frfFromDigits`)
weights positions by `3^k`, so colliding “first vs last” residues across towers changes the **positional** story without
changing the **triadic summary** — witness `exists_perm_same_triad_merge_diff_horner`. **`triadMerge` is many‑to‑one**
(`triad_merge_not_injective`): not a cryptographic one‑way function, but a **forgetful quotient**; **`frfDigits n`**
picks the canonical magnitude‑bearing expansion (`frf_from_digits_fr_digits`), while multiset summaries discard positional
information. **Queued follow‑ons:** Horner mod‑3 packaging with condensation; optional explicit
braid/word‑group layer beyond `Perm`; richer signed‑constellation / phase metaphors stay narrative unless encoded as
additional typed carriers. **Prefix / truncation bookkeeping:** `Gnosis.FrfWitnessTowerTruncation` packages
`take`/`drop` splits for `triadMerge`, `xorMerge`, and the parity-bit track.

**Dual monoid quotients (parallel-safe merges).**

- XOR via `xorMerge` — homomorphism out of `(List Bool, ++)` into `(Bool, xor)`
  (`xor_merge_append`, iterated associativity `xor_merge_fold_append`).
- Triadic via `triadMerge` — homomorphism out of `(List (Fin 3), ++)` into `(Fin 3, triadAdd)`
  (`triad_merge_append`).

**Race (two readings, both formal).**

1. **Fiber race / residue select** — already named on the numeric spine: `RankingFrfBridge.frfRace` is an
   alias of `frfFork` (“choose the winning residue `r : Fin 3` at this fork”).
2. **Merge contention / schedule** — combining observation packets commutes (`combineObservation_comm`) and
   associates (`combineObservation_assoc`), so **`observationFold`** is insensitive to block order
   (`observationFold_append_comm`): two streams arrive interleaved only up to concatenation of finite chunks,
   and the folded witness matches commuting the chunks. At the digit list layer, **adjacent triadic lanes
   commute** (`triad_merge_swapAdjacent`), generating permutation steps toward full multiset invariance
   (`triad_merge_perm`), and **block tumble** (`triad_merge_append_perm_comm`) connects `++` with `List.Perm` via
   `perm_append_comm`.

**Observation jugular.** `ObservationWitness := Bool × FiveTriadWitness` merges componentwise; the large
certificate `frf_jugular_certificate` bundles subsingleton + round-trip + both append laws + observation
associativity — one citation block for scheduler/OR proofs that glue GF(2) with triadic fibers.

Init-only. Zero `sorry`.
-/

namespace Gnosis
namespace FrfWitnessTower

open Gnosis.RankingFrfBridge
open Gnosis.FrfInherentGestalt

/-! ## Dependent one-step witness (canonical triangle slice over `n`) -/

/-- Dependent bundle: `n` equals one `frfFork k r` step (triangle vertex over `n`). -/
structure FrfOneStep (n : Nat) where
  k : Nat
  r : Fin 3
  eq : n = frfFork k r.val

/-- Canonical fiber coordinate extracted from `Nat` itself (`nat_is_fr_fork`). -/
def frfOneStepCanonical (n : Nat) : FrfOneStep n where
  k := n / 3
  r := ⟨n % 3, Nat.mod_lt n (by decide : 0 < 3)⟩
  eq := nat_is_fr_fork n

theorem frf_one_step_subsingleton (n : Nat) (w w' : FrfOneStep n) : w = w' := by
  obtain ⟨k, r, he⟩ := w
  obtain ⟨k', r', he'⟩ := w'
  have hp : frfFork k r.val = frfFork k' r'.val :=
    (Eq.symm he).trans he'
  rcases frf_fork_unique k k' r r' hp with ⟨rfl, rfl⟩
  rfl

theorem frf_one_step_eq_canonical (n : Nat) (w : FrfOneStep n) : w = frfOneStepCanonical n :=
  frf_one_step_subsingleton n w (frfOneStepCanonical n)

/-! ## Little-endian base‑3 tower: digits ⇄ `Nat` -/

/-- Greedy least-significant-first base‑3 expansion (fork-unfold). -/
def frfDigits (n : Nat) : List (Fin 3) :=
  if hn : n = 0 then []
  else
    have _lt : n / 3 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 3)
    ⟨n % 3, Nat.mod_lt n (by decide : 0 < 3)⟩ :: frfDigits (n / 3)
termination_by n

/-- Horner-style fold from digits back to a natural (inverse spine). -/
def frfFromDigits : List (Fin 3) → Nat
  | [] => 0
  | d :: ds => d.val + 3 * frfFromDigits ds

theorem frf_from_digits_fr_digits (n : Nat) : frfFromDigits (frfDigits n) = n :=
  Nat.strongRecOn n fun n ih => by
    by_cases h0 : n = 0
    · subst h0
      unfold frfDigits
      rfl
    · unfold frfDigits
      simp [if_neg h0]
      dsimp [frfFromDigits]
      rw [ih (n / 3) (Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide : 1 < 3))]
      calc
        n % 3 + 3 * (n / 3) = 3 * (n / 3) + n % 3 := Nat.add_comm _ _
        _ = n := Nat.div_add_mod n 3

theorem frf_digits_nil_iff_zero {n : Nat} : frfDigits n = [] ↔ n = 0 := by
  constructor
  · intro h
    by_cases hz : n = 0
    · exact hz
    · unfold frfDigits at h
      simp [if_neg hz] at h
  · intro h
    subst h
    unfold frfDigits
    rfl

/-! ## Iterated `frfFold` ⇔ greedy digit length (`Nat.repeat`) -/

/-- `Nat.repeat` peels an outer `f` (`repeat f (k+1) a = f (repeat f k a)`). -/
theorem repeat_frFold_succ_eq (k : Nat) (n : Nat) :
    Nat.repeat frfFold (Nat.succ k) n = frfFold (Nat.repeat frfFold k n) := by
  simp only [Nat.repeat]

theorem repeat_frFold_comm (k : Nat) (n : Nat) :
    frfFold (Nat.repeat frfFold k n) = Nat.repeat frfFold k (frfFold n) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp only [Nat.repeat]
      exact congrArg frfFold ih

/-- Nested `frfDigits` δ-steps align propositionally under `Nat.strongRecOn`. -/
theorem frfDigits_expand_if (q : Nat) :
    frfDigits q =
      if hq : q = 0 then []
      else ⟨q % 3, Nat.mod_lt q (by decide : 0 < 3)⟩ :: frfDigits (q / 3) := by
  refine Nat.strongRecOn q fun q ih => ?_
  rcases q with rfl | q'
  · unfold frfDigits
    rfl
  · unfold frfDigits
    rw [dif_neg (Nat.succ_ne_zero q')]
    let ql := (q' + 1) / 3
    have ql_lt : ql < q' + 1 :=
      Nat.div_lt_self (Nat.succ_pos q') (by decide : 1 < 3)
    rw [← ih ql ql_lt]
    rfl

theorem frf_digits_fr_mod_fold {n : Nat} (hn : n ≠ 0) :
    frfDigits n = ⟨n % 3, Nat.mod_lt n (by decide : 0 < 3)⟩ :: frfDigits (frfFold n) := by
  cases n with
  | zero =>
      nomatch hn rfl
  | succ n' =>
      dsimp [frfFold]
      unfold frfDigits
      rw [dif_neg (Nat.succ_ne_zero n')]
      rw [← frfDigits_expand_if ((n' + 1) / 3)]

theorem repeat_frFold_length_digits (n : Nat) :
    Nat.repeat frfFold (List.length (frfDigits n)) n = 0 := by
  refine Nat.strongRecOn n fun n ih => ?_
  by_cases h0 : n = 0
  · subst h0
    simp [frfDigits, Nat.repeat]
  · have hl :
      List.length (frfDigits n) = Nat.succ (List.length (frfDigits (frfFold n))) := by
      rw [frf_digits_fr_mod_fold h0]
      rfl
    rw [hl, repeat_frFold_succ_eq, repeat_frFold_comm]
    exact ih (frfFold n) (Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide : 1 < 3))

theorem frf_first_residual_eq_nat_mod (n : Nat) (hn : n ≠ 0) :
    (frfDigits n).get ⟨0, List.ne_nil_iff_length_pos.mp (mt frf_digits_nil_iff_zero.mp hn)⟩ =
      ⟨n % 3, Nat.mod_lt n (by decide : 0 < 3)⟩ := by
  cases n with
  | zero =>
      nomatch hn rfl
  | succ n' =>
      simp [frf_digits_fr_mod_fold (Nat.succ_ne_zero n')]

/-! ## Triadic word merge (second homomorphism beside XOR) -/

def triadZero : Fin 3 :=
  ⟨0, by decide⟩

theorem triadAdd_zero_left (a : Fin 3) : triadAdd triadZero a = a := by
  apply Fin.ext
  simp [triadAdd, triadZero]

theorem triadAdd_zero_right (a : Fin 3) : triadAdd a triadZero = a := by
  rw [triadAdd_comm]
  exact triadAdd_zero_left a

/-- Fold triadic words with `triadAdd` — neutral `triadZero`. -/
def triadMerge : List (Fin 3) → Fin 3
  | [] => triadZero
  | d :: ds => triadAdd d (triadMerge ds)

theorem triad_merge_nil : triadMerge [] = triadZero :=
  rfl

theorem triad_merge_append (xs ys : List (Fin 3)) :
    triadMerge (xs ++ ys) = triadAdd (triadMerge xs) (triadMerge ys) := by
  induction xs with
  | nil =>
      simp [triadMerge, triadAdd_zero_left]
  | cons x xs ih =>
      simp [triadMerge, ih, triadAdd_assoc]

theorem triad_merge_fold_append (xs ys zs : List (Fin 3)) :
    triadMerge ((xs ++ ys) ++ zs) =
      triadAdd (triadAdd (triadMerge xs) (triadMerge ys)) (triadMerge zs) := by
  simp [triad_merge_append, triadAdd_assoc]

theorem triad_merge_frDigits_succ {n : Nat} (hn : n ≠ 0) :
    triadMerge (frfDigits n) =
      triadAdd ⟨n % 3, Nat.mod_lt n (by decide : 0 < 3)⟩ (triadMerge (frfDigits (frfFold n))) := by
  rw [frf_digits_fr_mod_fold hn]
  rfl

theorem frf_telescope_quotient_step {n : Nat} (hn : n ≠ 0) :
    List.length (frfDigits n) = Nat.succ (List.length (frfDigits (frfFold n))) ∧
      Nat.repeat frfFold (List.length (frfDigits n)) n =
        Nat.repeat frfFold (List.length (frfDigits (frfFold n))) (frfFold n) ∧
      triadMerge (frfDigits n) =
        triadAdd ⟨n % 3, Nat.mod_lt n (by decide : 0 < 3)⟩ (triadMerge (frfDigits (frfFold n))) :=
  ⟨by rw [frf_digits_fr_mod_fold hn]; rfl,
    by
      have hl :
          List.length (frfDigits n) = Nat.succ (List.length (frfDigits (frfFold n))) := by
        rw [frf_digits_fr_mod_fold hn]
        rfl
      rw [hl, repeat_frFold_succ_eq, repeat_frFold_comm],
    triad_merge_frDigits_succ hn⟩

/-! ### Parity bits (`Fin 3 → Bool`) along the same greedy quotient spine -/

/-- Odd digits (`1`) carry `true`; `0` and `2` carry `false` — one GF(2) shadow of the triadic fiber. -/
def finThreeParityBit (d : Fin 3) : Bool :=
  decide (d.val % 2 = 1)

theorem frf_digits_xor_parity_merge_succ {n : Nat} (hn : n ≠ 0) :
    xorMerge (List.map finThreeParityBit (frfDigits n)) =
      (finThreeParityBit ⟨n % 3, Nat.mod_lt n (by decide : 0 < 3)⟩).xor
        (xorMerge (List.map finThreeParityBit (frfDigits (frfFold n)))) := by
  rw [frf_digits_fr_mod_fold hn]
  rfl

/-- Same depth/`Nat.repeat`/`length` spine as `frf_telescope_quotient_step`, extended with the XOR parity track. -/
theorem frf_telescope_braid_quotient_step {n : Nat} (hn : n ≠ 0) :
    List.length (frfDigits n) = Nat.succ (List.length (frfDigits (frfFold n))) ∧
      Nat.repeat frfFold (List.length (frfDigits n)) n =
        Nat.repeat frfFold (List.length (frfDigits (frfFold n))) (frfFold n) ∧
      triadMerge (frfDigits n) =
        triadAdd ⟨n % 3, Nat.mod_lt n (by decide : 0 < 3)⟩ (triadMerge (frfDigits (frfFold n))) ∧
      xorMerge (List.map finThreeParityBit (frfDigits n)) =
        (finThreeParityBit ⟨n % 3, Nat.mod_lt n (by decide : 0 < 3)⟩).xor
          (xorMerge (List.map finThreeParityBit (frfDigits (frfFold n)))) :=
  ⟨by rw [frf_digits_fr_mod_fold hn]; rfl,
    by
      have hl :
          List.length (frfDigits n) = Nat.succ (List.length (frfDigits (frfFold n))) := by
        rw [frf_digits_fr_mod_fold hn]
        rfl
      rw [hl, repeat_frFold_succ_eq, repeat_frFold_comm],
    triad_merge_frDigits_succ hn,
    frf_digits_xor_parity_merge_succ hn⟩

/-! ## XOR homomorphism iterated across nested partitions -/

theorem xor_merge_fold_append (xs ys zs : List Bool) :
    xorMerge ((xs ++ ys) ++ zs) =
      ((xorMerge xs).xor (xorMerge ys)).xor (xorMerge zs) := by
  simp [xorMerge_append]

/-! ## Observation carrier: GF(2) quotient ⊗ five triadic fibers -/

abbrev ObservationWitness := Bool × FiveTriadWitness

def combineObservation (u v : ObservationWitness) : ObservationWitness :=
  (u.1.xor v.1, combineFiveTriads u.2 v.2)

/-- Neutral observation: XOR identity `false`, triadic lane identities at each fiber index. -/
def observationNeutral : ObservationWitness :=
  (false, fun _ => triadZero)

theorem combineObservation_observationNeutral_left (u : ObservationWitness) :
    combineObservation observationNeutral u = u := by
  rcases u with ⟨b, t⟩
  apply Prod.ext
  · simp [combineObservation, observationNeutral]
  · funext i
    simp [combineObservation, observationNeutral, combineFiveTriads, triadAdd_zero_left]

theorem combineObservation_observationNeutral_right (u : ObservationWitness) :
    combineObservation u observationNeutral = u := by
  rcases u with ⟨b, t⟩
  apply Prod.ext
  · simp [combineObservation, observationNeutral]
  · funext i
    simp [combineObservation, observationNeutral, combineFiveTriads, triadAdd_zero_right]

theorem combineObservation_comm (u v : ObservationWitness) :
    combineObservation u v = combineObservation v u := by
  rcases u with ⟨ub, ut⟩
  rcases v with ⟨vb, vt⟩
  apply Prod.ext
  · simp [combineObservation, Bool.xor_comm]
  · funext i
    simp [combineObservation, combineFiveTriads, triadAdd_comm]

theorem combineObservation_assoc (u v w : ObservationWitness) :
    combineObservation (combineObservation u v) w =
      combineObservation u (combineObservation v w) := by
  rcases u with ⟨ub, ut⟩
  rcases v with ⟨vb, vt⟩
  rcases w with ⟨wb, wt⟩
  apply Prod.ext
  · show (ub.xor vb).xor wb = ub.xor (vb.xor wb)
    rw [Bool.xor_assoc]
  · show combineFiveTriads (combineFiveTriads ut vt) wt = combineFiveTriads ut (combineFiveTriads vt wt)
    rw [combineFiveTriads_assoc]

/-! ## Race layer — fold observation packets; blocks commute (schedule-blind merge) -/

/-- Fold a finite trace of observation witnesses with `combineObservation`. -/
def observationFold : List ObservationWitness → ObservationWitness
  | [] => observationNeutral
  | x :: xs => combineObservation x (observationFold xs)

theorem observationFold_nil : observationFold [] = observationNeutral :=
  rfl

theorem observationFold_append (xs ys : List ObservationWitness) :
    observationFold (xs ++ ys) = combineObservation (observationFold xs) (observationFold ys) := by
  induction xs with
  | nil =>
      simp [observationFold, combineObservation_observationNeutral_left]
  | cons x xs ih =>
      simp only [List.cons_append, observationFold]
      rw [ih, ← combineObservation_assoc]

theorem observationFold_append_comm (xs ys : List ObservationWitness) :
    observationFold (xs ++ ys) = observationFold (ys ++ xs) := by
  rw [observationFold_append, observationFold_append ys xs, combineObservation_comm]

/-! ### Digit-stream contention — adjacent swaps preserve triadic merge -/

theorem triad_merge_swapAdjacent (x y : Fin 3) (zs : List (Fin 3)) :
    triadMerge (x :: y :: zs) = triadMerge (y :: x :: zs) := by
  simp only [triadMerge]
  rw [(triadAdd_assoc x y (triadMerge zs)).symm]
  rw [congrArg (fun w => triadAdd w (triadMerge zs)) (triadAdd_comm x y)]
  rw [triadAdd_assoc y x (triadMerge zs)]

/-- `triadMerge` is blind to permutation of digits — multiset merge / braid closure from adjacent swaps. -/
theorem triad_merge_perm {xs ys : List (Fin 3)} (h : List.Perm xs ys) : triadMerge xs = triadMerge ys := by
  induction h with
  | nil =>
      rfl
  | cons x _ ih =>
      simp [triadMerge, ih]
  | swap x y l =>
      exact Eq.symm (triad_merge_swapAdjacent x y l)
  | trans _ _ ih₁ ih₂ =>
      exact Eq.trans ih₁ ih₂

/-! #### Append ⊗ `Perm` (multiset quotient — Init has no `Multiset`)

`triad_merge_perm` says `triadMerge` is well-defined on `List.Perm` equivalence classes (same multiset of digits).
Together with `triad_merge_append`, block reorderings and within-block shuffles are transparent to the merged fiber.
-/

theorem triad_merge_append_perm_comm (xs ys : List (Fin 3)) :
    triadMerge (xs ++ ys) = triadMerge (ys ++ xs) :=
  triad_merge_perm List.perm_append_comm

theorem triad_merge_perm_append_blocks {xs xs' ys ys' : List (Fin 3)}
    (hx : List.Perm xs xs') (hy : List.Perm ys ys') :
    triadMerge (xs ++ ys) = triadMerge (xs' ++ ys') := by
  simp [triad_merge_append, triad_merge_perm hx, triad_merge_perm hy]

/-- Same multiset of digits ⇒ same `triadMerge`; positional Horner spine can still disagree (`frfFromDigits`). -/
theorem exists_perm_same_triad_merge_diff_horner :
    ∃ xs ys : List (Fin 3),
      List.Perm xs ys ∧
        frfFromDigits xs ≠ frfFromDigits ys ∧
          triadMerge xs = triadMerge ys := by
  let d1 : Fin 3 := ⟨1, by decide⟩
  let d2 : Fin 3 := ⟨2, by decide⟩
  let xs := d1 :: d2 :: []
  let ys := d2 :: d1 :: []
  have hswap := List.Perm.swap d1 d2 []
  refine ⟨xs, ys, hswap.symm, ?_, ?_⟩
  · simp [xs, ys, frfFromDigits, d1, d2]
  · exact triad_merge_perm hswap.symm

/-- Distinct digit lists can yield the same `triadMerge` witness — the map is not injective. -/
theorem triad_merge_not_injective : ¬Function.Injective triadMerge := by
  intro hi
  let d1 : Fin 3 := ⟨1, by decide⟩
  let d2 : Fin 3 := ⟨2, by decide⟩
  have hs : triadMerge [d2] = triadMerge [d1, d1] := by
    simp [triadMerge, triadAdd, triadZero, d1, d2]
  have hne : ([d2] : List (Fin 3)) ≠ [d1, d1] := by decide
  exact hne (hi hs)

theorem xor_merge_swapAdjacent (x y : Bool) (zs : List Bool) :
    xorMerge (x :: y :: zs) = xorMerge (y :: x :: zs) := by
  simp only [xorMerge]
  rw [(Bool.xor_assoc x y (xorMerge zs)).symm]
  rw [congrArg (fun w => Bool.xor w (xorMerge zs)) (Bool.xor_comm x y)]
  rw [Bool.xor_assoc y x (xorMerge zs)]

/-- `xorMerge` is blind to permutation of bits — the GF(2) analogue of `triad_merge_perm`. -/
theorem xor_merge_perm {xs ys : List Bool} (h : List.Perm xs ys) : xorMerge xs = xorMerge ys := by
  induction h with
  | nil =>
      rfl
  | cons x _ ih =>
      simp [xorMerge, ih]
  | swap x y l =>
      exact Eq.symm (xor_merge_swapAdjacent x y l)
  | trans _ _ ih₁ ih₂ =>
      exact Eq.trans ih₁ ih₂

theorem xor_merge_append_perm_comm (xs ys : List Bool) :
    xorMerge (xs ++ ys) = xorMerge (ys ++ xs) :=
  xor_merge_perm List.perm_append_comm

theorem xor_merge_perm_append_blocks {xs xs' ys ys' : List Bool}
    (hx : List.Perm xs xs') (hy : List.Perm ys ys') :
    xorMerge (xs ++ ys) = xorMerge (xs' ++ ys') := by
  simp [xorMerge_append, xor_merge_perm hx, xor_merge_perm hy]

/-! ## Round-trip packaged corollary (triangle ⇄ tower retract on naturals) -/

theorem frf_jugular_round_trip (n : Nat) : frfFromDigits (frfDigits n) = n :=
  frf_from_digits_fr_digits n

/-! ## Jugular certificate (single cite-all block) -/

theorem frf_jugular_certificate (n : Nat) (w w' : FrfOneStep n) (xs ys : List Bool)
    (ds dt : List (Fin 3)) (u v zob : ObservationWitness) :
    (w = w') ∧
      frfFromDigits (frfDigits n) = n ∧
        xorMerge (xs ++ ys) = (xorMerge xs).xor (xorMerge ys) ∧
          triadMerge (ds ++ dt) = triadAdd (triadMerge ds) (triadMerge dt) ∧
            combineObservation (combineObservation u v) zob =
              combineObservation u (combineObservation v zob) :=
  ⟨frf_one_step_subsingleton n w w',
    frf_jugular_round_trip n,
    xorMerge_append xs ys,
    triad_merge_append ds dt,
    combineObservation_assoc u v zob⟩

/-- Race / schedule-blind merge facts beside the jugular certificate. -/
theorem frf_race_schedule_certificate (xs ys : List ObservationWitness) (x y : Fin 3) (zs : List (Fin 3))
    (a b : Bool) (wb : List Bool) :
    observationFold (xs ++ ys) = observationFold (ys ++ xs) ∧
      triadMerge (x :: y :: zs) = triadMerge (y :: x :: zs) ∧
        xorMerge (a :: b :: wb) = xorMerge (b :: a :: wb) :=
  ⟨observationFold_append_comm xs ys, triad_merge_swapAdjacent x y zs, xor_merge_swapAdjacent a b wb⟩

end FrfWitnessTower
end Gnosis
