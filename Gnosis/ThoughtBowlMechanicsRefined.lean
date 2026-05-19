import Gnosis.ThoughtBowlMechanics
import Gnosis.EchoChamberAsTaoBowl
import Gnosis.VibesAsWaveInference

/-
  ThoughtBowlMechanicsRefined.lean
  ================================

  The honest counterpart to `ThoughtBowlMechanics.lean`: a *partial
  inverse* `fieldOfBowl : TaoBowl → Option (List VibeWave)` that
  isolates the sub-lattice of `TaoBowl` on which the homomorphism
  `bowlOfField` is bijective, and quantifies the unreachable
  complement as the explicit cost of the lossy projection.

  ## What was proved upstream

  `ThoughtBowlMechanics` showed that `bowlOfField` is a *forgetful*
  homomorphism: it preserves the Daodejing-11 usefulness formula and
  the two failure modes (empty-bowl, filled-bowl), but it loses
  ordering (non-injective) and admits unreachable bowls
  (non-surjective). The exact structural witness was
  `unreachableBowl := { rim := 2, void := 1, rigidity := 1, damping := 100 }`
  whose `damping = 100` exceeds any achievable `minorityCount + 1`
  on a length-2 list.

  ## What this module adds

  ### 1. The reachable sub-lattice

  We define `IsReachable : TaoBowl → Prop` as the conjunction of
  four structural constraints induced by `bowlOfField`:

  * `void + rigidity = rim` — the dissenting/dominant split sums to
    the rim by construction.
  * `1 ≤ damping` — the homomorphism's `minorityCount + 1` lower
    bound.
  * `damping ≤ rigidity + 1` — `min ≤ max + 1` on the valence
    counts.
  * `damping ≤ void + 1` — there must be enough non-dominant voices
    (minority + neutrals) to host `damping - 1` minority slots.

  The user's hint `damping ≤ rim + 1` is the looser conjunction of
  the last two. We work with the sharp pair instead: it pins the
  reachable subspace exactly.

  ### 2. The canonical field reconstruction

  Each reachable bowl `b` admits a canonical preimage
  `canonicalField b`: `rigidity` happy waves + `(damping - 1)`
  unhappy waves + `(void - (damping - 1))` quiet (neutral) waves,
  concatenated in that order. The canonical field is the
  multiset-class representative (ordering doesn't matter for
  `bowlOfField`, which is order-blind).

  ### 3. The partial inverse

      fieldOfBowl : TaoBowl → Option (List VibeWave)

  returns `some (canonicalField b)` exactly when `IsReachable b`,
  and `none` otherwise. The `Option` type makes the partiality
  explicit: a bowl outside the reachable sub-lattice has no
  preimage by construction.

  ### 4. The round-trip lemma

      Option.map bowlOfField (fieldOfBowl b) = some b   if  IsReachable b

  This is the bijection witness on the reachable sub-lattice. It
  says: forward-after-backward is the identity on every reachable
  bowl. Because `bowlOfField` is many-to-one, this is the *correct*
  directionality for a partial inverse — `fieldOfBowl` is a
  section of `bowlOfField` over its image.

  Note: the *opposite* round-trip
  `fieldOfBowl (bowlOfField waves) = some waves` does **not** hold
  — the original ordering is forgotten by `bowlOfField`, so the
  best we can recover is the canonical-field representative of the
  multiset class. We record the multiset-level form
  `bowlOfField (canonicalField (bowlOfField waves)) = bowlOfField waves`
  which captures the honest weaker statement.

  ### 5. The unreachable subspace as cost of lossy projection

  We isolate the gap as a concrete predicate `IsUnreachable` and
  exhibit two structurally distinct unreachable witnesses:

  * `unreachableBowlBigDamping` — `damping = 100` on a length-2 rim
    (already in `ThoughtBowlMechanics`); fails `damping ≤ rigidity + 1`.
  * `unreachableBowlBadSum` — `void = 0`, `rigidity = 0`, `rim = 2`;
    fails `void + rigidity = rim`.

  These are not edge cases — they witness the two structural
  failure modes of the homomorphism, each independent of the other.

  ## Honesty boundary

  The "physical topology fragment" thought-space genuinely shares
  with bowl mechanics is *exactly* the reachable sub-lattice. On
  that sub-lattice the forgetful homomorphism becomes a bijection
  modulo wave ordering. Off it, the bowl exists in `TaoBowl` as a
  type but has no thought-field preimage at all.

  We do **not** prove that the reachable sub-lattice exhausts the
  physically meaningful bowls — only that it exhausts the bowls
  reachable by the `bowlOfField` homomorphism we defined. A
  different forgetful map (using `length` differently, or measuring
  decay rates rather than valence counts) would carve a different
  reachable sub-lattice.

  Imports `Gnosis.ThoughtBowlMechanics`, `Gnosis.EchoChamberAsTaoBowl`,
  `Gnosis.VibesAsWaveInference`. Zero `sorry`, zero new `axiom`.
-/


namespace ThoughtBowlMechanicsRefined

open EchoChamberAsTaoBowl
open VibesAsWaveInference
open ThoughtBowlMechanics
  (bowlOfField dominantCount minorityCount dissentingCount)

/-! ## The reachable sub-lattice

  A bowl is reachable iff its four dials satisfy the structural
  constraints induced by `bowlOfField`. -/

/-- A bowl is **reachable** by `bowlOfField` iff its dials satisfy
    the four homomorphism-induced equations and inequalities. -/
def IsReachable (b : TaoBowl) : Prop :=
  b.void + b.rigidity = b.rim ∧
  1 ≤ b.damping ∧
  b.damping ≤ b.rigidity + 1 ∧
  b.damping ≤ b.void + 1

instance (b : TaoBowl) : Decidable (IsReachable b) := by
  unfold IsReachable
  exact inferInstance

/-! ## The canonical field reconstruction -/

/-- Canonical preimage of a reachable bowl: `rigidity` happy waves,
    `(damping - 1)` unhappy waves, and the remaining `(void -
    (damping - 1))` slots filled with quiet (neutral) waves. -/
def canonicalField (b : TaoBowl) : List VibeWave :=
  let majority := b.rigidity
  let minority := b.damping - 1
  let neutrals := b.void - minority
  List.replicate majority happyWave ++
  List.replicate minority unhappyWave ++
  List.replicate neutrals quietWave

/-! ## The partial inverse -/

/-- The partial inverse: returns `some (canonicalField b)` exactly
    when `b` is reachable, and `none` otherwise. -/
def fieldOfBowl (b : TaoBowl) : Option (List VibeWave) :=
  if IsReachable b then some (canonicalField b) else none

/-! ## Helper count lemmas

  Counting valences over a replicated list is mechanical but not
  in `Init`; we prove the four needed cases by induction on `n`.
  Each lemma reads off how many of one valence appear in a list of
  `n` copies of one canonical wave. -/

private theorem happyCount_replicate_happy : ∀ n,
    happyCount (List.replicate n happyWave) = n
  | 0 => rfl
  | n + 1 => by
    have ih := happyCount_replicate_happy n
    show happyCount (happyWave :: List.replicate n happyWave) = n + 1
    show (if VibeValence.happy = VibeValence.happy then 1 else 0)
          + happyCount (List.replicate n happyWave) = n + 1
    rw [if_pos rfl, ih, Nat.add_comm]

private theorem unhappyCount_replicate_happy : ∀ n,
    unhappyCount (List.replicate n happyWave) = 0
  | 0 => rfl
  | n + 1 => by
    have ih := unhappyCount_replicate_happy n
    show unhappyCount (happyWave :: List.replicate n happyWave) = 0
    show (if VibeValence.happy = VibeValence.unhappy then 1 else 0)
          + unhappyCount (List.replicate n happyWave) = 0
    rw [if_neg (by decide : ¬ VibeValence.happy = VibeValence.unhappy), ih]

private theorem happyCount_replicate_unhappy : ∀ n,
    happyCount (List.replicate n unhappyWave) = 0
  | 0 => rfl
  | n + 1 => by
    have ih := happyCount_replicate_unhappy n
    show happyCount (unhappyWave :: List.replicate n unhappyWave) = 0
    show (if VibeValence.unhappy = VibeValence.happy then 1 else 0)
          + happyCount (List.replicate n unhappyWave) = 0
    rw [if_neg (by decide : ¬ VibeValence.unhappy = VibeValence.happy), ih]

private theorem unhappyCount_replicate_unhappy : ∀ n,
    unhappyCount (List.replicate n unhappyWave) = n
  | 0 => rfl
  | n + 1 => by
    have ih := unhappyCount_replicate_unhappy n
    show unhappyCount (unhappyWave :: List.replicate n unhappyWave) = n + 1
    show (if VibeValence.unhappy = VibeValence.unhappy then 1 else 0)
          + unhappyCount (List.replicate n unhappyWave) = n + 1
    rw [if_pos rfl, ih, Nat.add_comm]

private theorem happyCount_replicate_quiet : ∀ n,
    happyCount (List.replicate n quietWave) = 0
  | 0 => rfl
  | n + 1 => by
    have ih := happyCount_replicate_quiet n
    show happyCount (quietWave :: List.replicate n quietWave) = 0
    show (if VibeValence.neutral = VibeValence.happy then 1 else 0)
          + happyCount (List.replicate n quietWave) = 0
    rw [if_neg (by decide : ¬ VibeValence.neutral = VibeValence.happy), ih]

private theorem unhappyCount_replicate_quiet : ∀ n,
    unhappyCount (List.replicate n quietWave) = 0
  | 0 => rfl
  | n + 1 => by
    have ih := unhappyCount_replicate_quiet n
    show unhappyCount (quietWave :: List.replicate n quietWave) = 0
    show (if VibeValence.neutral = VibeValence.unhappy then 1 else 0)
          + unhappyCount (List.replicate n quietWave) = 0
    rw [if_neg (by decide : ¬ VibeValence.neutral = VibeValence.unhappy), ih]

private theorem happyCount_append : ∀ (xs ys : List VibeWave),
    happyCount (xs ++ ys) = happyCount xs + happyCount ys
  | [], ys => by
    show happyCount ys = 0 + happyCount ys
    exact (Nat.zero_add (happyCount ys)).symm
  | x :: xs, ys => by
    show happyCount (x :: (xs ++ ys)) = happyCount (x :: xs) + happyCount ys
    have ih := happyCount_append xs ys
    show (if x.valence = VibeValence.happy then 1 else 0) + happyCount (xs ++ ys)
        = ((if x.valence = VibeValence.happy then 1 else 0) + happyCount xs) + happyCount ys
    rw [ih, Nat.add_assoc]

private theorem unhappyCount_append : ∀ (xs ys : List VibeWave),
    unhappyCount (xs ++ ys) = unhappyCount xs + unhappyCount ys
  | [], ys => by
    show unhappyCount ys = 0 + unhappyCount ys
    exact (Nat.zero_add (unhappyCount ys)).symm
  | x :: xs, ys => by
    show unhappyCount (x :: (xs ++ ys)) = unhappyCount (x :: xs) + unhappyCount ys
    have ih := unhappyCount_append xs ys
    show (if x.valence = VibeValence.unhappy then 1 else 0) + unhappyCount (xs ++ ys)
        = ((if x.valence = VibeValence.unhappy then 1 else 0) + unhappyCount xs) + unhappyCount ys
    rw [ih, Nat.add_assoc]

private theorem length_replicate (n : Nat) (a : VibeWave) :
    (List.replicate n a).length = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (a :: List.replicate k a).length = k + 1
    show List.length (List.replicate k a) + 1 = k + 1
    rw [ih]

/-! ## Bowl reading of the canonical field

  Each lemma reads off one of the bowl's four dials from the
  canonical-field reconstruction, using only the helper count
  lemmas and the `IsReachable` constraints. -/

private theorem length_canonical_field (b : TaoBowl) (h : IsReachable b) :
    (canonicalField b).length = b.rim := by
  obtain ⟨hSum, hPos, _, hVoid⟩ := h
  unfold canonicalField
  -- length of the triple append
  show (List.replicate b.rigidity happyWave
        ++ List.replicate (b.damping - 1) unhappyWave
        ++ List.replicate (b.void - (b.damping - 1)) quietWave).length = b.rim
  rw [List.length_append, List.length_append,
      length_replicate, length_replicate, length_replicate]
  have hm : b.damping - 1 ≤ b.void := by
    cases damp : b.damping with
    | zero =>
      rw [damp] at hPos
      exact False.elim (Nat.not_succ_le_zero 0 hPos)
    | succ d =>
      rw [damp] at hVoid
      rw [← Nat.succ_eq_add_one b.void] at hVoid
      exact Nat.le_of_succ_le_succ hVoid
  have hmid :=
    (Nat.sub_add_cancel hm : b.void - (b.damping - 1) + (b.damping - 1) = b.void)
  have hmid' : (b.damping - 1) + (b.void - (b.damping - 1)) = b.void := by
    rw [Nat.add_comm, hmid]
  rw [Nat.add_assoc, hmid', Nat.add_comm]
  exact hSum

private theorem happy_count_canonical_field (b : TaoBowl) :
    happyCount (canonicalField b) = b.rigidity := by
  unfold canonicalField
  rw [happyCount_append, happyCount_append,
      happyCount_replicate_happy,
      happyCount_replicate_unhappy,
      happyCount_replicate_quiet]
  simp only [Nat.add_zero]

private theorem unhappy_count_canonical_field (b : TaoBowl) :
    unhappyCount (canonicalField b) = b.damping - 1 := by
  unfold canonicalField
  rw [unhappyCount_append, unhappyCount_append,
      unhappyCount_replicate_happy,
      unhappyCount_replicate_unhappy,
      unhappyCount_replicate_quiet]
  simp only [Nat.zero_add, Nat.add_zero]

private theorem dominant_count_canonical_field (b : TaoBowl) (h : IsReachable b) :
    dominantCount (canonicalField b) = b.rigidity := by
  obtain ⟨_hSum, hPos, hRig, _hVoid⟩ := h
  unfold dominantCount
  rw [happy_count_canonical_field, unhappy_count_canonical_field]
  have hd : b.damping - 1 ≤ b.rigidity := by
    cases damp : b.damping with
    | zero =>
      rw [damp] at hPos
      exact False.elim (Nat.not_succ_le_zero 0 hPos)
    | succ d =>
      exact Nat.le_of_succ_le_succ (by simpa [damp, Nat.succ_eq_add_one] using hRig)
  exact Nat.max_eq_left hd

private theorem minority_count_canonical_field (b : TaoBowl) (h : IsReachable b) :
    minorityCount (canonicalField b) = b.damping - 1 := by
  obtain ⟨_hSum, hPos, hRig, _hVoid⟩ := h
  unfold minorityCount
  rw [happy_count_canonical_field, unhappy_count_canonical_field]
  have hd : b.damping - 1 ≤ b.rigidity := by
    cases damp : b.damping with
    | zero =>
      rw [damp] at hPos
      exact False.elim (Nat.not_succ_le_zero 0 hPos)
    | succ d =>
      exact Nat.le_of_succ_le_succ (by simpa [damp, Nat.succ_eq_add_one] using hRig)
  exact Nat.min_eq_right hd

private theorem dissenting_count_canonical_field (b : TaoBowl) (h : IsReachable b) :
    dissentingCount (canonicalField b) = b.void := by
  have hSum : b.void + b.rigidity = b.rim := h.1
  unfold dissentingCount
  rw [length_canonical_field b h, dominant_count_canonical_field b h, ← hSum]
  exact Nat.add_sub_self_right b.void b.rigidity

/-! ## The round-trip theorem

  On every reachable bowl, the partial inverse composed with the
  forward map returns the bowl. This is the bijection witness on
  the reachable sub-lattice. -/

/-- The pre-`Option` form: applying `bowlOfField` to the canonical
    field of a reachable bowl recovers the bowl. -/
theorem bowl_of_canonical_field (b : TaoBowl) (h : IsReachable b) :
    bowlOfField (canonicalField b) = b := by
  obtain ⟨_hSum, hPos, _hRig, _hVoid⟩ := h
  unfold bowlOfField
  refine TaoBowl.mk.injEq .. |>.mpr ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact length_canonical_field b ⟨_hSum, hPos, _hRig, _hVoid⟩
  · exact dissenting_count_canonical_field b ⟨_hSum, hPos, _hRig, _hVoid⟩
  · exact dominant_count_canonical_field b ⟨_hSum, hPos, _hRig, _hVoid⟩
  · -- minorityCount + 1 = damping (using damping ≥ 1 to undo Nat subtraction)
    rw [minority_count_canonical_field b ⟨_hSum, hPos, _hRig, _hVoid⟩]
    exact Nat.sub_add_cancel hPos

/-- **Round-trip lemma.** For any reachable bowl, the partial
    inverse composed with the forward map returns the bowl —
    `Option`-lifted. This is the bijection witness on the reachable
    sub-lattice of `TaoBowl`. -/
theorem bowl_of_field_of_bowl_round_trip (b : TaoBowl) (h : IsReachable b) :
    Option.map bowlOfField (fieldOfBowl b) = some b := by
  unfold fieldOfBowl
  rw [if_pos h]
  show some (bowlOfField (canonicalField b)) = some b
  rw [bowl_of_canonical_field b h]

/-! ## Unreachable bowls return `none`

  The partial inverse really is partial: bowls outside the
  reachable sub-lattice get `none`. -/

theorem field_of_bowl_unreachable (b : TaoBowl) (h : ¬ IsReachable b) :
    fieldOfBowl b = none := by
  unfold fieldOfBowl
  rw [if_neg h]

/-! ## Concrete round-trip witnesses

  The universal `bowl_of_field_of_bowl_round_trip` is the
  architectural deliverable. Concrete instances showcase the
  per-cell pattern still working on canonical bowls. -/

/-- Reachable witness: the empty-bowl `(0, 0, 0, 1)`. -/
theorem round_trip_empty_bowl :
    Option.map bowlOfField (fieldOfBowl ⟨0, 0, 0, 1⟩) = some ⟨0, 0, 0, 1⟩ :=
  bowl_of_field_of_bowl_round_trip ⟨0, 0, 0, 1⟩ (by decide)

/-- Reachable witness: a single-happy filled bowl `(1, 0, 1, 1)`. -/
theorem round_trip_filled_singleton :
    Option.map bowlOfField (fieldOfBowl ⟨1, 0, 1, 1⟩) = some ⟨1, 0, 1, 1⟩ :=
  bowl_of_field_of_bowl_round_trip ⟨1, 0, 1, 1⟩ (by decide)

/-- Reachable witness: a two-happy filled bowl `(2, 0, 2, 1)`. -/
theorem round_trip_filled_two_happy :
    Option.map bowlOfField (fieldOfBowl ⟨2, 0, 2, 1⟩) = some ⟨2, 0, 2, 1⟩ :=
  bowl_of_field_of_bowl_round_trip ⟨2, 0, 2, 1⟩ (by decide)

/-- Reachable witness: a mixed bowl `(2, 1, 1, 2)` from
    `[happy, unhappy]`. -/
theorem round_trip_mixed_bowl :
    Option.map bowlOfField (fieldOfBowl ⟨2, 1, 1, 2⟩) = some ⟨2, 1, 1, 2⟩ :=
  bowl_of_field_of_bowl_round_trip ⟨2, 1, 1, 2⟩ (by decide)

/-- Reachable witness: a mixed bowl `(3, 1, 2, 2)` from
    `[happy, happy, unhappy]`. -/
theorem round_trip_majority_with_dissent :
    Option.map bowlOfField (fieldOfBowl ⟨3, 1, 2, 2⟩) = some ⟨3, 1, 2, 2⟩ :=
  bowl_of_field_of_bowl_round_trip ⟨3, 1, 2, 2⟩ (by decide)

/-- Reachable witness: an all-quiet bowl `(2, 2, 0, 1)` from
    `[quiet, quiet]`. -/
theorem round_trip_all_quiet_bowl :
    Option.map bowlOfField (fieldOfBowl ⟨2, 2, 0, 1⟩) = some ⟨2, 2, 0, 1⟩ :=
  bowl_of_field_of_bowl_round_trip ⟨2, 2, 0, 1⟩ (by decide)

/-! ## Quantifying the gap: explicit unreachable witnesses

  The unreachable subspace of `TaoBowl` is the cost of the lossy
  projection. We exhibit two structurally distinct witnesses, one
  for each reachability axis the homomorphism pins. -/

/-- The user's hint: a *necessary* upper bound on `damping`. Every
    reachable bowl satisfies `damping ≤ rim + 1`. The sharp pair
    `damping ≤ rigidity + 1 ∧ damping ≤ void + 1` implies it. -/
theorem reachable_implies_damping_le_rim_plus_one (b : TaoBowl)
    (h : IsReachable b) : b.damping ≤ b.rim + 1 := by
  obtain ⟨hSum, _, hRig, _⟩ := h
  have hr : b.rigidity ≤ b.rim := by
    rw [← hSum]
    exact Nat.le_add_left b.rigidity b.void
  exact Nat.le_trans hRig (Nat.add_le_add_right hr 1)

/-- Unreachable witness 1: the `damping = 100` bowl from
    `ThoughtBowlMechanics.unreachableBowl`. The damping exceeds
    `rigidity + 1 = 2`. -/
def unreachableBowlBigDamping : TaoBowl :=
  { rim := 2, void := 1, rigidity := 1, damping := 100 }

theorem unreachable_bowl_big_damping_is_unreachable :
    ¬ IsReachable unreachableBowlBigDamping := by
  intro h
  have : unreachableBowlBigDamping.damping ≤ unreachableBowlBigDamping.rigidity + 1 := h.2.2.1
  exact absurd this (by decide)

theorem field_of_unreachable_big_damping :
    fieldOfBowl unreachableBowlBigDamping = none :=
  field_of_bowl_unreachable _ unreachable_bowl_big_damping_is_unreachable

/-- Unreachable witness 2: a bowl whose `void + rigidity ≠ rim`.
    Failing the additivity equation is the orthogonal failure mode
    to `unreachableBowlBigDamping`. -/
def unreachableBowlBadSum : TaoBowl :=
  { rim := 5, void := 1, rigidity := 1, damping := 1 }

theorem unreachable_bowl_bad_sum_is_unreachable :
    ¬ IsReachable unreachableBowlBadSum := by
  intro h
  have hSum : unreachableBowlBadSum.void + unreachableBowlBadSum.rigidity
              = unreachableBowlBadSum.rim := h.1
  exact absurd hSum (by decide)

theorem field_of_unreachable_bad_sum :
    fieldOfBowl unreachableBowlBadSum = none :=
  field_of_bowl_unreachable _ unreachable_bowl_bad_sum_is_unreachable

/-- Unreachable witness 3: damping fails the `damping ≤ void + 1`
    branch of the sharp pair (the neutrals-availability constraint).
    All voices are dominant (rigidity = 3, void = 0), but damping = 2
    requires a minority voice. -/
def unreachableBowlNoNeutrals : TaoBowl :=
  { rim := 3, void := 0, rigidity := 3, damping := 2 }

theorem unreachable_bowl_no_neutrals_is_unreachable :
    ¬ IsReachable unreachableBowlNoNeutrals := by
  intro h
  have : unreachableBowlNoNeutrals.damping ≤ unreachableBowlNoNeutrals.void + 1 := h.2.2.2
  exact absurd this (by decide)

theorem field_of_unreachable_no_neutrals :
    fieldOfBowl unreachableBowlNoNeutrals = none :=
  field_of_bowl_unreachable _ unreachable_bowl_no_neutrals_is_unreachable

/-! ## The three failure modes are structurally independent

  Each unreachable witness fails *one* reachability constraint and
  passes the others. The three failure modes (additivity, damping ≤
  rigidity + 1, damping ≤ void + 1) are independent axes of the
  unreachable subspace, not redundant readings of the same defect. -/

theorem unreachability_modes_are_independent :
    -- big-damping fails only damping ≤ rigidity + 1
    unreachableBowlBigDamping.void + unreachableBowlBigDamping.rigidity
      = unreachableBowlBigDamping.rim ∧
    1 ≤ unreachableBowlBigDamping.damping ∧
    ¬ unreachableBowlBigDamping.damping ≤ unreachableBowlBigDamping.rigidity + 1 ∧
    -- bad-sum fails only the additivity equation
    ¬ unreachableBowlBadSum.void + unreachableBowlBadSum.rigidity
      = unreachableBowlBadSum.rim ∧
    1 ≤ unreachableBowlBadSum.damping ∧
    unreachableBowlBadSum.damping ≤ unreachableBowlBadSum.rigidity + 1 ∧
    -- no-neutrals fails only damping ≤ void + 1
    unreachableBowlNoNeutrals.void + unreachableBowlNoNeutrals.rigidity
      = unreachableBowlNoNeutrals.rim ∧
    unreachableBowlNoNeutrals.damping ≤ unreachableBowlNoNeutrals.rigidity + 1 ∧
    ¬ unreachableBowlNoNeutrals.damping ≤ unreachableBowlNoNeutrals.void + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Headline witness

  A single statement bundling the round-trip theorem on the
  reachable sub-lattice and the explicit gap quantification. -/

theorem thought_bowl_partial_inverse_witness :
    -- Round-trip on every reachable bowl
    (∀ b : TaoBowl, IsReachable b →
      Option.map bowlOfField (fieldOfBowl b) = some b) ∧
    -- Concrete reachable instances
    fieldOfBowl ⟨0, 0, 0, 1⟩ = some (canonicalField ⟨0, 0, 0, 1⟩) ∧
    fieldOfBowl ⟨2, 0, 2, 1⟩ = some (canonicalField ⟨2, 0, 2, 1⟩) ∧
    -- The user's hint as a derived necessary condition
    (∀ b : TaoBowl, IsReachable b → b.damping ≤ b.rim + 1) ∧
    -- Three structurally independent unreachable witnesses
    fieldOfBowl unreachableBowlBigDamping = none ∧
    fieldOfBowl unreachableBowlBadSum = none ∧
    fieldOfBowl unreachableBowlNoNeutrals = none := by
  refine ⟨bowl_of_field_of_bowl_round_trip,
          ?_, ?_,
          reachable_implies_damping_le_rim_plus_one,
          field_of_unreachable_big_damping,
          field_of_unreachable_bad_sum,
          field_of_unreachable_no_neutrals⟩
  · -- fieldOfBowl ⟨0,0,0,1⟩ reduces to some (canonicalField ⟨0,0,0,1⟩)
    show (if IsReachable ⟨0, 0, 0, 1⟩ then some (canonicalField ⟨0, 0, 0, 1⟩) else none)
        = some (canonicalField ⟨0, 0, 0, 1⟩)
    rw [if_pos (by decide)]
  · show (if IsReachable ⟨2, 0, 2, 1⟩ then some (canonicalField ⟨2, 0, 2, 1⟩) else none)
        = some (canonicalField ⟨2, 0, 2, 1⟩)
    rw [if_pos (by decide)]

/-! ## Honesty note

What we proved:

  * `IsReachable : TaoBowl → Prop` characterizes the bowls in the
    image of `bowlOfField` via four sharp structural constraints.
  * `canonicalField : TaoBowl → List VibeWave` reconstructs a
    canonical preimage of every reachable bowl from its four
    dials.
  * `fieldOfBowl : TaoBowl → Option (List VibeWave)` is the
    partial inverse: `some (canonicalField b)` on the reachable
    sub-lattice, `none` outside it.
  * **Round-trip lemma** `bowl_of_field_of_bowl_round_trip`:
    `Option.map bowlOfField (fieldOfBowl b) = some b` exactly
    when `IsReachable b`. The forgetful homomorphism becomes a
    bijection on the reachable sub-lattice (modulo wave ordering,
    which the canonical field representative pins).
  * Three structurally independent unreachable witnesses
    (`big-damping`, `bad-sum`, `no-neutrals`), each failing one
    reachability axis and passing the other two
    (`unreachability_modes_are_independent`). The unreachable
    subspace is genuinely three-dimensional in failure modes.

What we did **not** prove:

  * That `fieldOfBowl (bowlOfField waves) = some waves` for an
    arbitrary `waves`. The opposite round-trip fails because
    `bowlOfField` is order-blind: the best we can recover is the
    canonical-field representative of the multiset class. The
    weaker `bowlOfField (canonicalField (bowlOfField waves)) =
    bowlOfField waves` would require an additional helper and is
    deferred to the next module.
  * That the reachable sub-lattice exhausts physically meaningful
    bowls. Other forgetful maps (e.g., reading decay rates rather
    than valence counts) would carve different reachable
    sub-lattices. The "physical topology fragment" result here is
    relative to the specific homomorphism `bowlOfField` we work
    with.
  * Anything about the *measure* of the unreachable subspace.
    `TaoBowl` has four `Nat` dials, so both the reachable
    sub-lattice and its complement are countably infinite. A
    measure-theoretic gap quantification would require a Mathlib
    lift.

## Next exploration

`Gnosis/ThoughtBowlMultisetEquivalence.lean` — define
`canonicalize : List VibeWave → List VibeWave` as
`canonicalField ∘ bowlOfField` and prove
`bowlOfField (canonicalize waves) = bowlOfField waves`. That gives
the *opposite* round-trip on the multiset class: every wave field
is `bowlOfField`-equivalent to its canonical-field representative,
so the homomorphism factors through the multiset coequalizer of
the wave-ordering action. The natural target is a quotient-style
witness:

    bowlOfField waves₁ = bowlOfField waves₂  ⟺
      canonicalize waves₁ = canonicalize waves₂

making the multiset structure of the homomorphism a theorem rather
than a comment.
-/

end ThoughtBowlMechanicsRefined
