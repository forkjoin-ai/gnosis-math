import Init

/-!
# Cayley's Formula at Small `n`: `#{labeled trees on n vertices} = n^(n-2)`

This module witnesses Cayley's counting identity at small `n` via the
**Prüfer sequence bijection**: labeled trees on the vertex set
`{0, 1, …, n − 1}` are in bijection with length-`(n − 2)` sequences
drawn from that same vertex set. The count is therefore immediate:

    #{labeled trees on n} = #{Prüfer sequences of length (n − 2) over n} = n^(n − 2).

We do **not** prove the Prüfer bijection structurally. We enumerate
Prüfer sequences, count them, and check that the count agrees with
`natPow n (n − 2)` for `n ∈ {2, 3, 4, 5}`. For `n = 3` and `n = 4`
we cross-check by directly enumerating spanning trees of the
complete graph `K_n`: every subset of edges of `K_n` that is
acyclic and has exactly `n − 1` edges is a spanning tree of `K_n`
(connectedness follows from these two constraints on `n − 1`
vertices without cycles).

## Encoding

* A Prüfer sequence is a `List Nat`.
* `allSeqs len alphabetSize` enumerates every length-`len` list with
  entries in `{0, 1, …, alphabetSize − 1}`.
* `pruferSequences n = allSeqs (n − 2) n`.
* An edge of `K_n` is a pair `(i, j)` with `i < j < n`.
* A spanning tree of `K_n` is an edge subset of size `n − 1` that
  is acyclic on `{0, …, n − 1}`. Acyclicity is witnessed by a
  union-find pass: inserting edges one at a time, no edge may
  unify two already-unified endpoints.

Prüfer counts close under kernel `decide` up to `n = 6` with
`maxRecDepth 8192`; the direct spanning-tree enumeration is
included for `n = 3` and `n = 4` only (powerset blows up at
`K_5`: `2^10 = 1024` candidates).

## Hard constraints

No `sorry`, no new `axiom`. `Init` only. Kernel `decide` throughout.
`maxRecDepth` raised for the larger counts.

## Honest scope

This file witnesses Cayley's formula **pointwise at small `n`**. It
does not prove the general theorem `∀ n, #trees(n) = n^(n − 2)`,
does not prove the Prüfer bijection structurally, and does not
connect to the matrix-tree theorem. The Prüfer-side and
spanning-tree-side counts agree by kernel computation at the
enumerated `n`; that is the whole claim.
-/

namespace Gnosis
namespace CayleyTreeFormula

/-! ## Natural-number power -/

/-- `natPow b e = b ^ e` as a recursive `Nat → Nat → Nat`. -/
def natPow : Nat → Nat → Nat
  | _, 0     => 1
  | b, e + 1 => b * natPow b e

/-- Sanity table for `natPow`. -/
theorem natPow_table :
    natPow 2 0 = 1   ∧ natPow 3 1 = 3   ∧
    natPow 4 2 = 16  ∧ natPow 5 3 = 125 ∧
    natPow 6 4 = 1296 := by decide

/-! ## Prüfer-sequence enumeration -/

/-- `range n = [0, 1, …, n − 1]`. -/
def range : Nat → List Nat
  | 0     => []
  | n + 1 => range n ++ [n]

theorem range_length : ∀ n, (range n).length = n
  | 0     => rfl
  | n + 1 => by
      simp [range, List.length_append, range_length n]

/-- All length-`len` sequences over the alphabet `{0, …, alphabetSize − 1}`.
Built by prepending each symbol to every length-`(len − 1)` tail. -/
def allSeqs : Nat → Nat → List (List Nat)
  | 0,       _            => [[]]
  | _ + 1,   0            => []
  | len + 1, alphabetSize =>
      (range alphabetSize).flatMap fun head =>
        (allSeqs len alphabetSize).map (fun tail => head :: tail)

/-- `pruferSequences n` enumerates all Prüfer sequences on `n`
vertices, i.e., every length-`(n − 2)` list with entries in
`{0, …, n − 1}`. For `n ≤ 1` the length `n − 2` computes to `0`
under `Nat` subtraction, giving the single empty sequence. -/
def pruferSequences (n : Nat) : List (List Nat) :=
  allSeqs (n - 2) n

/-! ## Prüfer counts at small `n` -/

/-- For `n = 2`: one Prüfer sequence (the empty list). -/
theorem pruferCount_2 : (pruferSequences 2).length = 1 := by decide

/-- For `n = 3`: three Prüfer sequences, matching `3 = 3^1`. -/
theorem pruferCount_3 : (pruferSequences 3).length = 3 := by decide

/-- For `n = 4`: sixteen Prüfer sequences, matching `16 = 4^2`. -/
theorem pruferCount_4 : (pruferSequences 4).length = 16 := by decide

set_option maxRecDepth 4096 in
/-- For `n = 5`: one hundred twenty-five Prüfer sequences,
matching `125 = 5^3`. -/
theorem pruferCount_5 : (pruferSequences 5).length = 125 := by decide

set_option maxRecDepth 8192 in
/-- For `n = 6`: one thousand two hundred ninety-six Prüfer
sequences, matching `1296 = 6^4`. -/
theorem pruferCount_6 : (pruferSequences 6).length = 1296 := by decide

/-! ## Cayley identity at small `n`: Prüfer count `= n^(n − 2)` -/

/-- **Cayley at `n = 2`**: `#Prüfer(2) = 2^0 = 1`. -/
theorem cayley_prufer_2 :
    (pruferSequences 2).length = natPow 2 (2 - 2) := by decide

/-- **Cayley at `n = 3`**: `#Prüfer(3) = 3^1 = 3`. -/
theorem cayley_prufer_3 :
    (pruferSequences 3).length = natPow 3 (3 - 2) := by decide

/-- **Cayley at `n = 4`**: `#Prüfer(4) = 4^2 = 16`. -/
theorem cayley_prufer_4 :
    (pruferSequences 4).length = natPow 4 (4 - 2) := by decide

set_option maxRecDepth 4096 in
/-- **Cayley at `n = 5`**: `#Prüfer(5) = 5^3 = 125`. -/
theorem cayley_prufer_5 :
    (pruferSequences 5).length = natPow 5 (5 - 2) := by decide

set_option maxRecDepth 8192 in
/-- **Cayley at `n = 6`**: `#Prüfer(6) = 6^4 = 1296`. -/
theorem cayley_prufer_6 :
    (pruferSequences 6).length = natPow 6 (6 - 2) := by decide

/-! ## Direct spanning-tree enumeration on `K_3` and `K_4`

A spanning tree of `K_n` is an edge subset of size `n − 1` that
is acyclic on `{0, …, n − 1}`. For `n = 3` and `n = 4` we
enumerate every edge subset and filter on those two constraints.
Connectedness is implied: an acyclic edge set of size `n − 1` on
`n` vertices is a spanning tree of the vertex set.
-/

/-- Edge: unordered pair `(i, j)` stored with `i < j`. -/
abbrev Edge := Nat × Nat

/-- Edges of `K_n`: all pairs `(i, j)` with `i < j < n`. Built by
recursion on `n`, appending the `n − 1` new edges `(k, n − 1)`
for `k < n − 1` to `edgesOfK (n − 1)`. -/
def edgesOfK : Nat → List Edge
  | 0     => []
  | n + 1 => edgesOfK n ++ (range n).map (fun k => (k, n))

/-- Size: `C(n, 2) = n · (n − 1) / 2`. Witnessed by `decide` at
the small `n` we use. -/
theorem edgesOfK_3_length : (edgesOfK 3).length = 3 := by decide
theorem edgesOfK_4_length : (edgesOfK 4).length = 6 := by decide

/-! ### Powerset over a list -/

/-- Every subset of a list, as a list of lists. `powerset [a, b]`
returns `[[], [b], [a], [a, b]]` (order is implementation-specific;
only membership and length matter downstream). -/
def powerset {α} : List α → List (List α)
  | []      => [[]]
  | x :: xs =>
      let rest := powerset xs
      rest ++ rest.map (fun s => x :: s)

theorem powerset_nil_length {α} : (@powerset α []).length = 1 := rfl

theorem powerset_K3_length : (powerset (edgesOfK 3)).length = 8 := by decide
theorem powerset_K4_length : (powerset (edgesOfK 4)).length = 64 := by decide

/-! ### Union-find style acyclicity check

Represent a partition of `{0, …, n − 1}` as a list of parent
pointers, one per vertex, where `parent[i]` is any representative
of the component of `i`. We use a simplified flat array: after
each union, we rewrite every occurrence of the old root to the
new root. This is `O(n · m)` but fine at `n ≤ 4`.
-/

/-- Initial partition: each vertex is its own component. -/
def initParents (n : Nat) : List Nat := range n

/-- `listGet xs i default` returns `xs[i]` or `default` if out of range. -/
def listGet : List Nat → Nat → Nat → Nat
  | [],      _,     d => d
  | x :: _,  0,     _ => x
  | _ :: xs, i + 1, d => listGet xs i d

/-- `listSetAll xs oldRoot newRoot` replaces every entry equal to
`oldRoot` with `newRoot`. -/
def listSetAll : List Nat → Nat → Nat → List Nat
  | [],      _, _ => []
  | x :: xs, o, n =>
      (if x = o then n else x) :: listSetAll xs o n

/-- Attempt to insert an edge into the partition. Returns
`some parents'` on success (endpoints were in different components)
or `none` on failure (endpoints already share a component, so this
edge would create a cycle). -/
def tryUnion (parents : List Nat) (e : Edge) : Option (List Nat) :=
  let ra := listGet parents e.1 0
  let rb := listGet parents e.2 0
  if ra = rb then none else some (listSetAll parents ra rb)

/-- Fold over an edge list, carrying an `Option (List Nat)` state.
Returns `none` if any union fails (cycle detected). -/
def acyclicFold : List Edge → Option (List Nat) → Option (List Nat)
  | [],      acc      => acc
  | _ :: _,  none     => none
  | e :: es, some p   => acyclicFold es (tryUnion p e)

/-- Edge set is acyclic on `n` vertices iff running the union-find
fold from the trivial partition never detects a cycle. -/
def isAcyclic (n : Nat) (es : List Edge) : Bool :=
  match acyclicFold es (some (initParents n)) with
  | some _ => true
  | none   => false

/-- Spanning-tree predicate: `n − 1` edges, acyclic on `n` vertices. -/
def isSpanningTree (n : Nat) (es : List Edge) : Bool :=
  es.length = n - 1 ∧ isAcyclic n es

/-- All spanning trees of `K_n`, obtained by filtering the powerset
of edges. -/
def spanningTreesOfK (n : Nat) : List (List Edge) :=
  (powerset (edgesOfK n)).filter (isSpanningTree n)

/-! ### Counts -/

/-- **`K_3` has 3 spanning trees.** Matches `3 = natPow 3 1`. -/
theorem spanningTrees_K3_count : (spanningTreesOfK 3).length = 3 := by decide

set_option maxRecDepth 4096 in
/-- **`K_4` has 16 spanning trees.** Matches `16 = natPow 4 2`. -/
theorem spanningTrees_K4_count : (spanningTreesOfK 4).length = 16 := by decide

/-! ## Cross-check: Prüfer count agrees with spanning-tree count -/

/-- **Cayley at `n = 3`, two ways**: Prüfer enumeration and direct
spanning-tree enumeration both give `3`. -/
theorem cayley_k3_crosscheck :
    (pruferSequences 3).length = (spanningTreesOfK 3).length := by decide

set_option maxRecDepth 4096 in
/-- **Cayley at `n = 4`, two ways**: Prüfer enumeration and direct
spanning-tree enumeration both give `16`. -/
theorem cayley_k4_crosscheck :
    (pruferSequences 4).length = (spanningTreesOfK 4).length := by decide

/-! ## Summary bundle -/

set_option maxRecDepth 8192 in
/-- **Cayley at small `n`**: the Prüfer count matches `n^(n − 2)`
for every `n ∈ {2, 3, 4, 5, 6}`, and the spanning-tree count on
`K_3` and `K_4` agrees with the Prüfer count at those `n`. -/
theorem cayley_small_n :
    (pruferSequences 2).length = natPow 2 (2 - 2) ∧
    (pruferSequences 3).length = natPow 3 (3 - 2) ∧
    (pruferSequences 4).length = natPow 4 (4 - 2) ∧
    (pruferSequences 5).length = natPow 5 (5 - 2) ∧
    (pruferSequences 6).length = natPow 6 (6 - 2) ∧
    (spanningTreesOfK 3).length = natPow 3 (3 - 2) ∧
    (spanningTreesOfK 4).length = natPow 4 (4 - 2) := by decide

end CayleyTreeFormula
end Gnosis
