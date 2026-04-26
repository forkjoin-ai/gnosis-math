import Init

namespace Gnosis

class BuleFintype (α : Type _) where
  all : List α
  complete : ∀ x : α, x ∈ all

def Finset.sum {α : Type _} [BuleFintype α] [Add β] [Zero β] (f : α → β) : β :=
  BuleFintype.all.foldl (fun acc x => acc + f x) 0

class BuleMeasurableSpace (α : Type _) where
  measurableSets : α → Prop -- Structural placeholder

def BuleMeasurable {α β : Type _} [BuleMeasurableSpace α] [BuleMeasurableSpace β] (_f : α → β) : Prop :=
  True -- Structural placeholder

namespace Tactics
-- Re-export for convenience
export BuleFintype (all)
def BuleSup {α : Type _} (f : Nat → α) : α :=
  -- Structural placeholder for the supremum in a discrete space
  f 0 -- Minimal implementation

theorem BuleSup_add {α : Type _} [Add α] {f g : Nat → α} :
    BuleSup (fun n => f n + g n) = BuleSup f + BuleSup g := by
  simp [BuleSup]

structure BuleFinset (α : Type _) where
  val : List α

namespace BuleFinset

def mem {α : Type _} (x : α) (s : BuleFinset α) : Prop :=
  x ∈ s.val

instance {α : Type _} : Membership α (BuleFinset α) where
  mem s x := mem x s

def card {α : Type _} (s : BuleFinset α) : Nat :=
  s.val.length

def intersection {α : Type _} [DecidableEq α] (s t : BuleFinset α) : BuleFinset α :=
  ⟨s.val.filter (fun x => x ∈ t.val)⟩

instance {α : Type _} [DecidableEq α] : Inter (BuleFinset α) where
  inter := intersection

def Nonempty {α : Type _} (s : BuleFinset α) : Prop :=
  s.val ≠ []

def sup {α : Type _} [Max α] [Zero α] (s : BuleFinset Nat) (f : Nat → α) : α :=
  s.val.foldl (fun acc x => max acc (f x)) 0

end BuleFinset

end Tactics

end Gnosis
