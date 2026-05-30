import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Noam Chomsky: The Recursive Mind Witness.
Philadelphia / MIT, 1957 (Syntactic Structures).

Contrarian Take: Language is not a "learned behavior." It is a "Hardware
Invariant." Universal Grammar (UG) is the generative kernel of the mind
that produces the infinite surface variables of language from a finite set
of recursive operators. The "Deep Structure" is the constant; the "Surface
Structure" is the ephemeral residue of the environment.

Invariant: Language has a recursive, biological kernel.
Gap: The "Behaviorist" trap—assuming the mind is a blank slate (tabula rasa)
that merely records input frequencies.
Projection: Buley Topological Turing Machine (Gnosis.BuleyTopologicalTuringMachine).
-/

inductive GrammarStructure where
  | deep    : GrammarStructure -- The Invariant
  | surface : GrammarStructure -- The Variable
  deriving DecidableEq

def generativeComplexity (gs : GrammarStructure) : Nat :=
  match gs with
  | .deep    => 1 -- The kernel (O(1))
  | .surface => 100 -- The generated variety (O(N))

/--
Anti-Theory Witness: The kernel (Deep Structure) is strictly simpler
than the generated surface variety.
-/
theorem grammar_kernel_simplicity :
    generativeComplexity .deep < generativeComplexity .surface := by
  unfold generativeComplexity
  exact (by decide)

end Gnosis.Witnesses.History
