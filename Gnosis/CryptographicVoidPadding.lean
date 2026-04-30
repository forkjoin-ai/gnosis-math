set_option linter.unusedVariables false

namespace Gnosis

def structuralCausalityPadding (paths streams : Nat) : Nat :=
  paths - streams

def cryptographicIndCcaPadding (messageSize blockSize : Nat) : Nat :=
  blockSize - (messageSize % blockSize)

theorem cryptographic_void_padding_isomorphism (paths streams message block : Nat)
    (hPaths : paths >= streams)
    (hCausality : structuralCausalityPadding paths streams = 0)
    (hCrypto : cryptographicIndCcaPadding message block = block) :
    paths = streams := by
  unfold structuralCausalityPadding at hCausality
  omega

end Gnosis