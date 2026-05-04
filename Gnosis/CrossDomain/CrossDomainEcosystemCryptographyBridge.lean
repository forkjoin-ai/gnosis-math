namespace Gnosis

structure EcosystemCryptography where
  encryptionStrength : Nat
  speciesCount : Nat

theorem ecosystem_cryptography_bridges (e : EcosystemCryptography) (h1 : e.encryptionStrength > 0) (h2 : e.speciesCount > 0) : e.encryptionStrength + e.speciesCount > 1 :=
  Nat.lt_of_lt_of_le
    (Nat.lt_add_of_pos_right h2 : 1 < 1 + e.speciesCount)
    (Nat.add_le_add_right h1 e.speciesCount)

end Gnosis