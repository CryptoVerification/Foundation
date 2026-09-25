/-- The syntax of a public-key encryption scheme with an abstract computation type. -/
structure PKE (M : Type → Type) where
  PublicKey : Type
  SecretKey : Type
  Message : Type
  Ciphertext : Type
  keygen : M (PublicKey × SecretKey)
  encrypt : PublicKey → Message → M Ciphertext
  decrypt : SecretKey → Ciphertext → Option Message
