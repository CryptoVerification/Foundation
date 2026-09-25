/-- The syntax of a digital signature scheme with an abstract computation type. -/
structure SignatureScheme (M : Type → Type) where
  PublicKey : Type
  SecretKey : Type
  Message : Type
  Signature : Type
  keygen : M (PublicKey × SecretKey)
  sign : SecretKey → Message → M Signature
  verify : PublicKey → Message → Signature → Bool
