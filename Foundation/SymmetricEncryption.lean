import Mathlib.Algebra.Group.Defs

/-- Simple record for deterministic symmetric-key encryption. -/
structure SymmetricEncryption (Key Msg Ciph : Type _) where
  enc : Key → Msg → Ciph
  dec : Key → Ciph → Msg
  correct : ∀ k m, dec k (enc k m) = m

namespace SymmetricEncryption

variable {Key Msg Ciph : Type _}

-- Common-key specific lemmas would live in this namespace.

end SymmetricEncryption
