import Foundation.Crypto.Semantics.Oracle.ReusableResponseInitialization
import Foundation.Crypto.Semantics.Oracle.ReusableResponseEncoding

/-! Faithful initialization/alignment/repeated-request encodings. The frozen
original caller is included in every encoded runtime, even after activation. -/
namespace CryptoOracle.Interactive.ReusableInitializationEncoding
open Machine Foundation.Probability
universe u v
variable {Component : Type u} {State : Type v}

def fields (C : FiniteBitEncoding Component) (E : FiniteBitEncoding State) :=
  ControllerEncoding.initialization.sum
    (Machine.ConfigurationEncoding.tape.sum
      (ReusableResponseEncoding.control C E Machine.ConfigurationEncoding.tape))

def control (C : FiniteBitEncoding Component) (E : FiniteBitEncoding State) :
    FiniteBitEncoding (ReusableResponseInitialization.Control Component State) where
  encode := fun c => (fields C E).encode (match c with
    | .initializing component => .inl component
    | .aligning tape => .inr (.inl tape)
    | .active source => .inr (.inr source))
  decode := fun raw => ((fields C E).decode raw).map (fun c => match c with
    | .inl component => .initializing component
    | .inr (.inl tape) => .aligning tape
    | .inr (.inr source) => .active source)
  decode_encode := by intro c; cases c <;> simp [(fields C E).decode_encode]

def runtime (C : FiniteBitEncoding Component) (E : FiniteBitEncoding State) :=
  (ConfigurationEncoding.frame E).prod (control C E)

end CryptoOracle.Interactive.ReusableInitializationEncoding
