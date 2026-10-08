import Foundation.Crypto.Semantics.Oracle.ReusableResponseSource
import Foundation.Crypto.Semantics.Oracle.PrivateControllerEncoding

/-! Faithful repeated-request controller encodings. Saved callers, private
stores, requests, opaque states and each transcript copy remain runtime data. -/
namespace CryptoOracle.Interactive.ReusableResponseEncoding
open Machine Foundation.Probability
universe u v w
variable {Component : Type u} {State : Type v} {Saved : Type w}

def metadata (E : FiniteBitEncoding State) {Payload : Type*} (P : FiniteBitEncoding Payload) :=
  Machine.ConfigurationEncoding.configuration.prod
    (E.prod (ConfigurationEncoding.trace.prod (ConfigurationEncoding.bits.prod P)))

def fields (C : FiniteBitEncoding Component) (E : FiniteBitEncoding State) (R : FiniteBitEncoding Saved) :=
  (R.prod (ConfigurationEncoding.frame E)).sum
    ((metadata E C).sum (metadata E ((PrivateControllerEncoding.callback E).prod R)))

def control (C : FiniteBitEncoding Component) (E : FiniteBitEncoding State) (R : FiniteBitEncoding Saved) :
    FiniteBitEncoding (ReusableResponseSource.Control Component State Saved) where
  encode := fun c => (fields C E R).encode (match c with
    | .source retained frame => .inl (retained, frame)
    | .processing caller state trace request component => .inr (.inl (caller, state, trace, request, component))
    | .calling caller state trace request callback retained => .inr (.inr (caller, state, trace, request, callback, retained)))
  decode := fun raw => ((fields C E R).decode raw).map fun f => match f with
    | .inl (retained, frame) => .source retained frame
    | .inr (.inl (caller, state, trace, request, component)) => .processing caller state trace request component
    | .inr (.inr (caller, state, trace, request, callback, retained)) => .calling caller state trace request callback retained
  decode_encode := by intro c; cases c <;> simp [(fields C E R).decode_encode]

end CryptoOracle.Interactive.ReusableResponseEncoding
