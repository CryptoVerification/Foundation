import Foundation.Crypto.Semantics.Oracle.ComponentResponseCallback
import Foundation.Crypto.Semantics.Oracle.PrivateControllerEncoding

/-! Faithful callback representations. The fixed suspended caller, state,
request and history are encoded even when an active caller copy is present. -/
namespace CryptoOracle.Interactive.ComponentResponseEncoding
open Machine Foundation.Probability
universe u v w
variable {Component : Type u} {State : Type v} {Saved : Type w}

def fields (C : FiniteBitEncoding Component) (E : FiniteBitEncoding State) (R : FiniteBitEncoding Saved) :=
  C.sum ((PrivateControllerEncoding.callback E).prod R)

def control (C : FiniteBitEncoding Component) (E : FiniteBitEncoding State) (R : FiniteBitEncoding Saved) :
    FiniteBitEncoding (ComponentResponseCallback.Control Component State Saved) where
  encode := fun c => (fields C E R).encode (match c with
    | .processing component => .inl component
    | .delivering frame => .inr frame)
  decode := fun raw => ((fields C E R).decode raw).map fun f => match f with
    | .inl component => .processing component
    | .inr frame => .delivering frame
  decode_encode := by intro c; cases c <;> simp [(fields C E R).decode_encode]

abbrev Runtime (Component : Type u) (State : Type v) (Saved : Type w) :=
  Configuration State × (List Bool × ComponentResponseCallback.Control Component State Saved)

def runtime (C : FiniteBitEncoding Component) (E : FiniteBitEncoding State) (R : FiniteBitEncoding Saved) :
    FiniteBitEncoding (Runtime Component State Saved) :=
  (ConfigurationEncoding.frame E).prod (ConfigurationEncoding.bits.prod (control C E R))

def frame (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (c : ComponentResponseCallback.Control Component State Saved) : Runtime Component State Saved :=
  (⟨state, .running caller, trace⟩, request, c)

end CryptoOracle.Interactive.ComponentResponseEncoding
