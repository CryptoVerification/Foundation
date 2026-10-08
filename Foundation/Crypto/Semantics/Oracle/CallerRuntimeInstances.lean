import Foundation.Crypto.Semantics.Oracle.CallerRuntime
import Foundation.Crypto.Semantics.Oracle.ReusableResponseSource
import Foundation.Crypto.Semantics.Oracle.PacketResponseSource

/-! Both physical response controllers implement the same caller interface.
The generic caller proofs never inspect their component/export machinery. -/
namespace CryptoOracle.Interactive.CallerRuntime
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}

noncomputable def packet (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component) (ready : Component → Option (Saved × List Bool))
    (code : Code) (oracle : BitOracle State) :
    Runtime Saved (PacketResponseSource.Control Component State Saved) code oracle where
  step := PacketResponseSource.step componentStep begin ready code oracle
  embed := PacketResponseSource.Control.source
  boundary := fun outer => match outer with
    | .source _ frame => SourcePrefix.boundary frame
    | _ => true
  embed_boundary := fun _ _ => rfl
  source_step := by
    intro retained frame h
    cases hc : frame.control <;> simp_all [SourcePrefix.boundary, PacketResponseSource.step]
  request := fun retained caller state trace request => .processing caller state trace request (begin retained request)
  request_step := fun _ _ _ _ _ => rfl
  terminal := by
    intro retained frame h
    cases hc : frame.control <;> simp_all [Reification.terminal, PacketResponseSource.step,
      Reification.timedStep, PMF.pure_map]

noncomputable def nativeResponse (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component) (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State) :
    Runtime Saved (ReusableResponseSource.Control Component State Saved) code oracle where
  step := ReusableResponseSource.step componentStep begin ready native code oracle
  embed := ReusableResponseSource.Control.source
  boundary := fun outer => match outer with
    | .source _ frame => SourcePrefix.boundary frame
    | _ => true
  embed_boundary := fun _ _ => rfl
  source_step := by
    intro retained frame h
    cases hc : frame.control <;> simp_all [SourcePrefix.boundary, ReusableResponseSource.step]
  request := fun retained caller state trace request => .processing caller state trace request (begin retained request)
  request_step := fun _ _ _ _ _ => rfl
  terminal := by
    intro retained frame h
    cases hc : frame.control <;> simp_all [Reification.terminal, ReusableResponseSource.step,
      Reification.timedStep, PMF.pure_map]

end CryptoOracle.Interactive.CallerRuntime
