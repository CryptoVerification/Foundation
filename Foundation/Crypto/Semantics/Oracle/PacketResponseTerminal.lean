import Foundation.Crypto.Semantics.Oracle.PacketResponseSource

/-! Genuine caller termination for a packet-service runtime. A halted
private component is not a halted caller. -/
namespace CryptoOracle.Interactive.PacketResponseSource
open Foundation.Probability TimedExecution
universe u v w
variable {Component : Type u} {State : Type v} {Saved : Type w}

def terminal : Control Component State Saved → Bool
  | .source _ frame => Reification.terminal frame.control
  | _ => false

theorem terminal_absorbing (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component) (ready : Component → Option (Saved × List Bool))
    (code : Code) (oracle : BitOracle State) (control : Control Component State Saved)
    (h : terminal control = true) :
    step componentStep begin ready code oracle control = PMF.pure control := by
  cases control with
  | processing => simp [terminal] at h
  | returning => simp [terminal] at h
  | source retained frame =>
      rcases frame with ⟨state, control, trace⟩
      cases control <;>
        simp_all [terminal, Reification.terminal, step, Reification.timedStep, PMF.pure_map]

end CryptoOracle.Interactive.PacketResponseSource
