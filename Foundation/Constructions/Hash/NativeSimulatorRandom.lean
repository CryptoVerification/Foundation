import Foundation.Constructions.Hash.OracleWorlds
import Foundation.Crypto.Semantics.Oracle.NativeUniformPacketResources

/-! The local-randomness branch of the already fixed compression simulator
is realized by the existing constant native one-time-pad sampler and actual
physical response export. Recognition, table lookup and remembering an entry
are not implemented by this component. The final theorem's table update is
explicitly a mathematical observation, not an executed memory operation. -/
namespace Foundation.Hash.Native.SimulatorRandom
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false

/-- Logical observation of the packet already physically returned. This is
not a CPU decoder and is not charged as native code. -/
def decode (n : Nat) (packet : List Bool) : Bits n :=
  fun index => packet[index.val]?.getD false

@[simp] theorem decode_bits {n : Nat} (bits : Bits n) : decode n bits.toList = bits := by
  funext index
  simp [decode, Bits.toList]

noncomputable def execution {State : Type} (n : Nat) (state : State)
    (prior : List (List Bool × List Bool)) :=
  TimedExecution.eval (NativePacketComponent.step NativeUniformPacket.code NativeUniformPacket.silentOracle)
    (8 * n + 7) (.computing (NativeUniformPacket.start n state prior))

/-- The full physical packet execution realizes precisely the original
simulator backend's local draw, preserving its hidden ideal state. -/
theorem backend_packet {n κ : Nat} {State : Type}
    (ideal : Oracle (List (Bits κ)) (Bits n) State) (state : State)
    (prior : List (List Bool × List Bool)) :
    (execution n state prior).map (fun control =>
      let output := NativePacketComponent.read control
      (output.1.state, decode n output.2)) =
    simulatorBackend ideal state (.inr ()) := by
  rw [execution, NativeUniformPacket.packet_run, PMF.map_comp]
  simp only [Function.comp_def, NativePacketComponent.read, NativeUniformPacket.finish, NativeCode.frame,
    decode_bits, simulatorBackend]

/-- The same native run preserves every prior transcript event jointly
with the sampled response; it creates no ideal-hash query event. -/
theorem packet_history {n : Nat} {State : Type} (state : State)
    (prior : List (List Bool × List Bool)) :
    (execution n state prior).map (fun control =>
      let output := NativePacketComponent.read control
      (output.1.state, output.1.reverseTrace, decode n output.2)) =
    (uniform (Bits n)).map (fun bits => (state, prior, bits)) := by
  rw [execution, NativeUniformPacket.packet_run, PMF.map_comp]
  simp only [Function.comp_def, NativePacketComponent.read, NativeUniformPacket.finish, NativeCode.frame, decode_bits]

/-- Connection to the actual fixed simulator, only after its existing
lookup and recognizer select the local-draw branch. Remembering the entry
here is a logical observation; its native implementation remains separate. -/
theorem fresh_branch_observation {n κ : Nat} {State : Type}
    (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (input : CompressionInput (Bits κ) (Bits n))
    (prior : List (List Bool × List Bool))
    (fresh : table.lookup input = none)
    (unrecognized : terminalMessage initial terminal table input = none) :
    (execution n state prior).map (fun control =>
      let output := NativePacketComponent.read control
      let bits := decode n output.2
      (((input, bits) :: table, output.1.state), bits)) =
    compressionSimulator ideal initial terminal (table, state) input := by
  rw [compressionSimulator_terminal_eq, fresh, unrecognized]
  rw [execution, NativeUniformPacket.packet_run, PMF.map_comp]
  simp only [Function.comp_def, NativePacketComponent.read, NativeUniformPacket.finish, NativeCode.frame, decode_bits]

end Foundation.Hash.Native.SimulatorRandom
