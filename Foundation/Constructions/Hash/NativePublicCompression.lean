import Foundation.Constructions.Hash.NativeTypedCompression
import Foundation.Crypto.Semantics.Oracle.NativeCompressionCall

/-! The public compression window physically loads its raw packet, invokes
exactly the same ideal capability used by native hashing, and exports the
response. Typed requests are proof-side entry conditions, not a host decoder. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false

/-- All physical tapes, shared table and prior history are retained. The
returned packet is obtained by executing the exporter on the response tape. -/
theorem native_public_compression_run {n κ : Nat}
    (table : CompressionTable (Bits κ) (Bits n)) (input : CompressionInput (Bits κ) (Bits n))
    (prior : List (List Bool × List Bool)) :
    TimedExecution.eval
      (NativePacketLaunch.step NativeCompressionCall.code (idealCompression n κ) false prior)
      (NativeCompressionCall.rawSteps (n + κ + 1) n)
      (.preparing (encodeCompressionTable table) (.loading (compressionPacket input) {})) =
    (RandomOracle.oracle table input).map (fun answer =>
      .running (.exporting
        (NativeCompressionCall.finish (compressionPacket input) prior
          (encodeCompressionTable answer.1, answer.2.toList))
        (.returned answer.2.toList))) := by
  have run := NativeCompressionCall.raw_export_run (idealCompression n κ)
    (encodeCompressionTable table) (compressionPacket input) prior n
    (fun answer ha => (idealCompression_growth n κ _ _ answer ha).2)
  rw [compressionPacket_length, typed_compression_step, PMF.map_comp] at run
  exact run

end Foundation.Hash.Native
