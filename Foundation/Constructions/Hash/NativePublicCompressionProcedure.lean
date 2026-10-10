import Foundation.Constructions.Hash.NativePublicCompression
import Foundation.Constructions.Hash.NativeRuntimeRawPacket

/-! Public compression has an exact first physical return contract and
therefore fits the existing packet service without a supplied realization
witness. The complete actual native frame is retained in every output. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev RuntimeCompressionInput (n κ : Nat) :=
  CompressionTable (Bits κ) (Bits n) × CompressionInput (Bits κ) (Bits n)

variable {n κ : Nat} (prior : List (List Bool × List Bool))

/-- Constant-width capability outputs give an exact first physical return,
including the real raw loader, native call/halt and physical exporter. -/
theorem native_public_compression_first_joint (input : RuntimeCompressionInput n κ) :
    runToBoundary
      (NativePacketLaunch.step NativeCompressionCall.code (idealCompression n κ) false prior)
      (fun control => (runtimeRawReady control).isSome)
      (NativeCompressionCall.rawSteps (n + κ + 1) n)
      (.preparing (encodeCompressionTable input.1) (.loading (compressionPacket input.2) {})) =
    (RandomOracle.oracle input.1 input.2).map (fun answer =>
      (runtimeRawExit (NativeCompressionCall.finish (compressionPacket input.2) prior
          (encodeCompressionTable answer.1, answer.2.toList), answer.2.toList),
        NativeCompressionCall.rawSteps (n + κ + 1) n)) := by
  have before := NativeCompressionCall.raw_export_before_run (idealCompression n κ)
    (encodeCompressionTable input.1) (compressionPacket input.2) prior n
    (fun answer ha => (idealCompression_growth n κ _ _ answer ha).2)
  rw [compressionPacket_length, typed_compression_step, PMF.map_comp] at before
  have after := native_public_compression_run input.1 input.2 prior
  have h := runToBoundary_joint_of_adjacent
    (NativePacketLaunch.step NativeCompressionCall.code (idealCompression n κ) false prior)
    (fun control => (runtimeRawReady control).isSome)
    (.preparing (encodeCompressionTable input.1) (.loading (compressionPacket input.2) {}))
    (NativeCompressionCall.rawSteps (n + κ + 1) n - 1)
    (runtimeRawReady_absorbing _ _ prior)
    (by intro control support
        rw [before, PMF.mem_support_map_iff] at support
        obtain ⟨answer, _, rfl⟩ := support
        rfl)
    (by intro control support
        rw [show NativeCompressionCall.rawSteps (n + κ + 1) n - 1 + 1 =
          NativeCompressionCall.rawSteps (n + κ + 1) n by unfold NativeCompressionCall.rawSteps; omega,
          after, PMF.mem_support_map_iff] at support
        obtain ⟨answer, _, rfl⟩ := support
        rfl)
  simpa only [show NativeCompressionCall.rawSteps (n + κ + 1) n - 1 + 1 =
      NativeCompressionCall.rawSteps (n + κ + 1) n by unfold NativeCompressionCall.rawSteps; omega,
    after, PMF.map_comp, Function.comp_def, runtimeRawExit] using h

noncomputable def publicCompressionPacketProcedure :=
  Procedure.ofFixed
    (NativePacketLaunch.step NativeCompressionCall.code (idealCompression n κ) false prior)
    (fun input : RuntimeCompressionInput n κ => NativePacketLaunch.Control.preparing
      (encodeCompressionTable input.1) (.loading (compressionPacket input.2) {}))
    (fun _ output => runtimeRawExit output)
    (fun input => (RandomOracle.oracle input.1 input.2).map (fun answer =>
      (NativeCompressionCall.finish (compressionPacket input.2) prior
        (encodeCompressionTable answer.1, answer.2.toList), answer.2.toList)))
    (fun _ => NativeCompressionCall.rawSteps (n + κ + 1) n)
    (fun input => by
      rw [native_public_compression_run, PMF.map_comp]
      rfl)

theorem publicCompressionPacketProcedure_operational :
    Procedure.Operational (publicCompressionPacketProcedure (n := n) (κ := κ) prior) := by
  apply Procedure.operational_ofFixed

noncomputable def publicCompressionPacketHandler (input : RuntimeCompressionInput n κ) :
    PacketResponseService.Handler
      (NativePacketLaunch.step NativeCompressionCall.code (idealCompression n κ) false prior)
      runtimeRawReady where
  execution := (publicCompressionPacketProcedure prior).reindex (fun _ : Unit => input)
  ready_exit _ := rfl
  read := runtimeRawRead
  read_exit _ := rfl
  responseCap := n
  response_bound := by
    intro output support
    change output ∈ ((RandomOracle.oracle input.1 input.2).map _).support at support
    rw [PMF.mem_support_map_iff] at support
    obtain ⟨answer, _, rfl⟩ := support
    simp

theorem publicCompressionPacketHandler_exact (input : RuntimeCompressionInput n κ) :
    (publicCompressionPacketHandler prior input).ExactFirstReady := by
  change (runToBoundary _ (fun control => (runtimeRawReady control).isSome)
    (NativeCompressionCall.rawSteps (n + κ + 1) n)
    (.preparing (encodeCompressionTable input.1) (.loading (compressionPacket input.2) {}))).map
      (fun result => (runtimeRawRead result.1, result.2)) = _
  rw [native_public_compression_first_joint, PMF.map_comp]
  simp only [publicCompressionPacketHandler, publicCompressionPacketProcedure, Procedure.reindex,
    TimedExecution.Procedure.ofFixed, PMF.map_comp, Function.comp_def, runtimeRawRead, runtimeRawExit,
    NativePacketComponent.read]

end Foundation.Hash.Native
