import Foundation.Crypto.Semantics.Oracle.PacketWriter
import Foundation.Crypto.Semantics.Oracle.SelectedRejection
import Foundation.Constructions.Symmetric.OneTimePad
import Foundation.Examples.OneUseInvocation
import Foundation.Examples.OneUseAdaptiveSecrecy
import Foundation.Crypto.Semantics.Oracle.FirstAcceptance

/-! The real caller first sends an empty malformed request, then overwrites
the returned failure packet with an arbitrary-width valid request. Every
write, move, and rewind is executed by the existing interactive runtime. -/
namespace Foundation.RejectionThenRequestExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {width : Nat} (message : Bits width)

def code : Code := [.call] ++ StraightLine.code (PacketWriter.actions message.toList) ++ [.call, .native .halt]

def initial : Machine.Configuration := { outputTape := RequestExport.packetTape [] [] [] }

def returnedMachine : Machine.Configuration :=
  { (initial : Machine.Configuration).advance with outputTape := ResponseLoading.loaded [false] }

def ready : Machine.Configuration :=
  StraightLine.execute (PacketWriter.actions message.toList) returnedMachine

theorem ready_layout (hWidth : width ≠ 0) : ready message =
    { pc := 3 * width + 2, outputTape := RequestExport.packetTape [] [] message.toList } := by
  unfold ready
  rw [PacketWriter.writes_packet]
  have ht : (returnedMachine.outputTape.right).drop message.toList.length = [] := by
    cases width with
    | zero => exact False.elim (hWidth rfl)
    | succ n => simp [returnedMachine, ResponseLoading.loaded, ResponseLoading.fromCells]
  simp only [Bits.length_toList] at ht ⊢
  rw [ht]
  simp [returnedMachine, initial, ResponseLoading.loaded, ResponseLoading.fromCells,
    Machine.Configuration.advance, Nat.add_assoc]
  omega

theorem ready_active : (ready message).halted = false := by
  unfold ready
  rw [PacketWriter.writes_packet]
  rfl

theorem ready_pc : (ready message).pc = (StraightLine.code (PacketWriter.actions message.toList)).length + 1 := by
  unfold ready
  rw [PacketWriter.writes_packet]
  simp [StraightLine.code, PacketWriter.length, returnedMachine, initial, Machine.Configuration.advance]
  omega

theorem ready_call : (code message)[(ready message).pc]? = some .call := by
  rw [ready_pc]
  simp [code, List.getElem?_append_right]

theorem ready_next : (code message)[(ready message).advance.pc]? = some (.native .halt) := by
  change (code message)[(ready message).pc + 1]? = _
  rw [ready_pc]
  simp [code, List.getElem?_append_right]

variable (native : Machine.Program) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (key : Bits width) (hWidth : width ≠ 0)

def firstCall : SelectedRejection.Call State (code message) width where
  machine := initial
  state := state
  trace := trace
  request := []
  tail := []
  active := rfl
  instruction := by simp [code, initial]
  tape := rfl
  mismatch := hWidth

noncomputable def rejected :=
  (SelectedRejection.reject native oracle key.toList [] (by simp) (firstCall message state trace hWidth)).observe
    (fun _ => ())
    (fun _ _ => .source false (Machine.PairPreparation.operand [] key.toList [])
      (NativeCallback.resumed initial.advance state trace [] [false]))
    (fun _ output h =>
      (SelectedRejection.reject_exit native oracle key.toList [] (by simp)
        (firstCall message state trace hWidth) output h).symm)

noncomputable def writer :=
  StraightLine.procedure native oracle (Machine.PairPreparation.operand [] key.toList [])
    state (([], [false]) :: trace) [.call] [.call, .native .halt]
    (PacketWriter.actions message.toList) returnedMachine (by rfl) (by rfl)

noncomputable def preparation :=
  (rejected message native oracle state trace key hWidth).seq
    (writer message native oracle state trace key) (fun _ _ _ => rfl)
    (fun _ => (PacketWriter.actions message.toList).length) (fun _ _ _ => Nat.le_refl _)

theorem preparation_exit (output : Unit × Unit) :
    (preparation message native oracle state trace key hWidth).exit () output =
      .source false (Machine.PairPreparation.operand [] key.toList [])
        ⟨state, .running (ready message), ([], [false]) :: trace⟩ := rfl

theorem preparation_budget : (preparation message native oracle state trace key hWidth).budget () =
    3 * width + 30 := by
  change (SelectedRejection.reject native oracle key.toList [] (by simp)
    (firstCall message state trace hWidth)).budget () + (PacketWriter.actions message.toList).length = _
  unfold SelectedRejection.reject
  rw [OneUseSource.rejectedInvocation_budget, PacketWriter.length]
  simp [SelectedRejection.input, firstCall, Machine.PreparationCheck.consumed]
  omega

def operands : Machine.PairPreparation.Input :=
  ⟨key.toList, message.toList, [], [], by simp⟩

noncomputable def normal :=
  Procedure.ofFixed (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code (code message) oracle)
    (fun _ : Unit => .source false (Machine.PairPreparation.operand [] key.toList [])
      ⟨state, .running (ready message), ([], [false]) :: trace⟩)
    (fun _ _ : Unit => OneUseInvocationExamples.final (ready message) state (([], [false]) :: trace)
      (operands message key))
    (fun _ => PMF.pure ()) (fun _ => 33 * width + 34)
    (fun _ => by
      have ht : (ready message).outputTape = RequestExport.packetTape [] [] message.toList := by
        rw [ready_layout message hWidth]
      simpa only [operands, Bits.length_toList, PMF.pure_map] using
        OneUseInvocationExamples.run (code message) oracle (ready message) state (([], [false]) :: trace)
          (operands message key) (ready_active message) (ready_call message) ht (ready_next message))

noncomputable def complete :=
  (preparation message Machine.OneTimePad.Prepared.listProcedure.code oracle state trace key hWidth).seq
    ((normal message oracle state trace key hWidth).reindex (fun _ : Unit × Unit => ()))
    (fun _ output _ => (preparation_exit message Machine.OneTimePad.Prepared.listProcedure.code oracle state trace key hWidth output).symm)
    (fun _ => 33 * width + 34) (fun _ _ _ => Nat.le_refl _)

theorem complete_budget : (complete message oracle state trace key hWidth).budget () = 36 * width + 64 := by
  change (preparation message Machine.OneTimePad.Prepared.listProcedure.code oracle state trace key hWidth).budget () +
    (33 * width + 34) = _
  rw [preparation_budget]
  omega

include hWidth in
theorem run :
    TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code (code message) oracle)
      (36 * width + 64) (.source false (Machine.PairPreparation.operand [] key.toList [])
        ⟨state, .running initial, trace⟩) =
      PMF.pure (OneUseInvocationExamples.final (ready message) state (([], [false]) :: trace) (operands message key)) := by
  have h := (complete message oracle state trace key hWidth).final_run ()
    (fun _ _ => by
      simp [complete, Procedure.seq, Procedure.reindex, normal, Procedure.ofFixed, OneUseInvocationExamples.final,
        OneUseSource.step, Reification.timedStep, Reification.terminal, PMF.pure_map])
    (36 * width + 64) (by rw [complete_budget])
  change TimedExecution.eval _ _ (.source false (Machine.PairPreparation.operand [] key.toList [])
    ⟨state, .running initial, trace⟩) =
    ((complete message oracle state trace key hWidth).semantics ()).map
      (Function.const _ (OneUseInvocationExamples.final (ready message) state (([], [false]) :: trace) (operands message key))) at h
  rw [PMF.map_const] at h
  exact h

include hWidth in
theorem first_accepts (result : OneUseSource.Control State × Nat)
    (h : result ∈ ((FirstAcceptance.execution Machine.OneTimePad.Prepared.listProcedure.code (code message) oracle
      (36 * width + 64)).costed
      (.source false (Machine.PairPreparation.operand [] key.toList []) ⟨state, .running initial, trace⟩)).support) :
    OneUseSource.used result.1 = true := by
  apply FirstAcceptance.completes Machine.OneTimePad.Prepared.listProcedure.code (code message) oracle
    (36 * width + 64) _ _ result h
  intro finish hFinish
  rw [run message oracle state trace key hWidth, PMF.mem_support_pure_iff] at hFinish
  subst finish
  rfl

include hWidth in
theorem first_acceptance_witness (result : OneUseSource.Control State × Nat)
    (h : result ∈ ((FirstAcceptance.execution Machine.OneTimePad.Prepared.listProcedure.code (code message) oracle
      (36 * width + 64)).costed
      (.source false (Machine.PairPreparation.operand [] key.toList []) ⟨state, .running initial, trace⟩)).support) :
    ∃ before, before ∈ (TimedExecution.eval
      (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code (code message) oracle) (result.2 - 1)
      (.source false (Machine.PairPreparation.operand [] key.toList []) ⟨state, .running initial, trace⟩)).support ∧
      OneUseSource.used before = false ∧ OneUseSource.accepted before = true ∧
      result.1 ∈ (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code (code message) oracle before).support :=
  FirstAcceptance.acceptance_witness Machine.OneTimePad.Prepared.listProcedure.code (code message) oracle
    (36 * width + 64) _ result rfl (first_accepts message oracle state trace key hWidth result h) h

noncomputable def ciphertext :=
  (uniform (Bits width)).bind (fun key =>
    (TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code (code message) oracle)
      (36 * width + 64) (.source false (Machine.PairPreparation.operand [] key.toList [])
        ⟨state, .running initial, trace⟩)).map OneUseAdaptiveSecrecyExamples.packet)

include hWidth in
theorem ciphertext_uniform : ciphertext message oracle state trace =
    (uniform (Bits width)).map (fun bits => true :: bits.toList) := by
  unfold ciphertext
  simp_rw [run message oracle state trace _ hWidth, PMF.pure_map]
  have he : ∀ key : Bits width,
      OneUseAdaptiveSecrecyExamples.packet
        (OneUseInvocationExamples.final (ready message) state (([], [false]) :: trace) (operands message key)) =
      true :: (Foundation.Symmetric.OneTimePad.encrypt key message).toList := by
    intro key
    simp [OneUseAdaptiveSecrecyExamples.packet, OneUseInvocationExamples.final, operands,
      Machine.Configuration.outputBits, ResponseLoading.loaded, ResponseLoading.fromCells,
      Machine.Tape.bits, Foundation.Symmetric.OneTimePad.encrypt, Machine.OneTimePad.toList_xor]
    exact (Machine.OneTimePad.toList_xor key message).symm.trans
      ((congrArg Bits.toList (Bits.xor_comm key message)).trans (Machine.OneTimePad.toList_xor message key))
  simp_rw [he]
  change (uniform (Bits width)).map (fun key => true :: (Foundation.Symmetric.OneTimePad.encrypt key message).toList) = _
  have h := congrArg (fun distribution => distribution.map (fun bits : Bits width => true :: bits.toList))
    (Foundation.Symmetric.OneTimePad.ciphertext_uniform message)
  simpa only [Foundation.Symmetric.OneTimePad.ciphertext, PMF.map_comp, Function.comp_def] using h

end Foundation.RejectionThenRequestExamples
