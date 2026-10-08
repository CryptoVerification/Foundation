import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMask
import Foundation.Crypto.Semantics.Oracle.ReusableProjectedInitialization

/-! Generated block masking with internal native results separate from the
exported mask. Seeds/scratch data remain part of physical native generation;
only the existing ownership-transfer operation discards that machine. The
key projection need not be injective or reconstruct the internal result. -/
namespace Foundation.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ResponseHandoffProgram
open Foundation.Examples
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} {Result : Type w} {width : Nat}
    (P : Machine.Procedure Input Result) (key : Result → Bits width)
    (hHalt : ∀ input result, (P.execution.exit input result).halted = true)
    (hTape : ∀ input result, (P.execution.exit input result).outputTape = ResponseExport.endTape (key result).toList)
    (read : Input → Machine.Configuration → Result)
    (hRead : ∀ input result, read input (P.execution.exit input result) = result)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool)) (message : Bits width)

noncomputable abbrev step := ReusableResponseInitialization.step ReusableBlockPad.componentStep
  ReusableResponse.begin ReusableBlockPad.ready P.code FlaggedBlockXor.code ReusableBlockPad.code oracle
  (ReusableBlockPad.callerFrame state trace message)

noncomputable def initialization :=
  ReusableResponseInitialization.Projected.initialization ReusableBlockPad.componentStep
    ReusableResponse.begin ReusableBlockPad.ready FlaggedBlockXor.code ReusableBlockPad.code oracle
    (ReusableBlockPad.callerFrame state trace message) P key Bits.toList hHalt hTape read hRead
    (fun _ => width) (fun _ _ _ => by simp)
    (PrivateBitGeneration.decode width) (PrivateBitGeneration.decode_store width)

noncomputable def whole :=
  ReusableResponseInitialization.follow ReusableBlockPad.componentStep ReusableResponse.begin ReusableBlockPad.ready
    P.code FlaggedBlockXor.code ReusableBlockPad.code oracle (ReusableBlockPad.callerFrame state trace message)
    (initialization P key hHalt hTape read hRead oracle state trace message)
    (fun key : Bits width => retainedKey key.toList) (fun _ _ _ => rfl)
    (ReusableBlockPad.consumer oracle state trace message) (fun _ => rfl)
    (fun _ => 49 * width + 35)
    (fun _ result _ => le_of_eq (ReusableBlockPad.consumer_budget oracle state trace message result.1))

theorem budget (input : Input) :
    (whole P key hHalt hTape read hRead oracle state trace message).budget input =
      P.execution.budget input + 50 * width + 39 := by
  rw [whole, ReusableResponseInitialization.follow_budget,
    initialization, ReusableResponseInitialization.Projected.budget]
  omega

theorem semantics (input : Input) :
    (whole P key hHalt hTape read hRead oracle state trace message).semantics input =
      (P.execution.semantics input).map (fun result => ((key result, ()), ())) := by
  rw [whole, ReusableResponseInitialization.follow_semantics,
    initialization, ReusableResponseInitialization.Projected.semantics]
  simp only [PMF.bind_map, ReusableBlockPad.consumer_semantics, PMF.pure_map, Function.comp_def]
  rfl

/-- The original initialization and consumer cost correlation is retained. -/
theorem costed (input : Input) :
    (whole P key hHalt hTape read hRead oracle state trace message).costed input =
      ((initialization P key hHalt hTape read hRead oracle state trace message).costed input).bind
        (fun generated => ((ReusableBlockPad.consumer oracle state trace message).costed generated.1.1).map
          (fun returned => ((generated.1, returned.1), generated.2 + returned.2))) := rfl

include hHalt hTape hRead in
theorem run (input : Input) (horizon : Nat)
    (hTime : P.execution.budget input + 50 * width + 39 ≤ horizon) :
    TimedExecution.eval (step P oracle state trace message) horizon
      (.initializing (.generating (P.execution.entry input))) =
      (P.execution.semantics input).map (fun result => ReusableResponseInitialization.Control.active
        (ReusableResponseSource.Control.source (retainedKey (key result).toList)
          ⟨state, .running (ReusableBlockPad.finalCaller (key result) message),
            ReusableBlockPad.finalTrace trace (key result) message⟩)) := by
  have h := (whole P key hHalt hTape read hRead oracle state trace message).final_run input
    (by
      intro result hr
      rw [semantics, PMF.mem_support_map_iff] at hr
      obtain ⟨result, _, rfl⟩ := hr
      change step P oracle state trace message
        (.active (.source (retainedKey (key result).toList)
          ⟨state, .running (ReusableBlockPad.finalCaller (key result) message),
            ReusableBlockPad.finalTrace trace (key result) message⟩)) = _
      simp [step, ReusableResponseInitialization.step, ReusableResponseSource.step,
        Reification.timedStep, Reification.terminal, ReusableBlockPad.finalCaller, PMF.pure_map]
      rfl)
    horizon (by rw [budget]; exact hTime)
  rw [semantics, PMF.map_comp] at h
  exact h

noncomputable def ciphertext (input : Input) (horizon : Nat) : PMF (List Bool) :=
  (TimedExecution.eval (step P oracle state trace message) horizon
    (.initializing (.generating (P.execution.entry input)))).map ReusableBlockPad.observe

include hHalt hTape hRead in
theorem ciphertext_eq (input : Input) (horizon : Nat)
    (hTime : P.execution.budget input + 50 * width + 39 ≤ horizon) :
    ciphertext P oracle state trace message input horizon =
      (P.execution.semantics input).map (fun result => (OneTimePad.encrypt (key result) message).toList) := by
  rw [ciphertext, run P key hHalt hTape read hRead oracle state trace message input horizon hTime, PMF.map_comp]
  simp only [Function.comp_def, ReusableBlockPad.observe, ReusableBlockPad.finalCaller,
    Machine.Configuration.outputBits]
  have hb : ∀ bits : List Bool, (ResponseLoading.loaded bits).bits = bits := by
    intro bits
    cases bits <;> simp [ResponseLoading.loaded, ResponseLoading.fromCells, Tape.bits]
  simp only [hb]

end Foundation.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask
