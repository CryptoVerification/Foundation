import Foundation.Examples.ReusableBlockPad
import Foundation.Constructions.Symmetric.PRGEncryption

/-! The real block-mask experiment with any certified finite key-generation
program. Key distributions need not be uniform and elapsed time may depend
on the generated key. A generator's cryptographic security is a separate
premise, never inferred from execution or from its declared budget. -/
namespace Foundation.Symmetric.EncryptThenMAC.GeneratedBlockMask
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ResponseHandoffProgram
open Foundation.Examples
open scoped ENNReal
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} {width : Nat}
    (P : Machine.Procedure Input (Bits width))
    (hHalt : ∀ input key, (P.execution.exit input key).halted = true)
    (hTape : ∀ input key, (P.execution.exit input key).outputTape = ResponseExport.endTape key.toList)
    (read : Input → Machine.Configuration → Bits width)
    (hRead : ∀ input key, read input (P.execution.exit input key) = key)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool)) (message : Bits width)

noncomputable abbrev step := ReusableResponseInitialization.step ReusableBlockPad.componentStep
  ReusableResponse.begin ReusableBlockPad.ready P.code FlaggedBlockXor.code ReusableBlockPad.code oracle
  (ReusableBlockPad.callerFrame state trace message)

noncomputable def initialization :=
  ReusableResponseInitialization.initialization ReusableBlockPad.componentStep ReusableResponse.begin
    ReusableBlockPad.ready FlaggedBlockXor.code ReusableBlockPad.code oracle
    (ReusableBlockPad.callerFrame state trace message) P Bits.toList hHalt hTape read hRead
    (fun _ => width) (fun _ key _ => by simp)
    (Machine.PrivateBitGeneration.decode width) (Machine.PrivateBitGeneration.decode_store width)

noncomputable def whole :=
  ReusableResponseInitialization.follow ReusableBlockPad.componentStep ReusableResponse.begin ReusableBlockPad.ready
    P.code FlaggedBlockXor.code ReusableBlockPad.code oracle (ReusableBlockPad.callerFrame state trace message)
    (initialization P hHalt hTape read hRead oracle state trace message)
    (fun key : Bits width => retainedKey key.toList) (fun _ _ _ => rfl)
    (ReusableBlockPad.consumer oracle state trace message) (fun _ => rfl)
    (fun _ => 49 * width + 35)
    (fun _ result _ => le_of_eq (ReusableBlockPad.consumer_budget oracle state trace message result.1))

theorem budget (input : Input) :
    (whole P hHalt hTape read hRead oracle state trace message).budget input =
      P.execution.budget input + 50 * width + 39 := by
  rw [whole, ReusableResponseInitialization.follow_budget,
    initialization, ReusableResponseInitialization.budget]
  omega

theorem semantics (input : Input) :
    (whole P hHalt hTape read hRead oracle state trace message).semantics input =
      (P.execution.semantics input).map (fun key => ((key, ()), ())) := by
  rw [whole, ReusableResponseInitialization.follow_semantics,
    initialization, ReusableResponseInitialization.semantics]
  simp only [PMF.bind_map, ReusableBlockPad.consumer_semantics, PMF.pure_map, Function.comp_def]
  rfl

/-- Record real generation and consumer costs, retaining their correlation
with the key. Replacing the key's marginal distribution does not replace
this joint distribution. -/
theorem costed (input : Input) :
    (whole P hHalt hTape read hRead oracle state trace message).costed input =
      ((initialization P hHalt hTape read hRead oracle state trace message).costed input).bind
        (fun generated => ((ReusableBlockPad.consumer oracle state trace message).costed generated.1.1).map
          (fun returned => ((generated.1, returned.1), generated.2 + returned.2))) := rfl

include hHalt hTape hRead in
theorem run (input : Input) (horizon : Nat)
    (hTime : P.execution.budget input + 50 * width + 39 ≤ horizon) :
    TimedExecution.eval (step P oracle state trace message) horizon
      (.initializing (.generating (P.execution.entry input))) =
      (P.execution.semantics input).map (fun key => ReusableResponseInitialization.Control.active
        (ReusableResponseSource.Control.source (retainedKey key.toList)
          ⟨state, .running (ReusableBlockPad.finalCaller key message), ReusableBlockPad.finalTrace trace key message⟩)) := by
  have h := (whole P hHalt hTape read hRead oracle state trace message).final_run input
    (by
      intro result hr
      rw [semantics, PMF.mem_support_map_iff] at hr
      obtain ⟨key, _, rfl⟩ := hr
      change step P oracle state trace message
        (.active (.source (retainedKey key.toList)
          ⟨state, .running (ReusableBlockPad.finalCaller key message), ReusableBlockPad.finalTrace trace key message⟩)) = _
      simp [step, ReusableResponseInitialization.step, ReusableResponseSource.step,
        Reification.timedStep, Reification.terminal, ReusableBlockPad.finalCaller, PMF.pure_map]
      rfl)
    horizon (by rw [budget]; exact hTime)
  rw [semantics, PMF.map_comp] at h
  exact h

noncomputable def ciphertext (input : Input) (horizon : Nat) : PMF (List Bool) :=
  (TimedExecution.eval (step P oracle state trace message) horizon
    (.initializing (.generating (P.execution.entry input)))).map ReusableBlockPad.observe

private theorem loaded_bits (bits : List Bool) : (ResponseLoading.loaded bits).bits = bits := by
  cases bits <;> simp [ResponseLoading.loaded, ResponseLoading.fromCells, Tape.bits]

include hHalt hTape hRead in
theorem ciphertext_eq (input : Input) (horizon : Nat)
    (hTime : P.execution.budget input + 50 * width + 39 ≤ horizon) :
    ciphertext P oracle state trace message input horizon =
      (P.execution.semantics input).map (fun key => (OneTimePad.encrypt key message).toList) := by
  rw [ciphertext, run P hHalt hTape read hRead oracle state trace message input horizon hTime, PMF.map_comp]
  simp only [Function.comp_def, ReusableBlockPad.observe, ReusableBlockPad.finalCaller,
    Configuration.outputBits, loaded_bits]

theorem budget_polynomial {generation width : Nat → Nat}
    (hGeneration : PolynomiallyBounded generation) (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => generation n + 50 * width n + 39) :=
  (hGeneration.add ((PolynomiallyBounded.const 50).mul hWidth)).add (PolynomiallyBounded.const 39)

end Foundation.Symmetric.EncryptThenMAC.GeneratedBlockMask
