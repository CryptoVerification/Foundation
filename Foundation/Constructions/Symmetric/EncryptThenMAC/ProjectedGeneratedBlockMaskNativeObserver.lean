import Foundation.Constructions.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask
import Foundation.Examples.ReusableBlockPadNativeObserver

/-! Any certified native generator, real block masking and an actual finite
native observer. The public physical entry depends only on ciphertext, while
exported private key/history remain in the saved producer state. Native
generation retains full internal state until its existing ownership transfer. -/
namespace Foundation.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask.NativeObserver
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ResponseHandoffProgram
open Foundation.Examples
open ReusableBlockPad.NativeObserver (RuntimeState boundary publicMachine publicCaller decision observer)
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} {Result : Type w} {Output : Type x} {width : Nat}
    (P : Machine.Procedure Input Result) (key : Result → Bits width)
    (hHalt : ∀ input result, (P.execution.exit input result).halted = true)
    (hTape : ∀ input result, (P.execution.exit input result).outputTape = ResponseExport.endTape (key result).toList)
    (read : Input → Machine.Configuration → Result)
    (hRead : ∀ input result, read input (P.execution.exit input result) = result)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (message : Bits width) (input : Input)

theorem absorbing (target : RuntimeState State) (h : boundary target = true) :
    ProjectedGeneratedBlockMask.step P oracle state trace message target = PMF.pure target :=
  ReusableNativeObservation.absorbing ReusableBlockPad.componentStep ReusableResponse.begin ReusableBlockPad.ready
    P.code FlaggedBlockXor.code ReusableBlockPad.code oracle
    (ReusableBlockPad.callerFrame state trace message) target h

noncomputable def completion :=
  Completion.ofProcedure
    ((ProjectedGeneratedBlockMask.whole P key hHalt hTape read hRead oracle state trace message).reindex (fun _ : Unit => input))
    rfl (terminal := fun target => boundary target = true)
    (by
      intro result hr
      change result ∈ ((ProjectedGeneratedBlockMask.whole P key hHalt hTape read hRead oracle state trace message).semantics input).support at hr
      rw [ProjectedGeneratedBlockMask.semantics, PMF.mem_support_map_iff] at hr
      obtain ⟨result, _, rfl⟩ := hr
      rfl)

theorem completion_semantics :
    (completion P key hHalt hTape read hRead oracle state trace message input).execution.semantics () =
      (P.execution.semantics input).map (fun result =>
        ReusableResponseInitialization.Control.active
          (ReusableResponseSource.Control.source (retainedKey (key result).toList)
            ⟨state, .running (ReusableBlockPad.finalCaller (key result) message), ReusableBlockPad.finalTrace trace (key result) message⟩)) := by
  rw [completion, Completion.ofProcedure_semantics]
  change ((ProjectedGeneratedBlockMask.whole P key hHalt hTape read hRead oracle state trace message).semantics input).map _ = _
  rw [ProjectedGeneratedBlockMask.semantics, PMF.map_comp]
  rfl

variable (Q : Machine.Procedure Machine.Configuration Output)
    (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hQHalt : ∀ machine output, output ∈ (Q.execution.semantics machine).support →
      (Q.execution.exit machine output).halted = true)
    (cap : Nat) (hCap : ∀ ciphertext : List Bool, ciphertext.length = width →
      Q.execution.budget (publicCaller ciphertext) ≤ cap)

include hCap in
theorem supported_cap (target : RuntimeState State)
    (h : target ∈ ((completion P key hHalt hTape read hRead oracle state trace message input).execution.semantics ()).support) :
    Q.execution.budget (publicMachine target) ≤ cap := by
  rw [completion_semantics, PMF.mem_support_map_iff] at h
  obtain ⟨result, _, rfl⟩ := h
  change Q.execution.budget (publicCaller (OneTimePad.encrypt (key result) message).toList) ≤ cap
  exact hCap _ (Bits.length_toList _)

noncomputable def whole :=
  NativeContinuation.whole (ProjectedGeneratedBlockMask.step P oracle state trace message) boundary publicMachine
    (completion P key hHalt hTape read hRead oracle state trace message input)
    (absorbing P oracle state trace message) Q publicMachine
    (fun target => hEntry (publicMachine target)) cap
    (supported_cap P key hHalt hTape read hRead oracle state trace message input Q cap hCap)

theorem budget :
    (whole P key hHalt hTape read hRead oracle state trace message input Q hEntry cap hCap).budget () =
      P.execution.budget input + 50 * width + 40 + cap := by
  rw [whole, NativeContinuation.whole_budget]
  change (ProjectedGeneratedBlockMask.whole P key hHalt hTape read hRead oracle state trace message).budget input + 1 + cap = _
  rw [ProjectedGeneratedBlockMask.budget]

noncomputable def game (horizon : Nat) : PMF Bool :=
  (TimedExecution.eval
    (NativeContinuation.step (ProjectedGeneratedBlockMask.step P oracle state trace message) boundary publicMachine Q.code)
    horizon (.producing (.initializing (.generating (P.execution.entry input))))).map decision

include hHalt hTape hRead hEntry hQHalt hCap in
/-- Whole native execution equals the ciphertext distribution followed by
this observer's native semantics, with all execution stages charged. -/
theorem game_eq (horizon : Nat)
    (hTime : P.execution.budget input + 50 * width + 40 + cap ≤ horizon) :
    game P oracle state trace message input Q horizon =
      (ProjectedGeneratedBlockMask.ciphertext P oracle state trace message input
        (P.execution.budget input + 50 * width + 39)).bind (observer Q) := by
  have ht : (completion P key hHalt hTape read hRead oracle state trace message input).execution.budget () + 1 + cap ≤ horizon := by
    change (ProjectedGeneratedBlockMask.whole P key hHalt hTape read hRead oracle state trace message).budget input + 1 + cap ≤ horizon
    rw [ProjectedGeneratedBlockMask.budget]
    omega
  have h := NativeContinuation.run (ProjectedGeneratedBlockMask.step P oracle state trace message) boundary publicMachine
    (completion P key hHalt hTape read hRead oracle state trace message input)
    (absorbing P oracle state trace message) Q publicMachine (fun target => hEntry (publicMachine target))
    hQHalt cap (supported_cap P key hHalt hTape read hRead oracle state trace message input Q cap hCap) horizon ht
  have hg := congrArg (fun distribution => distribution.map decision) h
  change game P oracle state trace message input Q horizon = _ at hg
  rw [ProjectedGeneratedBlockMask.ciphertext_eq P key hHalt hTape read hRead oracle state trace message input _ (Nat.le_refl _)]
  simpa only [completion_semantics, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
    publicMachine, ReusableNativeObservation.publicMachine,
    ReusableBlockPad.finalCaller, ReusableBlockPad.caller, Machine.Configuration.advance,
    observer, publicCaller, decision, ReusableNativeObservation.decision] using hg

theorem time_polynomial {generation width observerCap : Nat → Nat}
    (hGeneration : PolynomiallyBounded generation) (hWidth : PolynomiallyBounded width)
    (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded (fun n => generation n + 50 * width n + 40 + observerCap n) :=
  ((hGeneration.add ((PolynomiallyBounded.const 50).mul hWidth)).add
    (PolynomiallyBounded.const 40)).add hObserver

end Foundation.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask.NativeObserver
