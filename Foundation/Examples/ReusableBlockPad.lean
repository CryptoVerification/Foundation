import Foundation.Constructions.Symmetric.EncryptThenMAC.BlockPadResponse
import Foundation.Crypto.Semantics.Oracle.ReusableBitInitialization

/-! Real key generation, one arbitrary-width pad request and caller halt in
the reusable runtime. Secrecy observes ciphertext bytes only; it does not
give the observer the private key or the complete internal caller history. -/
namespace Foundation.Examples.ReusableBlockPad
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ResponseHandoffProgram
universe u
set_option backward.isDefEq.respectTransparency false

def code : Code := [.call, .native .halt]

def caller {width : Nat} (message : Bits width) : Machine.Configuration :=
  {outputTape := ResponseLoading.loaded (FlaggedBlockXor.request message.toList)}

def finalCaller {width : Nat} (key message : Bits width) : Machine.Configuration :=
  {(caller message).advance with
    outputTape := ResponseLoading.loaded (OneTimePad.encrypt key message).toList
    halted := true}

def finalTrace {width : Nat} (trace : List (List Bool × List Bool)) (key message : Bits width) :=
  (FlaggedBlockXor.request message.toList, (OneTimePad.encrypt key message).toList) :: trace

variable {State : Type u} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) {width : Nat} (key message : Bits width)

noncomputable def capture :=
  Procedure.ofFixed (ReusableResponse.step FlaggedBlockXor.code code oracle)
    (fun _ : Unit => ReusableResponseSource.Control.source (retainedKey key.toList)
      ⟨state, .running (caller message), trace⟩)
    (fun _ _ : Unit => .processing (caller message).advance state trace (FlaggedBlockXor.request message.toList)
      (.headerWriting (retainedKey key.toList) (FlaggedBlockXor.request message.toList) {}))
    (fun _ => PMF.pure ()) (fun _ => 4 * width + 6)
    (fun _ => by
      have h := ReusableResponse.capture_run FlaggedBlockXor.code code oracle (retainedKey key.toList)
        (caller message) state trace (FlaggedBlockXor.request message.toList) [] [] rfl rfl (by rfl)
      have ht : 2 * (FlaggedBlockXor.request message.toList).length + 4 = 4 * width + 6 := by
        simp only [FlaggedBlockXor.request_length, Bits.length_toList]
        omega
      rw [ht] at h
      simpa only [PMF.pure_map] using h)

noncomputable def body :=
  (BlockPadResponse.service key message code oracle (caller message).advance state trace).observe
    (fun _ => ())
    (fun _ _ => ReusableResponseSource.Control.source (retainedKey key.toList)
      (NativeCallback.resumed (caller message).advance state trace (FlaggedBlockXor.request message.toList)
        (OneTimePad.encrypt key message).toList))
    (by
      intro _ result h
      rw [BlockPadResponse.semantics, PMF.mem_support_pure_iff] at h
      subst result
      rfl)

theorem body_budget : (body oracle state trace key message).budget () = 45 * width + 28 :=
  BlockPadResponse.budget _ _ _ _ _ _ _

noncomputable def finish :=
  Procedure.ofFixed (ReusableResponse.step FlaggedBlockXor.code code oracle)
    (fun _ : Unit => ReusableResponseSource.Control.source (retainedKey key.toList)
      (NativeCallback.resumed (caller message).advance state trace (FlaggedBlockXor.request message.toList)
        (OneTimePad.encrypt key message).toList))
    (fun _ _ : Unit => .source (retainedKey key.toList)
      ⟨state, .running (finalCaller key message), finalTrace trace key message⟩)
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by
      simp [TimedExecution.eval, ReusableResponse.step, ReusableResponseSource.step, NativeCallback.resumed,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition,
        code, caller, finalCaller, finalTrace, Machine.Configuration.advance, Machine.Instruction.next,
        PMF.pure_map])

private noncomputable def raw :=
  ((capture oracle state trace key message).seq (body oracle state trace key message)
    (fun _ _ _ => rfl) (fun _ => 45 * width + 28)
    (fun argument _ _ => by cases argument; rw [body_budget])).seq
      ((finish oracle state trace key message).reindex (fun _ : Unit × Unit => ()))
      (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

noncomputable def whole :=
  (raw oracle state trace key message).observe (fun _ => ())
    (fun _ _ => ReusableResponseSource.Control.source (retainedKey key.toList)
      ⟨state, .running (finalCaller key message), finalTrace trace key message⟩)
    (fun _ _ _ => rfl)

theorem whole_budget : (whole oracle state trace key message).budget () = 49 * width + 35 := by
  change (4 * width + 6) + (45 * width + 28) + 1 = _
  omega

theorem whole_semantics (argument : Unit) :
    (whole oracle state trace key message).semantics argument = PMF.pure () := by
  change ((raw oracle state trace key message).semantics argument).map (fun _ => ()) = _
  exact PMF.map_const _ _

noncomputable abbrev componentStep := ResponseHandoffProgram.step FlaggedBlockXor.code
abbrev ready := Callback.ready
abbrev callerFrame := (⟨state, .running (caller message), trace⟩ : Configuration State)
noncomputable abbrev step := ReusableResponseInitialization.step componentStep ReusableResponse.begin ready
  Machine.OneTimePad.keygen FlaggedBlockXor.code code oracle (callerFrame state trace message)

noncomputable def initialization :=
  ReusableBitInitialization.initialization componentStep ReusableResponse.begin ready
    FlaggedBlockXor.code code oracle (callerFrame state trace message) width

noncomputable def consumer := Procedure.dispatch (fun key : Bits width => whole oracle state trace key message)

theorem consumer_budget (key : Bits width) :
    (consumer oracle state trace message).budget key = 49 * width + 35 :=
  whole_budget oracle state trace key message

theorem consumer_semantics (key : Bits width) :
    (consumer oracle state trace message).semantics key = PMF.pure () :=
  whole_semantics oracle state trace key message ()

noncomputable def initialized :=
  ReusableResponseInitialization.follow componentStep ReusableResponse.begin ready Machine.OneTimePad.keygen
    FlaggedBlockXor.code code oracle (callerFrame state trace message)
    (initialization oracle state trace message)
    (fun key : Bits width => retainedKey key.toList) (fun _ _ _ => rfl)
    (consumer oracle state trace message) (fun _ => rfl)
    (fun _ => 49 * width + 35)
    (fun _ result _ => le_of_eq (consumer_budget oracle state trace message result.1))

theorem initialized_budget : (initialized oracle state trace message).budget () = 55 * width + 41 := by
  rw [initialized, ReusableResponseInitialization.follow_budget]
  change (initialization oracle state trace message).budget () + (49 * width + 35) = _
  rw [initialization, ReusableBitInitialization.budget]
  omega

theorem initialized_semantics :
    (initialized oracle state trace message).semantics () =
      (uniform (Bits width)).map (fun key => ((key, ()), ())) := by
  rw [initialized, ReusableResponseInitialization.follow_semantics]
  change ((initialization oracle state trace message).semantics ()).bind _ = _
  rw [initialization, ReusableBitInitialization.initialization, ReusableResponseInitialization.semantics]
  change ((uniform (Bits width)).map (fun key => (key, ()))).bind _ = _
  simp only [PMF.bind_map, consumer_semantics, PMF.pure_map, Function.comp_def]
  rfl

theorem run (horizon : Nat) (hTime : 55 * width + 41 ≤ horizon) :
    TimedExecution.eval (step oracle state trace message) horizon
      (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      (uniform (Bits width)).map (fun key => ReusableResponseInitialization.Control.active
        (ReusableResponseSource.Control.source (retainedKey key.toList)
          ⟨state, .running (finalCaller key message), finalTrace trace key message⟩)) := by
  have h := (initialized oracle state trace message).final_run ()
    (by
      intro result hr
      rw [initialized_semantics, PMF.mem_support_map_iff] at hr
      obtain ⟨key, _, rfl⟩ := hr
      change step oracle state trace message
        (.active (.source (retainedKey key.toList)
          ⟨state, .running (finalCaller key message), finalTrace trace key message⟩)) = _
      simp [step, ReusableResponseInitialization.step, ReusableResponseSource.step,
        Reification.timedStep, Reification.terminal, finalCaller, PMF.pure_map]
      rfl)
    horizon (by rw [initialized_budget]; exact hTime)
  rw [initialized_semantics, PMF.map_comp] at h
  exact h

def observe : ReusableResponseInitialization.Control ResponseHandoff.Control State → List Bool
  | .active (.source _ frame) =>
      match frame.control with
      | .running machine => machine.outputBits
      | _ => []
  | _ => []

private theorem loaded_bits (bits : List Bool) : (ResponseLoading.loaded bits).bits = bits := by
  cases bits <;> simp [ResponseLoading.loaded, ResponseLoading.fromCells, Tape.bits]

noncomputable def ciphertext (horizon : Nat) : PMF (List Bool) :=
  (TimedExecution.eval (step oracle state trace message) horizon
    (.initializing (.generating (Machine.Configuration.initial (List.replicate width true))))).map observe

theorem ciphertext_eq (horizon : Nat) (hTime : 55 * width + 41 ≤ horizon) :
    ciphertext oracle state trace message horizon =
      (uniform (Bits width)).map (fun key => (OneTimePad.encrypt key message).toList) := by
  rw [ciphertext, run oracle state trace message horizon hTime, PMF.map_comp]
  simp only [Function.comp_def, observe, finalCaller, Configuration.outputBits, loaded_bits]

theorem ciphertext_uniform (horizon : Nat) (hTime : 55 * width + 41 ≤ horizon) :
    ciphertext oracle state trace message horizon = (uniform (Bits width)).map Bits.toList := by
  rw [ciphertext_eq oracle state trace message horizon hTime]
  have h := congrArg (fun p : PMF (Bits width) => p.map Bits.toList) (OneTimePad.ciphertext_uniform message)
  simpa only [OneTimePad.ciphertext, PMF.map_comp, Function.comp_def] using h

/-- Whole-execution perfect secrecy for one fresh key and one request.
Only the ciphertext tape is observed, never the saved private state. -/
theorem perfect_secrecy (other : Bits width) (leftTime rightTime : Nat)
    (hLeft : 55 * width + 41 ≤ leftTime) (hRight : 55 * width + 41 ≤ rightTime)
    (observer : List Bool → PMF Bool) :
    (ciphertext oracle state trace message leftTime).bind observer =
      (ciphertext oracle state trace other rightTime).bind observer := by
  rw [ciphertext_uniform oracle state trace message leftTime hLeft,
    ciphertext_uniform oracle state trace other rightTime hRight]

theorem time_polynomial {width : Nat → Nat} (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => 55 * width n + 41) :=
  ((PolynomiallyBounded.const 55).mul hWidth).add (PolynomiallyBounded.const 41)

end Foundation.Examples.ReusableBlockPad
