import Foundation.Crypto.Semantics.Oracle.NativeCallback
import Foundation.Examples.ResponseExport

/-! Native sampling/encryption, physical response export and loading, source
resumption, and a real source halt run in one common continuing controller. -/
namespace Foundation.NativeCallbackExamples
open Foundation.Probability TimedExecution
open CryptoOracle.Interactive NativeCallback
universe u v w
set_option backward.isDefEq.respectTransparency false

def code : Code := [.native .halt]

def caller (input : Machine.Tape) : Machine.Configuration := { inputTape := input }

def final {State : Type u} (input : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool)) (request packet : List Bool) : NativeCallback.Control State :=
  .source ⟨state, .running { inputTape := input, outputTape := ResponseLoading.loaded packet, halted := true },
    (request, packet) :: trace⟩

theorem source_halts {State : Type u} (native : Machine.Program) (oracle : BitOracle State)
    (input : Machine.Tape) (state : State) (trace : List (List Bool × List Bool))
    (request packet : List Bool) (fuel : Nat) (hFuel : 1 ≤ fuel) :
    TimedExecution.eval (NativeCallback.step native code oracle (caller input) state trace request) fuel
      (.source (resumed (caller input) state trace request packet)) =
      PMF.pure (final input state trace request packet) := by
  rw [source_eval, Reification.timed_eval_eq]
  cases fuel with
  | zero => omega
  | succ fuel =>
      simp only [Reification.eval, resumed, caller, Reification.terminal, Bool.false_eq_true,
        ↓reduceIte, CryptoOracle.Interactive.step, transition, code,
        List.getElem?_cons_zero, Machine.Instruction.next, PMF.pure_bind]
      rw [Reification.eval_terminal _ oracle fuel _ (by rfl), PMF.pure_map]
      rfl

section Generic
variable {Input : Type v} {Output : Type w} {State : Type u}
    (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)
    (oracle : BitOracle State) (sourceInput : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

include hHalt hTape hRead hCap in
theorem run (input : Input) :
    TimedExecution.eval (NativeCallback.step P.code code oracle (caller sourceInput) state trace request)
      (P.execution.budget input + (6 * cap input + 8))
      (.responding (.running (P.execution.entry input))) =
      (P.execution.semantics input).map (fun output => final sourceInput state trace request (encode output)) := by
  let C := callback P encode hHalt hTape read hRead cap hCap code oracle (caller sourceInput) state trace request
  rw [callback_law P encode hHalt hTape read hRead cap hCap code oracle (caller sourceInput)
    state trace request input _ (by omega)]
  change (C.costed input).bind (fun result => TimedExecution.eval _ _ _) = _
  rw [← PMF.bindOnSupport_eq_bind]
  have he : ∀ result ∈ (C.costed input).support,
      TimedExecution.eval (NativeCallback.step P.code code oracle (caller sourceInput) state trace request)
        (P.execution.budget input + (6 * cap input + 8) - result.2)
        (.source (resumed (caller sourceInput) state trace request result.1.1)) =
        PMF.pure (final sourceInput state trace request result.1.1) := by
    intro result hResult
    have hb := C.bounded input result hResult
    have hBudget := callback_budget P encode hHalt hTape read hRead cap hCap code oracle
      (caller sourceInput) state trace request input
    change result.2 ≤ C.budget input at hb
    change C.budget input = _ at hBudget
    rw [hBudget] at hb
    exact source_halts P.code oracle sourceInput state trace request result.1.1 _ (by omega)
  have hBind : (C.costed input).bindOnSupport (fun result _ =>
      TimedExecution.eval (NativeCallback.step P.code code oracle (caller sourceInput) state trace request)
        (P.execution.budget input + (6 * cap input + 8) - result.2)
        (.source (resumed (caller sourceInput) state trace request result.1.1))) =
      (C.costed input).bindOnSupport (fun result _ =>
        PMF.pure (final sourceInput state trace request result.1.1)) := by
    congr 1
    funext result hResult
    exact he result hResult
  rw [hBind, PMF.bindOnSupport_eq_bind]
  change (C.costed input).map ((fun result => final sourceInput state trace request result.1) ∘ Prod.fst) = _
  rw [← PMF.map_comp, C.correct]
  simp only [C, callback, exported, transfer, Procedure.seq, Procedure.liftBoundary,
    Procedure.ofFixed, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

end Generic

open Foundation.Symmetric ResponseExportExamples

theorem pad_run {State : Type u} (width : Nat) (input : ResponseExportExamples.PadInput width)
    (oracle : BitOracle State) (sourceInput : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :
    TimedExecution.eval (NativeCallback.step (encryptor width).code code oracle (caller sourceInput) state trace request)
      (14 * width + 10) (.responding (.running ((encryptor width).execution.entry input))) =
      PMF.pure (final sourceInput state trace request (OneTimePad.encrypt input.key input.message).toList) := by
  have h := NativeCallbackExamples.run (encryptor width) Bits.toList (fun _ _ => rfl) (fun _ _ => rfl)
    (readVector width) (encryptor_read width) (fun _ => width) (fun _ _ _ => by simp)
    oracle sourceInput state trace request input
  have hn : (encryptor width).execution.budget input + (6 * width + 8) = 14 * width + 10 := by
    change 8 * width + 2 + (6 * width + 8) = _
    omega
  rw [hn] at h
  simpa only [encryptor, Foundation.Symmetric.EncryptThenMAC.PrimitiveContracts.padEncrypt,
    Machine.Procedure.ofFixed, Procedure.ofFixed, Procedure.reindex, Function.comp_def, PMF.pure_map] using h

theorem sampler_run {State : Type u} (width : Nat) (retained : List Bool)
    (oracle : BitOracle State) (sourceInput : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :
    TimedExecution.eval (NativeCallback.step (sampler width).code code oracle (caller sourceInput) state trace request)
      (11 * width + 10) (.responding (.running ((sampler width).execution.entry retained))) =
      (uniform (Bits width)).map (fun key => final sourceInput state trace request key.toList) := by
  have h := NativeCallbackExamples.run (sampler width) Bits.toList (fun _ _ => rfl) (fun _ _ => rfl)
    (readVector width) (sampler_read width) (fun _ => width) (fun _ _ _ => by simp)
    oracle sourceInput state trace request retained
  have hn : (sampler width).execution.budget retained + (6 * width + 8) = 11 * width + 10 := by
    change 5 * width + 2 + (6 * width + 8) = _
    omega
  rw [hn] at h
  exact h

theorem pad_saved_run {State : Type u} (width : Nat) (input : ResponseExportExamples.PadInput width)
    (oracle : BitOracle State) (sourceInput : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (privateStore : Machine.Tape) :
    TimedExecution.eval (framedStep (NativeCallback.step (encryptor width).code code oracle
      (caller sourceInput) state trace request)) (14 * width + 10)
      (.responding (.running ((encryptor width).execution.entry input)), privateStore) =
      PMF.pure (final sourceInput state trace request (OneTimePad.encrypt input.key input.message).toList,
        privateStore) := by
  rw [framed_eval, pad_run, PMF.pure_map]

/-- Genuine execution of the resumed source halt, rather than exhausted fuel. -/
theorem pad_stops {State : Type u} (width : Nat) (input : ResponseExportExamples.PadInput width)
    (oracle : BitOracle State) (sourceInput : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (endpoint : NativeCallback.Control State)
    (hEndpoint : endpoint ∈ (TimedExecution.eval (NativeCallback.step (encryptor width).code code oracle
      (caller sourceInput) state trace request) (14 * width + 10)
      (.responding (.running ((encryptor width).execution.entry input)))).support) :
    ∃ frame, endpoint = .source frame ∧ Reification.terminal frame.control = true := by
  rw [pad_run, PMF.mem_support_pure_iff] at hEndpoint
  subst endpoint
  exact ⟨_, rfl, rfl⟩

end Foundation.NativeCallbackExamples
