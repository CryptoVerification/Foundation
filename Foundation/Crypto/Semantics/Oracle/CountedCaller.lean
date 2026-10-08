import Foundation.Crypto.Semantics.Oracle.BalancedCopyFramed
import Foundation.Crypto.Semantics.Oracle.OneUseCodeRelocation

/-! A fixed caller consumes one public marker per rejected request. At the
blank separator it enters the relocated plaintext-copy block. Data preceding
that separator remains on the physical input tape throughout normal copying. -/
namespace CryptoOracle.Interactive.CountedCaller
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

def before : Code :=
  [.native (.branch .input 6 1 1), .native (.branch .output 8 2 8),
   .native (.randomBit .output), .call, .native (.moveRight .input), .native (.jump 0),
   .native (.moveRight .input), .native (.jump 10), .native .halt]

def code : Code := CodeRelocation.host before BalancedCopy.code

def waiting (past : List (Option Bool)) (markers payload : List Bool) : Machine.Configuration :=
  { inputTape := RequestExport.packetTape past (payload.map some ++ [none]) markers
    outputTape := ResponseLoading.loaded [false] }

def selected (past : List (Option Bool)) (markers payload : List Bool) (bit : Bool) : Machine.Configuration :=
  { (waiting past markers payload) with pc := 3, outputTape := RequestExport.packetTape [] [] [bit] }

def advanced (past : List (Option Bool)) (marker : Bool) (markers payload : List Bool) : Machine.Configuration :=
  waiting (some marker :: past) markers payload

def copyEntry (past : List (Option Bool)) (payload : List Bool) : Machine.Configuration :=
  { pc := 1, inputTape := RequestExport.packetTape (none :: past) [] payload
    outputTape := ResponseLoading.loaded [false] }

def ready (past : List (Option Bool)) (payload : List Bool) : Machine.Configuration :=
  { pc := 17, inputTape := RequestExport.packetTape (none :: past) [] payload
    outputTape := RequestExport.packetTape [] ([none].drop payload.length) payload }

variable {State : Type u} (native : Machine.Program) (oracle : BitOracle State)
    (key : Machine.Tape) (state : State) (trace : List (List Bool × List Bool))

theorem choose (past : List (Option Bool)) (marker : Bool) (markers payload : List Bool) :
    TimedExecution.eval (OneUseSource.step native code oracle) 3
      (.source false key ⟨state, .running (waiting past (marker :: markers) payload), trace⟩) =
      sampleBit.map (fun bit => .source false key
        ⟨state, .running (selected past (marker :: markers) payload bit), trace⟩) := by
  cases marker <;>
    simp [TimedExecution.eval, OneUseSource.step, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, code, before, CodeRelocation.host,
      waiting, selected, RequestExport.packetTape, ResponseLoading.loaded, ResponseLoading.fromCells,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, Machine.Tape.write, PMF.map_comp, Function.comp_def]
  all_goals congr 1; funext bit; cases bit <;> rfl

/-- After the actual rejection has returned at address four, two real
instructions consume the marker and return to the loop test. -/
theorem advance (past : List (Option Bool)) (marker : Bool) (markers payload : List Bool) :
    TimedExecution.eval (OneUseSource.step native code oracle) 2
      (.source false key ⟨state, .running { (waiting past (marker :: markers) payload) with pc := 4 }, trace⟩) =
      PMF.pure (.source false key ⟨state, .running (advanced past marker markers payload), trace⟩) := by
  cases markers <;>
    simp [TimedExecution.eval, OneUseSource.step, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, code, before, CodeRelocation.host,
      waiting, advanced, RequestExport.packetTape, ResponseLoading.loaded, ResponseLoading.fromCells,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, Machine.Tape.moveRight, PMF.pure_map]

theorem enter_copy (past : List (Option Bool)) (payload : List Bool) :
    TimedExecution.eval (OneUseSource.step native code oracle) 3
      (.source false key ⟨state, .running (waiting past [] payload), trace⟩) =
      PMF.pure (CodeRelocation.oneUse before.length
        (.source false key ⟨state, .running (copyEntry past payload), trace⟩)) := by
  cases payload <;>
    simp [TimedExecution.eval, OneUseSource.step, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, code, before, CodeRelocation.host,
      waiting, copyEntry, CodeRelocation.oneUse, CodeRelocation.frame, CodeRelocation.control,
      RequestExport.packetTape, ResponseLoading.loaded, ResponseLoading.fromCells,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, Machine.Configuration.rebasePc, Machine.Tape.moveRight, PMF.pure_map]

/-- The physically consumed marker prefix survives through copy and rewind.
The endpoint is the actual normal call instruction in the combined code. -/
theorem prepare_normal (past : List (Option Bool)) (payload : List Bool) :
    TimedExecution.eval (OneUseSource.step native code oracle) (11 * payload.length + 8)
      (.source false key ⟨state, .running (waiting past [] payload), trace⟩) =
      PMF.pure (CodeRelocation.oneUse before.length
        (.source false key ⟨state, .running (ready past payload), trace⟩)) := by
  rw [show 11 * payload.length + 8 = 3 + (11 * payload.length + 5) by omega,
    TimedExecution.eval_add, enter_copy, PMF.pure_bind]
  unfold code
  rw [CodeRelocation.one_use_eval]
  have h := BalancedCopy.run_framed native oracle key state trace past payload [] [none] (some false)
  change TimedExecution.eval _ _ (OneUseSource.Control.source false key
    ⟨state, .running (copyEntry past payload), trace⟩) = _ at h
  rw [h, PMF.pure_map]
  rfl

noncomputable def preparation : Procedure (OneUseSource.step native code oracle)
    (List (Option Bool) × List Bool) Unit :=
  Procedure.ofFixed _
    (fun input => .source false key ⟨state, .running (waiting input.1 [] input.2), trace⟩)
    (fun input _ => CodeRelocation.oneUse before.length
      (.source false key ⟨state, .running (ready input.1 input.2), trace⟩))
    (fun _ => PMF.pure ()) (fun input => 11 * input.2.length + 8)
    (fun input => by simpa only [PMF.pure_map] using prepare_normal native oracle key state trace input.1 input.2)

theorem ready_active (past : List (Option Bool)) (payload : List Bool) :
    ((ready past payload).rebasePc before.length).halted = false := rfl

theorem ready_call (past : List (Option Bool)) (payload : List Bool) :
    code[((ready past payload).rebasePc before.length).pc]? = some .call := rfl

theorem ready_halt (past : List (Option Bool)) (payload : List Bool) :
    code[((ready past payload).rebasePc before.length).pc + 1]? = some (.native .halt) := rfl

theorem ready_tape (past : List (Option Bool)) (payload : List Bool) (hPayload : payload ≠ []) :
    ((ready past payload).rebasePc before.length).outputTape = Machine.PairPreparation.operand [] payload [] := by
  cases payload with
  | nil => contradiction
  | cons bit rest =>
      have hd : ([none] : List (Option Bool)).drop (bit :: rest).length = [] :=
        List.drop_eq_nil_of_le (by simp)
      simp only [ready, Machine.Configuration.rebasePc, hd]
      rfl

end CryptoOracle.Interactive.CountedCaller
