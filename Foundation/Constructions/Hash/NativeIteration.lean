import Foundation.Constructions.Hash.NativePreparation
import Foundation.Crypto.Semantics.Oracle.QueryMap

/-! Compile a fixed finite block sequence into native compression-call code.
All returned chaining values are processed by that code at runtime. The initial
digest is a caller tape precondition, not a free reset performed by the routine.
The list of blocks is specialized into the finite code; a uniform runtime
message parser is a separate obligation. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

/-- Compile each block, with one actual call per block and one native halt. -/
def iterationCode (digestWidth : Nat) : List (List Bool) → Code
  | [] => [.native .halt]
  | block :: rest => compressionCode digestWidth block ++ iterationCode digestWidth rest

def iterationSteps (digestWidth : Nat) : List (List Bool) → Nat
  | [] => 1
  | block :: rest => (7 * digestWidth + 5 * block.length + 6) + iterationSteps digestWidth rest

/-- Observable raw requests concatenate the fixed-width digest and block. -/
def encodeIterationTrace (trace : List ((List Bool × List Bool) × List Bool)) :
    List (List Bool × List Bool) :=
  trace.map (fun entry => (entry.1.1 ++ entry.1.2, entry.2))

def iterationFinish {State : Type*} (pc : Nat) (input : Tape)
    (prior : List (List Bool × List Bool))
    (out : Outcome (List Bool × List Bool) (List Bool) (List Bool) State) : Configuration State :=
  ⟨out.state, .running { pc := pc, inputTape := input, outputTape := ResponseLoading.loaded out.result, halted := true },
    (encodeIterationTrace out.trace).reverse ++ prior⟩

/-- The finite native code realizes the existing adaptive `iterate` program.
The oracle is arbitrary except for its fixed response width. Complete private
state and trace are retained, including responses selected adaptively by it. -/
theorem iteration_run {State : Type*} (oracle : BitOracle State) (digestWidth : Nat)
    (width : ∀ state request answer, answer ∈ (oracle state request).support →
      answer.2.length = digestWidth)
    (before after : Code) (input : Tape) (state : State)
    (prior : List (List Bool × List Bool)) (digest : List Bool) (blocks : List (List Bool))
    (digestLength : digest.length = digestWidth) :
    TimedExecution.eval (Reification.timedStep (before ++ iterationCode digestWidth blocks ++ after) oracle)
      (iterationSteps digestWidth blocks)
      (⟨state, .running { pc := before.length, inputTape := input, outputTape := ResponseLoading.loaded digest }, prior⟩ : Configuration State) =
    ((Foundation.Hash.iterate digest blocks).run
      (Program.adaptOracle (fun pair => pair.1 ++ pair.2) id oracle) state).map
      (iterationFinish (before.length + (iterationCode digestWidth blocks).length - 1) input prior) := by
  induction blocks generalizing before state prior digest with
  | nil =>
      simp [iterationCode, iterationSteps, TimedExecution.eval, Reification.timedStep,
        Reification.terminal, Reification.perform, Reification.action, transition,
        Machine.Instruction.next, Foundation.Hash.iterate, Program.run,
        PMF.pure_map, iterationFinish, encodeIterationTrace]
  | cons block rest ih =>
      rw [iterationSteps, TimedExecution.eval_add]
      have hc := compression_run oracle state prior before (iterationCode digestWidth rest ++ after)
        input digest block (fun answer h => (width state _ answer h).trans digestLength.symm)
      simp only [digestLength, iterationCode, List.append_assoc] at hc ⊢
      rw [hc, PMF.bind_map]
      simp only [Foundation.Hash.iterate, Program.run, Program.adaptOracle,
        PMF.bind_map, Function.comp_def, PMF.map_bind, PMF.map_comp]
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext answer hAnswer
      have h := ih (before ++ compressionCode digestWidth block) answer.1
        ((digest ++ block, answer.2) :: prior) answer.2 (width state _ answer hAnswer)
      simp only [List.append_assoc, List.length_append, compressionCode_length] at h
      simp only [Nat.add_assoc, id_eq] at h ⊢
      rw [h]
      congr 1
      funext out
      simp [iterationFinish, encodeIterationTrace, List.reverse_cons, List.append_assoc,
        compressionCode_length, Nat.add_assoc]

end Foundation.Hash.Native
