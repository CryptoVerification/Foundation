import Foundation.Constructions.Hash.NativeRuntimeLoop

/-! Exact joint semantics of the common runtime-message hash loop. Message
length affects the evaluator budget, but never the finite instruction list. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

def runtimePayloadBits (message : List (List Bool)) : List Bool :=
  message.flatMap (fun payload => false :: payload)

def runtimeInputBits (message : List (List Bool)) : List Bool :=
  runtimePayloadBits message ++ [true]

def runtimeLoopSteps (n κ count : Nat) : Nat :=
  count * (7 * n + 8 * κ + 14) + (7 * n + 5 * κ + 13)

/-- One fixed code handles every valid message of arbitrary finite length.
The final input head remains on the terminal marker; all consumed cells,
private oracle state and complete transcript are represented in the law. -/
theorem runtime_loop_run {State : Type*} (oracle : BitOracle State) (n : Nat)
    (width : ∀ state request answer, answer ∈ (oracle state request).support → answer.2.length = n)
    (before after : Code) (terminal : List Bool)
    (state : State) (prior : List (List Bool × List Bool))
    (beforeInput : List (Option Bool)) (digest : List Bool) (message : List (List Bool))
    (digestLength : digest.length = n)
    (messageWidth : ∀ payload ∈ message, payload.length = terminal.length) (tail : List (Option Bool) := []) :
    TimedExecution.eval
      (Reification.timedStep (before ++ runtimeLoopCode before.length n terminal ++ after) oracle)
      (runtimeLoopSteps n terminal.length message.length)
      (⟨state, .running { pc := before.length, inputTape := FixedWidthCopy.frontier beforeInput ((runtimeInputBits message).map some ++ tail), outputTape := ResponseLoading.loaded digest }, prior⟩ : Configuration State) =
    ((Foundation.Hash.iterate digest (markedBlocks terminal message)).run
      (Program.adaptOracle (fun pair => pair.1 ++ pair.2) id oracle) state).map
      (iterationFinish (runtimeHaltPc before.length n terminal.length)
        (FixedWidthCopy.frontier ((runtimePayloadBits message).reverse.map some ++ beforeInput) (some true :: tail)) prior) := by
  induction message generalizing state prior beforeInput digest with
  | nil =>
      have h := runtime_loop_terminal oracle state prior before after beforeInput digest terminal
        (fun answer h => (width state _ answer h).trans digestLength.symm) tail
      simpa [digestLength, runtimeLoopSteps, runtimeInputBits, runtimePayloadBits,
        markedBlocks, Foundation.Hash.encode, Foundation.Hash.iterate, Program.run,
        Program.adaptOracle, iterationFinish, encodeIterationTrace, PMF.map_comp,
        PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def, PMF.map] using h
  | cons payload message ih =>
      have payloadWidth := messageWidth payload (by simp)
      have restWidth : ∀ p ∈ message, p.length = terminal.length := fun p hp => messageWidth p (by simp [hp])
      rw [show runtimeLoopSteps n terminal.length (payload :: message).length =
          (7 * n + 8 * terminal.length + 14) + runtimeLoopSteps n terminal.length message.length by
            simp [runtimeLoopSteps, Nat.add_mul]; omega,
        TimedExecution.eval_add]
      have roundRun := runtime_loop_data oracle state prior before after beforeInput
        ((runtimeInputBits message).map some ++ tail) digest payload terminal payloadWidth
        (fun answer h => (width state _ answer h).trans digestLength.symm)
      simp only [digestLength] at roundRun
      simp only [runtimeInputBits, runtimePayloadBits, List.flatMap_cons, List.append_assoc,
        List.map_append, List.map_cons, List.cons_append] at roundRun ⊢
      rw [roundRun, PMF.bind_map]
      simp only [markedBlocks, Foundation.Hash.encode, List.map_cons, List.map_append, List.cons_append, List.map_nil,
        Foundation.Hash.iterate, Program.run, Program.adaptOracle,
        PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext answer hAnswer
      have h := ih answer.1 ((digest ++ false :: payload, answer.2) :: prior)
        ((false :: payload).reverse.map some ++ beforeInput) answer.2
        (width state _ answer hAnswer) restWidth
      simp only [runtimeInputBits, runtimePayloadBits, markedBlocks, Foundation.Hash.encode,
        List.map_append, List.map_cons] at h
      simp only [List.map_nil, List.append_assoc, List.cons_append, List.nil_append, id_eq] at h ⊢
      rw [h]
      congr 1
      funext out
      simp [iterationFinish, encodeIterationTrace, List.reverse_append, List.reverse_cons,
        List.map_append, List.append_assoc]

end Foundation.Hash.Native
