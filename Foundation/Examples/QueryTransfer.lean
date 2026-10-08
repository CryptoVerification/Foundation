import Foundation.Crypto.Semantics.Oracle.QueryTransfer

/-! A finite source program performs one real call, receives a random
two-bit response, resumes and halts. The caller input tape and previous
transcript are arbitrary. All request and response transfer steps are charged. -/
namespace Foundation.QueryTransferExamples
open Foundation.Probability
open CryptoOracle.Interactive

def code : Code := [.call, .native .halt]

noncomputable def oracle (state : Nat) (_ : List Bool) : PMF (Nat × List Bool) :=
  sampleBit.map (fun bit => (state + 1, [bit, !bit]))

def machine (request : List Bool) (before after : List (Option Bool)) (input : Machine.Tape) : Machine.Configuration :=
  { inputTape := input, outputTape := RequestExport.packetTape before after request }

theorem response_length (state : Nat) (request : List Bool) :
    ∀ answer ∈ (oracle state request).support, answer.2.length ≤ 2 := by
  intro answer hAnswer
  rw [oracle, PMF.mem_support_map_iff] at hAnswer
  obtain ⟨bit, _, he⟩ := hAnswer
  subst answer
  simp

noncomputable def certificate (state : Nat) (request : List Bool)
    (before after : List (Option Bool)) (input : Machine.Tape)
    (trace : List (List Bool × List Bool)) :=
  QueryTransfer.fullStage code oracle (machine request before after input) state trace request
    before after rfl rfl rfl 2 (response_length state request)

theorem budget (state : Nat) (request : List Bool) (before after : List (Option Bool))
    (input : Machine.Tape) (trace : List (List Bool × List Bool)) :
    (certificate state request before after input trace).budget = 2 * request.length + 12 := by
  change 2 * request.length + 3 + (3 * 2 + 3) = _
  omega

def final (state : Nat) (request : List Bool) (input : Machine.Tape)
    (trace : List (List Bool × List Bool)) (bit : Bool) : Configuration Nat :=
  ⟨state + 1, .running { pc := 1, inputTape := input, outputTape := ResponseLoading.loaded [bit, !bit], halted := true },
    (request, [bit, !bit]) :: trace⟩

theorem run (state : Nat) (request : List Bool) (before after : List (Option Bool))
    (input : Machine.Tape) (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep code oracle) (2 * request.length + 13)
      (⟨state, .running (machine request before after input), trace⟩ : Configuration Nat) =
    sampleBit.map (final state request input trace) := by
  have hResume (bit : Bool) :
      TimedExecution.eval (Reification.timedStep code oracle) 1
        (QueryTransfer.resumed (machine request before after input).advance trace request (state + 1, [bit, !bit])) =
      PMF.pure (final state request input trace bit) := by
    simp [TimedExecution.eval, QueryTransfer.resumed, machine, Machine.Configuration.advance,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, code, Machine.Instruction.next, final]
  have h := (certificate state request before after input trace).law (2 * request.length + 13)
    (by rw [budget]; omega)
  simp only [id_eq] at h
  rw [h]
  simp only [certificate, QueryTransfer.fullStage, QueryTransfer.stage, oracle,
    PMF.bind_map, Function.comp_def, List.length_cons, List.length_nil]
  have ht : 2 * request.length + 13 - ((2 * request.length + 3) + 9) = 1 := by omega
  simp only [ht]
  simp_rw [hResume]
  simp only [PMF.map, Function.comp_def]

theorem source_stops (state : Nat) (request : List Bool) (before after : List (Option Bool))
    (input : Machine.Tape) (trace : List (List Bool × List Bool)) :
    Reification.HaltsWithin code oracle
      ⟨state, .running (machine request before after input), trace⟩ (2 * request.length + 13) := by
  intro result hResult
  rw [← Reification.timed_eval_eq, run, PMF.mem_support_map_iff] at hResult
  obtain ⟨bit, _, he⟩ := hResult
  subst result
  rfl

end Foundation.QueryTransferExamples
