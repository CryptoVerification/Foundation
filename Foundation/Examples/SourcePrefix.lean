import Foundation.Crypto.Semantics.Oracle.SourcePrefix

/-! An actual random instruction chooses the first bit of an arbitrary-length
request. Physical request capture then reaches the first call boundary. -/
namespace Foundation.SourcePrefixExamples
open Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false

def code : Code := [.native (.randomBit .output), .call, .native .halt]
variable {State : Type u} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (rest : List Bool) (tail : List (Option Bool))

def initialMachine : Machine.Configuration :=
  { outputTape := RequestExport.packetTape [] tail (false :: rest) }

def selectedMachine (bit : Bool) : Machine.Configuration :=
  { pc := 1, outputTape := RequestExport.packetTape [] tail (bit :: rest) }

def captured (bit : Bool) : Configuration State :=
  ⟨state, .awaiting (selectedMachine rest tail bit).advance (bit :: rest), trace⟩

theorem choose_run :
    SourcePrefix.step code oracle ⟨state, .running (initialMachine rest tail), trace⟩ =
      sampleBit.map (fun bit => ⟨state, .running (selectedMachine rest tail bit), trace⟩) := by
  simp [SourcePrefix.step, SourcePrefix.boundary, Reification.timedStep, Reification.terminal,
    Reification.perform, Reification.action, transition, code, initialMachine, selectedMachine,
    Machine.Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance,
    RequestExport.packetTape, Machine.Tape.write]
  congr 1
  funext bit
  cases bit <;> rfl

theorem run :
    TimedExecution.eval (SourcePrefix.step code oracle) (2 * rest.length + 6)
      ⟨state, .running (initialMachine rest tail), trace⟩ =
      sampleBit.map (captured state trace rest tail) := by
  rw [show 2 * rest.length + 6 = (2 * (false :: rest).length + 3) + 1 by simp; omega,
    TimedExecution.eval, choose_run, PMF.bind_map]
  rw [PMF.map]
  congr 1
  funext bit
  simpa only [List.length_cons, captured, Function.comp_def] using
    (SourcePrefix.capture_run code oracle (selectedMachine rest tail bit) state trace (bit :: rest)
      [] tail rfl rfl rfl)

noncomputable def input : SourcePrefix.Input code oracle :=
  ⟨⟨state, .running (initialMachine rest tail), trace⟩, 2 * rest.length + 6, by
    rw [run]
    intro frame hFrame
    rw [PMF.mem_support_map_iff] at hFrame
    obtain ⟨bit, _, he⟩ := hFrame
    subst frame
    rfl⟩

theorem request_distribution (native : Machine.Program) (key : Machine.Tape) :
    ((SourcePrefix.procedure code oracle native key).costed (input oracle state trace rest tail)).map Prod.fst =
      sampleBit.map (captured state trace rest tail) := by
  rw [SourcePrefix.boundary_distribution]
  exact run oracle state trace rest tail

theorem selection_cost_independence (firstNative secondNative : Machine.Program)
    (firstKey secondKey : Machine.Tape) :
    (SourcePrefix.procedure code oracle firstNative firstKey).costed (input oracle state trace rest tail) =
      (SourcePrefix.procedure code oracle secondNative secondKey).costed (input oracle state trace rest tail) := rfl
theorem handoff_distribution (native : Machine.Program) (key : Machine.Tape) :
    ((SourcePrefix.toHandler code oracle native key).costed (input oracle state trace rest tail)).map
      (fun result => (SourcePrefix.toHandler code oracle native key).exit (input oracle state trace rest tail) result.1) =
      sampleBit.map (fun bit => OneUseSource.Control.handling false
        (selectedMachine rest tail bit).advance state trace (bit :: rest)
        (.preparing (.preparing (.reading key (selectedMachine rest tail bit).outputTape {})))) := by
  rw [SourcePrefix.toHandler_distribution]
  change (TimedExecution.eval (SourcePrefix.step code oracle) (2 * rest.length + 6)
    ⟨state, .running (initialMachine rest tail), trace⟩).map (SourcePrefix.next key) = _
  rw [run, PMF.map_comp]
  rfl
end Foundation.SourcePrefixExamples
