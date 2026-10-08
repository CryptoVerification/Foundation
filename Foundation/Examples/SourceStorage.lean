import Foundation.Crypto.Semantics.Oracle.SourceStorage
import Foundation.Examples.SourcePrefix

/-! Arbitrary-width random request selection retains all trailing cells.
The bound includes request copies, temporary lists, opaque state and history. -/
namespace Foundation.Examples.SourceStorage
open Foundation.Probability CryptoOracle.Interactive
universe u

theorem selection_peak {State : Type u} (stateSize : State → Nat)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (rest : List Bool) (tail : List (Option Bool)) (elapsed : Nat)
    (hElapsed : elapsed ≤ 2 * rest.length + 6) (intermediate : Configuration State)
    (h : intermediate ∈ (TimedExecution.eval (SourcePrefix.step SourcePrefixExamples.code oracle)
      elapsed ⟨state, .running (SourcePrefixExamples.initialMachine rest tail), trace⟩).support) :
    CryptoOracle.Interactive.SourceStorage.cells stateSize intermediate ≤
      stateSize state + CryptoOracle.Interactive.SourceStorage.traceCells trace +
        6 * rest.length + 2 * tail.length + 18 := by
  have hb := CryptoOracle.Interactive.SourceStorage.running_peak stateSize
    SourcePrefixExamples.code oracle (2 * rest.length + 6) elapsed hElapsed
    (SourcePrefixExamples.initialMachine rest tail) state trace intermediate h
  simp only [SourcePrefixExamples.initialMachine, Machine.Configuration.tapeCells,
    RequestExport.packetTape, List.map_cons, List.cons_append, List.headD_cons, List.tail_cons,
    Machine.Tape.cells, List.length_nil, List.length_append, List.length_map, List.length_cons] at hb
  omega

theorem selection_endpoint {State : Type u} (stateSize : State → Nat)
    (oracle : BitOracle State) (native : Machine.Program) (key : Machine.Tape)
    (state : State) (trace : List (List Bool × List Bool)) (rest : List Bool)
    (tail : List (Option Bool)) (result : Configuration State × Nat)
    (h : result ∈ ((SourcePrefix.procedure SourcePrefixExamples.code oracle native key).costed
      (SourcePrefixExamples.input oracle state trace rest tail)).support) :
    key.cells + CryptoOracle.Interactive.SourceStorage.cells stateSize result.1 ≤
      key.cells + stateSize state + CryptoOracle.Interactive.SourceStorage.traceCells trace +
        2 * rest.length + 2 * tail.length + 6 + 2 * result.2 := by
  have hb := CryptoOracle.Interactive.SourceStorage.procedure_endpoint stateSize
    SourcePrefixExamples.code oracle native key (SourcePrefixExamples.input oracle state trace rest tail)
    (by trivial) result h
  simp only [SourcePrefixExamples.input, CryptoOracle.Interactive.SourceStorage.potential,
    CryptoOracle.Interactive.SourceStorage.capacity, SourcePrefixExamples.initialMachine,
    Machine.Configuration.tapeCells, RequestExport.packetTape, List.map_cons, List.cons_append,
    List.headD_cons, List.tail_cons, Machine.Tape.cells, List.length_nil, List.length_append,
    List.length_map, List.length_cons] at hb
  omega

end Foundation.Examples.SourceStorage
