import Foundation.Constructions.Hash.PolygraphOracle
import Foundation.Examples.PolygraphRandomOracle

/-! A fresh sample is physically inserted and then queried again from the
same retained tape, using the opposite supplied random bit on the second call.
The generic packet theorem additionally certifies admission and export costs. -/
namespace Foundation.Hash.Native.PolygraphOracle.Examples

open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability
open Foundation.Symmetric
open CryptoOracle.RandomOracle.PolygraphExamples.Native

def ask (coin : Bool) (machine : Machine.Configuration) (fuel : Nat) :=
  Reification.simulate (SimulatorLookupDispatch.code 1 1) (fun state _ => (state, [])) coin fuel
    (SimulatorQueryLoading.loadingFrame 1 1 () machine [] (compressionPacket first ++ [false]))

def retained (frame : Configuration Unit) : Machine.Configuration :=
  match frame.control with
  | .running machine => machine
  | _ => {}

def twice (coin : Bool) :=
  let initial : Machine.Configuration :=
    { inputTape := Tape.ofBits (SimulatorLookup.tableBits ([] : Table 1 1)) }
  let a := ask coin initial 1000
  let b := ask (!coin) (retained a.1) 1000
  let value : Bits 1 := fun _ => coin
  (SimulatorDispatchQueryLoading.headBits (retained a.1).outputTape,
   SimulatorDispatchQueryLoading.headBits (retained b.1).outputTape,
   (retained a.1).inputTape.bits == SimulatorLookup.tableBits [(first, value)],
   (retained b.1).inputTape.bits == (retained a.1).inputTape.bits,
   a.2, b.2)

/-- info: true -/
#guard_msgs in
#eval [false, true].all fun coin =>
  let (a, b, stored, unchanged, firstTime, nextTime) := twice coin
  a == [coin] && b == [coin] && stored && unchanged && firstTime == 65 && nextTime == 79

/-- info: (73, 87, 358) -/
#guard_msgs in
#eval (SimulatorQueryPacket.steps first ([] : Table 1 1),
  SimulatorQueryPacket.steps first [(first, zero)], totalBudget 1 1 2)

def repeated : CryptoOracle.Program (Key 1 1) (Bits 1) (Bits 1 × Bits 1) :=
  .query first fun a => .query first fun b => .done (a, b)

theorem repeated_queries : repeated.BoundedQueries 2 :=
  .query _ _ 1 (fun _ => .query _ _ 0 (fun _ => .done _ 0))

theorem repeated_erasure :
    (repeated.run costedOracle ([], 0)).map (Program.mapState Prod.fst) =
      repeated.run RandomOracle.oracle [] := erase_cost repeated [] 0

theorem empty_steps : SimulatorQueryPacket.steps first ([] : Table 1 1) = 73 := by decide

theorem hit_steps (value : Bits 1) : SimulatorQueryPacket.steps first [(first, value)] = 87 := by
  rfl

theorem repeated_law : repeated.run costedOracle ([], 0) =
    (uniform (Bits 1)).map (fun value =>
      (⟨(value, value), ([(first, value)], 160), [(first, value), (first, value)]⟩ :
        Outcome (Key 1 1) (Bits 1) (Bits 1 × Bits 1) (Table 1 1 × Nat))) := by
  simp [repeated, Program.run, costedOracle, RandomOracle.oracle, PMF.bind_map,
    PMF.map_comp, PMF.pure_map, PMF.pure_bind, empty_steps, hit_steps, Function.comp_def]
  rfl

theorem repeated_exact
    (out : Outcome (Key 1 1) (Bits 1) (Bits 1 × Bits 1) (Table 1 1 × Nat))
    (ho : out ∈ (repeated.run costedOracle ([], 0)).support) :
    out.state.2 = 160 ∧ out.result.1 = out.result.2 ∧ out.state.1.length = 1 := by
  rw [repeated_law, PMF.mem_support_map_iff] at ho
  obtain ⟨value, _, rfl⟩ := ho
  exact ⟨rfl, rfl, rfl⟩

theorem repeated_cost
    (out : Outcome (Key 1 1) (Bits 1) (Bits 1 × Bits 1) (Table 1 1 × Nat))
    (ho : out ∈ (repeated.run costedOracle ([], 0)).support) : out.state.2 ≤ 358 := by
  exact empty_bound repeated_queries (by decide) out ho

end Foundation.Hash.Native.PolygraphOracle.Examples
