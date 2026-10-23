import Foundation.Examples.MixedCircuitMACAnalysisCompilation
import Foundation.Crypto.Semantics.Oracle.NativeVerdictPacketExecution
import Foundation.Examples.MixedCircuitMACNativeRepairExample

/-! Actual native verdict materialization for arbitrary one-seed MAC analysis
circuits. State/transcript snapshots are logical retained payload, not exported
by code. Caller-to-block linking, mask generation cost and full multi-input
compilation remain separate obligations. -/
namespace CryptoOracle.Interactive.NativeVerdictPacket
open Machine Foundation.Probability

theorem written_view (output : Tape) (bits : List Bool) :
    (written output bits).current :: (written output bits).left =
      bits.reverse.map some ++ (output.current :: output.left) := by
  induction bits generalizing output with
  | nil => rfl
  | cons bit rest ih =>
      rw [written, ih]
      cases output with
      | mk left current right => cases right <;> simp [Tape.moveRight, Tape.write, List.reverse_cons, List.map_append, List.append_assoc]

def read (count : Nat) (output : Tape) : List Bool :=
  (((output.current :: output.left).take count).reverse).map (fun cell => cell.getD false)

theorem read_written (output : Tape) (bits : List Bool) : read bits.length (written output bits) = bits := by
  rw [read, written_view]
  simp

theorem original_cell_retained (output : Tape) (bits : List Bool) :
    ((written output bits).current :: (written output bits).left).drop bits.length = output.current :: output.left := by
  rw [written_view]
  simp

theorem written_cells (output : Tape) (bits : List Bool) : (written output bits).cells ≤ output.cells + bits.length := by
  induction bits generalizing output with
  | nil => simp [written]
  | cons bit rest ih =>
      have bound := ih (output.moveRight.write (some bit))
      rw [Tape.cells_write] at bound
      have move := Tape.cells_moveRight_le output
      simp only [written, List.length_cons]
      omega

end CryptoOracle.Interactive.NativeVerdictPacket

namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.AnalysisCompilation
open Foundation.Probability
open Foundation.Symmetric
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Foundation.Logic.Polygraph.ScheduleCertificate
open CryptoOracle CryptoOracle.Interactive
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

abbrev Packet := CryptoOracle.Interactive.NativeVerdictPacket.code

def program {stage : Nat} {m} (circuit : Circuit signature (source stage) m) : Code := Packet (flags circuit)
def budget {stage : Nat} {m} (_ : Circuit signature (source stage) m) : Nat := 2 * width m + 3

def verdict (orders : Nat → Schedule 8) (vertex : signature.PortAtom) : family orders vertex → Bool :=
  match vertex with | .stage _ => fun value => value.result | .finish => fun value => value.result

def verdicts (orders : Nat → Schedule 8) : (shape : Port signature) → Bundle (family orders) shape → List Bool
  | .atom vertex, value => [verdict orders vertex value]
  | .unit, _ => []
  | .pair left right, pair => verdicts orders left pair.1 ++ verdicts orders right pair.2

theorem restored_verdicts (orders : Nat → Schedule 8) (seed : Outcome) (shape : Port signature) (bits : Bundle Bits shape) :
    verdicts orders shape (shape.map (restore orders seed) bits) =
      NativeVerdictPacket.result (flatten shape bits) seed.result := by
  induction shape with
  | atom vertex => cases vertex <;> cases bits <;> simp [verdicts, verdict, Shape.map, restore, flatten, NativeVerdictPacket.result, MACNormalization.sanitize]
  | unit => rfl
  | pair left right one two => simp only [verdicts, Shape.map, one, two, flatten, NativeVerdictPacket.result, List.map_append]

theorem program_length {stage : Nat} {m} (circuit : Circuit signature (source stage) m) :
    (program circuit).length = 4 * width m + 4 := by rw [program, NativeVerdictPacket.code_length, flags_length]

/-- Both branches, even for a false input verdict, execute the same exact
number of real native transitions. Entry retains arbitrary input memory. -/
theorem native_run {State : Type} {stage : Nat} {m} (circuit : Circuit signature (source stage) m)
    (oracle : BitOracle State) (input output : Machine.Tape) (state : State) (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep (program circuit) oracle) (budget circuit)
      (⟨state, .running (NativeVerdictPacket.start 0 input output), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (NativeVerdictPacket.finish (flags circuit) input output), trace⟩ := by
  simpa only [program, budget, flags_length] using NativeVerdictPacket.timed (flags circuit) oracle input output state trace

/-- Native output cells equal the verdict projection of the original full
MAC analysis. The seed's hidden state/trace are retained proof data, not
additional native read instructions. This theorem makes the entry relation explicit. -/
theorem native_correct (orders : Nat → Schedule 8) {stage : Nat} {m}
    (circuit : Circuit signature (source stage) m) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (oracle : BitOracle MACNativeQuantitative.State) (input output : Machine.Tape)
    (state : MACNativeQuantitative.State) (trace : List (List Bool × List Bool)) :
    (TimedExecution.eval (Reification.timedStep (program circuit) oracle) (budget circuit)
      (⟨state, .running (NativeVerdictPacket.start 0 input output), trace⟩ : Configuration MACNativeQuantitative.State)).map
        (fun frame => match frame.control with
          | .running machine => NativeVerdictPacket.read (width m) machine.outputTape
          | _ => []) =
    (MixedCircuit.evaluate (MAC.base orders) circuit valid
      (RandomFunctionMACNativeCaller.Native.observe ⟨state, .running (NativeVerdictPacket.start 0 input output), trace⟩)).map
        (verdicts orders m) := by
  rw [native_run, compile_correct]
  simp only [PMF.pure_map, NativeVerdictPacket.finish]
  rw [← flags_length circuit, ← NativeVerdictPacket.result_length (flags circuit) (output.current.getD false), NativeVerdictPacket.read_written]
  rw [restored_verdicts]
  rfl

noncomputable def checkedBits (orders : Nat → Schedule 8) : CheckedModel MAC.relators (MACNormalization.condition orders) Bits where
  base := model orders
  localSound := by
    intro stage valid input
    simp only [MAC.relators, before, after, MixedCircuit.evaluate, model, PMF.pure_bind]

/-- A repaired higher comparison gives exactly equal generated programs;
the original internal conditions remain a premise of the correctness proof. -/
theorem repaired_program_eq {old : Nat → Prop} (orders : Nat → Schedule 8)
    {basis : HigherBasis StatefulWiring.UnionRules} {stage : Nat} {m}
    {left right : Circuit signature (source stage) m}
    {first second : RewriteTrack (relators := StatefulWiring.UnionRules) left right}
    (cell : PresentedCell basis first second) (changed : Finset Nat) (cached : Holds old (PresentedCell.support cell))
    (unchanged : ∀ label ∉ changed, old label → MACNormalization.condition orders label)
    (rechecked : Holds (MACNormalization.condition orders) (fresh (PresentedCell.support cell) changed)) :
    program left = program right := by
  obtain ⟨_, _, leftValid, rightValid, equal⟩ := Stateful.cell_repaired
    (StatefulWiring.checked (Stateful.liftChecked (State := Unit) (checkedBits orders))) cell changed cached unchanged rechecked
  have same := equal () true
  change Stateful.evaluate (Stateful.lift (model orders)) left leftValid () true =
    Stateful.evaluate (Stateful.lift (model orders)) right rightValid () true at same
  simp only [Stateful.evaluate_lift, evaluate_bits, PMF.pure_map] at same
  have member : ((), output left true) ∈ (PMF.pure ((), output left true)).support := by simp
  rw [same] at member
  have outputs := congrArg Prod.snd ((PMF.mem_support_pure_iff _ _).mp member)
  exact congrArg (fun bits => Packet (flatten m bits)) outputs


theorem repaired_same_process {old : Nat → Prop} (orders : Nat → Schedule 8)
    {basis : HigherBasis StatefulWiring.UnionRules} {stage : Nat} {m}
    {left right : Circuit signature (source stage) m}
    {first second : RewriteTrack (relators := StatefulWiring.UnionRules) left right}
    (cell : PresentedCell basis first second) (changed : Finset Nat) (cached : Holds old (PresentedCell.support cell))
    (unchanged : ∀ label ∉ changed, old label → MACNormalization.condition orders label)
    (rechecked : Holds (MACNormalization.condition orders) (fresh (PresentedCell.support cell) changed))
    {State : Type} (oracle : BitOracle State) (fuel : Nat) (frame : Configuration State) :
    TimedExecution.eval (Reification.timedStep (program left) oracle) fuel frame =
      TimedExecution.eval (Reification.timedStep (program right) oracle) fuel frame := by
  rw [repaired_program_eq orders cell changed cached unchanged rechecked]

/-- Apply to the previously generated finite comparison under actual
nonempty tensor/copy/discard, rather than assuming a new whole-path root. -/
theorem example_program_eq (orders : Nat → Schedule 8) (stage : Nat) :
    program (NativeContinuation.RepairExample.originalDiagram stage) =
      program (NativeContinuation.RepairExample.updatedDiagram stage) :=
  repaired_program_eq orders (NativeContinuation.RepairExample.comparison stage) ∅
    (MACNormalization.conditions orders _) (fun _ _ proof => proof) (MACNormalization.conditions orders _)

def doubledPort : Nat → Port signature
  | 0 => source 0
  | count + 1 => .pair (doubledPort count) (doubledPort count)

def duplications : (count : Nat) → Circuit signature (source 0) (doubledPort count)
  | 0 => .wire (.identity (source 0))
  | count + 1 => .seq (duplications count) (.wire (.copy (doubledPort count)))

theorem doubled_width (count : Nat) : width (doubledPort count) = 2 ^ count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [doubledPort, width, ih, pow_succ]; omega

/-- Output materialization costs cannot be hidden in the number of copy
schemata. Port/boundary payload is also part of a fair input-size model. -/
theorem duplication_cost (count : Nat) :
    (program (duplications count)).length = 4 * 2 ^ count + 4 ∧
      budget (duplications count) = 2 * 2 ^ count + 3 := by
  rw [program_length, budget, doubled_width]
  exact ⟨rfl, rfl⟩

/-- info: (12, 7, [false, false]) -/
#guard_msgs in
#eval (program (NativeContinuation.analysis 0) |>.length, budget (NativeContinuation.analysis 0), flags (NativeContinuation.analysis 0))

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.AnalysisCompilation
