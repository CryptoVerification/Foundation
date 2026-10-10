import Foundation.Crypto.Semantics.Machine.DelimitedTapeComparison
import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.BoundaryExactTime
import Foundation.Crypto.Semantics.Machine.ClosedSubroutineArrival

/-! Native equality for run-time table keys, sharing the existing numerical
comparator. Keys have equal widths; their actual prefixes and suffixes are
retained. The input delimiter is temporarily replaced by the equality bit.
A table-lookup caller must restore that delimiter before continuing. -/
namespace Machine.DelimitedTapeEquality
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev program : Program := DelimitedTapeComparison.programWithDecision (fun order => order == Ordering.eq)

@[simp] theorem code_length : program.length = 59 := rfl

theorem no_randomBit (which : TapeId) : Instruction.randomBit which ∉ program := by
  cases which <;> decide

theorem compare_eq (candidate query : List Bool) (width : candidate.length = query.length) :
    (BinaryComparison.compare Ordering.eq (candidate.zip query) == Ordering.eq) = decide (candidate = query) := by
  have injective : Binary.value candidate = Binary.value query → candidate = query := by
    intro same
    calc
      candidate = Binary.encode candidate.length (Binary.value candidate) := (Binary.encode_value candidate).symm
      _ = Binary.encode query.length (Binary.value query) := by rw [width, same]
      _ = query := Binary.encode_value query
  rw [BinaryComparison.compare_values,
    List.map_fst_zip (by omega : candidate.length ≤ query.length),
    List.map_snd_zip (by omega : query.length ≤ candidate.length)]
  by_cases equal : candidate = query
  · subst query
    simp
  · have unequal : Binary.value candidate ≠ Binary.value query := fun same => equal (injective same)
    split_ifs <;> simp_all
    omega

structure Input where
  beforeInput : List (Option Bool)
  beforeOutput : List (Option Bool)
  candidate : List Bool
  query : List Bool
  tail : List Bool
  suffix : List Bool
  width : candidate.length = query.length

def start (input : Input) : Configuration :=
  DelimitedTapeComparison.state Ordering.eq input.beforeInput input.beforeOutput
    (FiniteBitEncoding.delimit input.candidate ++ input.tail) (input.query ++ input.suffix)

def finish (input : Input) : Configuration :=
  DelimitedTapeComparison.doneWithDecision (fun order => order == Ordering.eq)
    (BinaryComparison.compare Ordering.eq (input.candidate.zip input.query))
    ((DelimitedTapeComparison.marked input.candidate).reverse.map some ++ input.beforeInput)
    (input.query.reverse.map some ++ input.beforeOutput) input.tail input.suffix

/-- Full tape layout, not just a decoded Boolean decision. -/
theorem run (input : Input) :
    evalConfigWithin program (start input) (7 * input.candidate.length + 3) = PMF.pure (finish input) :=
  DelimitedTapeComparison.eval_decision_layout _ _ _ _ _ _ _ _ input.width

theorem before_halt (input : Input) :
    evalConfigWithin program (start input) (7 * input.candidate.length + 2) =
      PMF.pure { finish input with halted := false } := by
  simpa only [Bool.toNat_false, Nat.add_zero, start, finish, List.map_reverse] using
    DelimitedTapeComparison.eval_decision_stage_layout (fun order => order == Ordering.eq) false
      Ordering.eq input.beforeInput input.beforeOutput input.candidate input.query
      input.tail input.suffix input.width

theorem status (input : Input) :
    (finish input).inputTape.current = some (decide (input.candidate = input.query)) := by
  simp only [finish, DelimitedTapeComparison.doneWithDecision, Tape.write]
  rw [compare_eq _ _ input.width]

/-- The output retains the query and every following cell. The head has
advanced past exactly the query, and its old left prefix is still present. -/
theorem output_layout (input : Input) :
    (finish input).outputTape =
      { Tape.ofBits input.suffix with left := input.query.reverse.map some ++ input.beforeOutput } := rfl

theorem input_layout (input : Input) :
    (finish input).inputTape =
      { Tape.ofBits (false :: input.tail) with
        left := (DelimitedTapeComparison.marked input.candidate).reverse.map some ++ input.beforeInput,
        current := some (decide (input.candidate = input.query)) } := by
  simp only [finish, DelimitedTapeComparison.doneWithDecision, Tape.write]
  rw [compare_eq _ _ input.width]

/-- Exact first halt, including empty keys. -/
theorem first_joint (input : Input) :
    runToBoundary (stepPMF program) Configuration.halted (7 * input.candidate.length + 3) (start input) =
      PMF.pure (finish input, 7 * input.candidate.length + 3) := by
  have h := runToBoundary_joint_of_adjacent (stepPMF program) Configuration.halted
    (start input) (7 * input.candidate.length + 2)
    (by intro machine halted; simp [stepPMF, next, halted])
    (by intro machine support
        rw [Machine.timed_eval_eq, before_halt, PMF.mem_support_pure_iff] at support
        subst machine
        rfl)
    (by intro machine support
        rw [show 7 * input.candidate.length + 2 + 1 = 7 * input.candidate.length + 3 by omega,
          Machine.timed_eval_eq, run, PMF.mem_support_pure_iff] at support
        subst machine
        rfl)
  simpa only [show 7 * input.candidate.length + 2 + 1 = 7 * input.candidate.length + 3 by omega,
    Machine.timed_eval_eq, run, PMF.pure_map] using h

/-- Existing native operational composition can invoke this same code. -/
theorem runs (input : Input) :
    ∃ used, used ≤ 7 * input.candidate.length + 3 ∧
      RunsFor program (start input) (finish input) used := by
  have supported : finish input ∈
      (evalConfigWithin program (start input) (7 * input.candidate.length + 3)).support := by
    rw [run]
    simp
  exact ((mem_support_evalConfigWithin_iff _ _ _ _).mp supported).toRunsFor_le

noncomputable def procedure : Machine.Procedure Input Unit :=
  Machine.Procedure.ofFixed program start (fun input _ => finish input) (fun _ => PMF.pure ())
    (fun input => 7 * input.candidate.length + 3)
    (fun input => by rw [run, PMF.pure_map])

noncomputable def component : NativeComponent Input Unit where
  procedure := procedure
  closed := DelimitedTapeComparison.decision_control_closed _
  entry := fun _ => by change 0 < 59; decide
  active := fun _ => rfl
  halted := fun _ _ _ => rfl

/-- The ordinary native component carries the same actual first-halt
joint law, without a separate realization hypothesis. -/
theorem component_first_joint (input : Input) :
    component.firstArrival.procedure.execution.costed input =
      PMF.pure (finish input, 7 * input.candidate.length + 3) := by
  rw [component.firstArrival_costed]
  exact first_joint input

/-- Replacing the real halt by a real return jump preserves its exact
cost and both retained tapes. The caller must keep its return address
outside the relocated comparison body. -/
theorem subroutine_first_joint (before after : Program) (returnPc : Nat)
    (separate : ∀ pc, pc < program.length → before.length + pc ≠ returnPc) (input : Input) :
    runToBoundary (stepPMF (Program.withSubroutine before program after returnPc))
      (fun machine => machine.pc == returnPc) (7 * input.candidate.length + 3)
      ((start input).rebasePc before.length) =
      PMF.pure ((finish input).resumeAt returnPc, 7 * input.candidate.length + 3) := by
  rw [Program.runToBoundary_subroutineState before program after returnPc separate
    (DelimitedTapeComparison.decision_control_closed _)
    (start input) (by change 0 < 59; decide) rfl,
    first_joint, PMF.pure_map]
  rfl

/-- Full finite syntax and every represented cell are counted at each
intermediate time, rather than only after the comparison has finished. -/
theorem encoded_peak (input : Input) (elapsed : Nat)
    (within : elapsed ≤ 7 * input.candidate.length + 3)
    (target : Configuration)
    (support : target ∈ (TimedExecution.eval (stepPMF program) elapsed (start input)).support) :
    (NativeEncodedResources.completeEncoding.encode (program, target)).length ≤
      NativeEncodedResources.bound program (start input).pc (start input).tapeCells
        (7 * input.candidate.length + 3) :=
  NativeEncodedResources.peak program _ elapsed within (start input) target support

/-- Count the actual first-arrival endpoint at its reported time, retaining
the entire physical state rather than only the equality observation. -/
theorem first_encoded (input : Input) (result : Configuration × Nat)
    (support : result ∈ (runToBoundary (stepPMF program) Configuration.halted
      (7 * input.candidate.length + 3) (start input)).support) :
    (NativeEncodedResources.completeEncoding.encode (program, result.1)).length ≤
      NativeEncodedResources.bound program (start input).pc (start input).tapeCells result.2 :=
  NativeEncodedResources.boundary program Configuration.halted _ _ result support

end Machine.DelimitedTapeEquality
