import Foundation.Crypto.Semantics.Oracle.RejectionPlan
import Foundation.Constructions.Symmetric.OneTimePad

/-! A fixed caller reads the previous failure response before choosing its
next random request. Every rejected round restores the same private key.
Finite iteration is a runtime prefix, not an artificial machine halt. -/
namespace Foundation.AdaptiveRejectionLoopExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def code : Code := [.native (.branch .output 4 1 4), .native (.randomBit .output),
  .call, .native (.jump 0), .native .halt]

structure Public (State : Type u) where
  input : Machine.Tape
  state : State
  trace : List (List Bool × List Bool)

def machine {State : Type u} (publicState : Public State) : Machine.Configuration :=
  { pc := 3, inputTape := publicState.input, outputTape := ResponseLoading.loaded [false] }

def frame {State : Type u} (publicState : Public State) : Configuration State :=
  ⟨publicState.state, .running (machine publicState), publicState.trace⟩

def chosen {State : Type u} (publicState : Public State) (bit : Bool) : Machine.Configuration :=
  { pc := 2, inputTape := publicState.input, outputTape := RequestExport.packetTape [] [] [bit] }

variable {State : Type u} {width : Nat} (native : Machine.Program) (oracle : BitOracle State)
    (key : Bits width) (hMismatch : width ≠ 1)

def call (publicState : Public State) (bit : Bool) : SelectedRejection.Call State code width where
  machine := chosen publicState bit
  state := publicState.state
  trace := publicState.trace
  request := [bit]
  tail := []
  active := rfl
  instruction := rfl
  tape := rfl
  mismatch := hMismatch

noncomputable def selection : Procedure (OneUseSource.step native code oracle)
    (Public State) (SelectedRejection.Call State code width) :=
  Procedure.ofFixed _
    (fun publicState => .source false (Machine.PairPreparation.operand [] key.toList []) (frame publicState))
    (fun publicState bit => .source false (Machine.PairPreparation.operand [] key.toList [])
      ⟨bit.state, .running bit.machine, bit.trace⟩)
    (fun publicState => sampleBit.map (call hMismatch publicState)) (fun _ => 3)
    (fun publicState => by
      simp [TimedExecution.eval, OneUseSource.step, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, code, frame, machine, chosen, call,
        Machine.Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance, Machine.Configuration.tape,
        ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape, Machine.Tape.write,
        PMF.map_comp, Function.comp_def]
      congr 1
      funext bit
      cases bit <;> rfl)

def next (descriptor : SelectedRejection.Call State code width) : Public State :=
  ⟨descriptor.machine.inputTape, descriptor.state, (descriptor.request, [false]) :: descriptor.trace⟩

theorem call_pc (descriptor : SelectedRejection.Call State code width) : descriptor.machine.pc = 2 := by
  have h := descriptor.instruction
  have hb : descriptor.machine.pc < 5 := by
    by_contra hn
    have he : code[descriptor.machine.pc]? = none := List.getElem?_eq_none (by simp [code]; omega)
    rw [he] at h
    contradiction
  interval_cases hp : descriptor.machine.pc <;> simp [code, hp] at h ⊢

theorem next_frame (descriptor : SelectedRejection.Call State code width) :
    frame (next descriptor) = SelectedRejection.returned descriptor := by
  rcases descriptor with ⟨m, state, trace, request, tail, active, instruction, tape, mismatch⟩
  have hp := call_pc (show SelectedRejection.Call State code width from
    ⟨m, state, trace, request, tail, active, instruction, tape, mismatch⟩)
  dsimp only at hp active
  cases m with
  | mk pc input output halted =>
      simp only at hp active
      subst pc
      subst halted
      rfl

noncomputable def plan : SelectedRejection.Plan State (Public State) width code oracle [] frame where
  native := native
  key := key.toList
  key_width := by simp
  selection := selection native oracle key hMismatch
  handoff := fun _ _ _ => rfl
  cap := fun _ => 12 * min width 1 + 31
  bound := by
    intro start descriptor h
    change descriptor ∈ (sampleBit.map (call hMismatch start)).support at h
    rw [PMF.mem_support_map_iff] at h
    obtain ⟨bit, _, he⟩ := h
    subst descriptor
    unfold SelectedRejection.reject
    rw [OneUseSource.rejectedInvocation_budget]
    simp [SelectedRejection.input, call, Machine.PreparationCheck.consumed]
    omega
  entry := fun _ => rfl

noncomputable def execution (stop : Public State → Bool) (rounds : Nat) :=
  (plan native oracle key hMismatch).execute next next_frame (12 * min width 1 + 34)
    (fun _ => by change 3 + (12 * min width 1 + 31) ≤ _; omega) stop rounds

theorem budget (stop : Public State → Bool) (rounds : Nat) (start : Public State) :
    (execution native oracle key hMismatch stop rounds).budget start = rounds * (12 * min width 1 + 34) :=
  SelectedRejection.Plan.execute_budget _ _ _ _ _ stop rounds start

noncomputable def publicSelection (start : Public State) :=
  sampleBit.map (fun bit => (call hMismatch start bit, 3))

theorem public_cost (stop : Public State → Bool) (rounds : Nat) (start : Public State) :
    (execution native oracle key hMismatch stop rounds).costed start =
      CostedIteration.eval (CostedIteration.guarded
        (SelectedRejection.roundKernel [] next (publicSelection hMismatch)) stop) rounds start := by
  apply SelectedRejection.Plan.public_cost
  intro publicState
  simp only [plan, selection, Procedure.ofFixed, publicSelection, PMF.map_comp, Function.comp_def]

theorem key_independence (firstNative secondNative : Machine.Program) (firstKey secondKey : Bits width)
    (stop : Public State → Bool) (rounds : Nat) (start : Public State) :
    (execution firstNative oracle firstKey hMismatch stop rounds).costed start =
      (execution secondNative oracle secondKey hMismatch stop rounds).costed start := by
  rw [public_cost, public_cost]

theorem exit (stop : Public State → Bool) (rounds : Nat) (start finish : Public State) :
    (execution native oracle key hMismatch stop rounds).exit start finish =
      .source false (Machine.PairPreparation.operand [] key.toList []) (frame finish) :=
  SelectedRejection.Plan.execute_exit _ _ _ _ _ stop rounds start finish

theorem entry (stop : Public State → Bool) (rounds : Nat) (start : Public State) :
    (execution native oracle key hMismatch stop rounds).entry start =
      .source false (Machine.PairPreparation.operand [] key.toList []) (frame start) :=
  SelectedRejection.Plan.execute_entry _ _ _ _ _ stop rounds start

/-- Stopping this logical prefix does not stop the actual caller. Remaining
time runs the same machine, including its next response-dependent branch. -/
theorem resume_law (stop : Public State → Bool) (rounds : Nat) (start : Public State)
    (horizon : Nat) (hHorizon : rounds * (12 * min width 1 + 34) ≤ horizon) :
    TimedExecution.eval (OneUseSource.step native code oracle) horizon
      (.source false (Machine.PairPreparation.operand [] key.toList []) (frame start)) =
      ((execution native oracle key hMismatch stop rounds).costed start).bind (fun result =>
        TimedExecution.eval (OneUseSource.step native code oracle) (horizon - result.2)
          (.source false (Machine.PairPreparation.operand [] key.toList []) (frame result.1))) :=
  by
    have h := (execution native oracle key hMismatch stop rounds).law start horizon
      (by rw [budget]; exact hHorizon)
    have he : (execution native oracle key hMismatch stop rounds).entry start =
        .source false (Machine.PairPreparation.operand [] key.toList []) (frame start) :=
      SelectedRejection.Plan.execute_entry _ _ _ _ _ stop rounds start
    rw [he] at h
    simp only [exit] at h
    exact h

/-- The whole retained public trace and actual accumulated cost are jointly
independent of the private key, for any key prior and native-code family. -/
theorem joint_independence (prior : PMF (Bits width)) (natives : Bits width → Machine.Program)
    (stop : Public State → Bool) (rounds : Nat) (start : Public State) :
    KeyedIteration.joint prior (fun key =>
      (execution (natives key) oracle key hMismatch stop rounds).costed start) =
      prior.bind (fun key =>
        (CostedIteration.eval (CostedIteration.guarded
          (SelectedRejection.roundKernel [] next (publicSelection hMismatch)) stop) rounds start).map
          (fun result => (key, result))) := by
  apply KeyedIteration.joint_independent
  intro key
  exact public_cost (natives key) oracle key hMismatch stop rounds start

end Foundation.AdaptiveRejectionLoopExamples
