import Foundation.Crypto.Semantics.Oracle.OneUseResponse
import Foundation.Crypto.Semantics.Oracle.PreparedCallback

/-! Physical operand preparation and acceptance in the one-use controller.
Acceptance changes the use flag only after both lengths have been checked. -/
namespace CryptoOracle.Interactive.OneUseSource
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

def preparationBoundary : Control State → Bool
  | .handling _ _ _ _ _ (.preparing (.preparing component)) => PreparedCallback.boundary component
  | _ => true

def embedPreparation (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (component : Machine.PairPreparation.Control) : Control State :=
  .handling false saved state trace request (.preparing (.preparing component))

noncomputable def preparation : Procedure (step native code oracle) Machine.PairPreparation.Input Unit :=
  Machine.PairPreparation.procedure.liftBoundary PreparedCallback.boundary (fun _ _ _ => rfl)
    (fun component h => by cases component <;> simp_all [PreparedCallback.boundary, Machine.PairPreparation.step])
    (fun _ _ => ()) (fun _ _ => rfl)
    (step native code oracle) preparationBoundary (embedPreparation saved state trace request) (fun _ => rfl)
    (fun component h => by
      cases component <;> simp_all [PreparedCallback.boundary, step, CheckedCallback.step,
        Machine.PreparationCheck.step, embedPreparation, PMF.map_comp, Function.comp_def] <;> rfl)

noncomputable def acceptance : Procedure (step native code oracle) (Machine.PairPreparation.Input × Unit) Unit :=
  Procedure.ofFixed _
    (fun input => embedPreparation saved state trace request (Machine.PairPreparation.procedure.exit input.1 input.2))
    (fun input _ => .handling true saved state trace request (.computing
      (Machine.PairPreparation.operand [] input.1.first input.1.firstTail)
      (Machine.PairPreparation.operand [] input.1.second input.1.secondTail)
      (.running { inputTape := Machine.PairPreparation.fromCells ((Machine.PairPreparation.interleave input.1.first input.1.second).map some ++ [none]) })))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun input => by
      simpa only [embedPreparation, Machine.PairPreparation.procedure, Procedure.ofFixed, PMF.pure_map] using
        (fresh_accept native code oracle saved state trace request
          (Machine.PairPreparation.operand [] input.1.first input.1.firstTail)
          (Machine.PairPreparation.operand [] input.1.second input.1.secondTail)
          (Machine.PairPreparation.fromCells ((Machine.PairPreparation.interleave input.1.first input.1.second).map some ++ [none]))))

noncomputable def preparationPrefix :=
  (preparation native code oracle saved state trace request).remember.seq
    (acceptance native code oracle saved state trace request) (fun _ _ _ => rfl)
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem preparationPrefix_budget (input : Machine.PairPreparation.Input) :
    (preparationPrefix native code oracle saved state trace request).budget input = 12 * input.first.length + 4 := by
  change (12 * input.first.length + 3) + 1 = _
  omega

theorem preparationPrefix_semantics (input : Machine.PairPreparation.Input) :
    (preparationPrefix native code oracle saved state trace request).semantics input = PMF.pure ((input, ()), ()) := by
  simp [preparationPrefix, preparation, acceptance, Procedure.seq, Procedure.remember, Procedure.liftBoundary,
    Machine.PairPreparation.procedure, Procedure.ofFixed, PMF.pure_map]

section Response
variable {Input : Type v} {Output : Type w}
    (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)
    (physical : Machine.PairPreparation.Input) (input : Input)
    (hEntry : P.execution.entry input = { inputTape := Machine.PairPreparation.fromCells ((Machine.PairPreparation.interleave physical.first physical.second).map some ++ [none]) })

/-- A native procedure starts from the buffer physically prepared by the controller.
The contract is closed over the actual operands and the suspended caller. -/
noncomputable def preparedResponse :=
  ((preparationPrefix P.code code oracle saved state trace request).reindex (fun _ : Unit => physical)).seq
    ((nativeResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap
      (Machine.PairPreparation.operand [] physical.first physical.firstTail)
      (Machine.PairPreparation.operand [] physical.second physical.secondTail)).reindex (fun _ => input))
    (fun start result hResult => by
      change result ∈ ((preparationPrefix P.code code oracle saved state trace request).semantics physical).support at hResult
      rw [preparationPrefix_semantics, PMF.mem_support_pure_iff] at hResult
      subst result
      simp only [preparationPrefix, acceptance, Procedure.seq, Procedure.reindex, Procedure.ofFixed,
        nativeResponse, rawBody, Procedure.remember, Procedure.liftBoundary, Procedure.frame,
        NativeCallback.exported, Function.comp_def]
      rw [hEntry]
      rfl)
    (fun _ => P.execution.budget input + 11 * cap input + 23)
    (fun _ _ _ => by
      simp only [Procedure.reindex, Function.comp_def]
      rw [nativeResponse_budget])

theorem preparedResponse_budget :
    (preparedResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap
      physical input hEntry).budget () =
      12 * physical.first.length + P.execution.budget input + 11 * cap input + 27 := by
  change (preparationPrefix P.code code oracle saved state trace request).budget physical + _ = _
  rw [preparationPrefix_budget]
  dsimp only
  omega

theorem preparedResponse_semantics :
    (preparedResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap
      physical input hEntry).semantics () =
      (PMF.pure ((physical, ()), ())).bind (fun previous =>
        (P.execution.semantics input).map (fun output => (previous, nativeResult input (encode output)))) := by
  simp only [preparedResponse, Procedure.seq, Procedure.reindex, Function.comp_def]
  rw [preparationPrefix_semantics, nativeResponse_semantics]
  simp only [PMF.map_comp, Function.comp_def]
theorem preparedResponse_distribution :
    ((preparedResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap
      physical input hEntry).costed ()).map
      (fun result => (preparedResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap
        physical input hEntry).exit () result.1) =
      (P.execution.semantics input).map (fun output => .source true
        (Machine.PairPreparation.operand [] physical.first physical.firstTail)
        (NativeCallback.resumed saved state trace request (true :: encode output))) := by
  have h := congrArg (fun distribution => distribution.map
    ((preparedResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap
      physical input hEntry).exit ()))
    ((preparedResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap
      physical input hEntry).correct ())
  rw [preparedResponse_semantics] at h
  simp only [PMF.pure_bind, PMF.map_comp, Function.comp_def] at h
  exact h
end Response

end CryptoOracle.Interactive.OneUseSource
