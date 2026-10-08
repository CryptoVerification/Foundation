import Foundation.Crypto.Semantics.Machine.PolynomialObserver
import Foundation.Crypto.Semantics.Machine.NativeHaltingProgram
import Foundation.Crypto.Semantics.Machine.TapeSwapProcedure

/-! Every fixed-code polynomial observer has a native component suitable
for physical linking, including empty programs and out-of-range control.
The wrapper preserves the observed head bit and adds two to the time bound.
Its actual first-halt time remains the time of the transformed program. -/
namespace Machine.PolynomialObserver
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
variable (O : PolynomialObserver)

theorem horizon_distribution (input : List Bool) :
    evalConfigWithin O.code (Configuration.initial input) (O.budget input.length) =
      (O.costed input).map Prod.fst := by
  have h := (Block.stopped (stepPMF O.code) Configuration.halted
    (O.budget input.length) (Configuration.initial input)).final_law
    (by
      intro result hResult
      have hHalt := O.costed_halted input result hResult
      simp [stepPMF, next, hHalt]) (O.budget input.length) (Nat.le_refl _)
  rw [timed_eval_eq] at h
  exact h

noncomputable def native : NativeComponent (List Bool) Configuration :=
  NativeHaltingProgram.component O.code Configuration.initial (fun input => O.budget input.length)
    (fun _ => rfl) (fun _ => rfl)
    (fun input state hState => O.halts input state ((mem_support_evalConfigWithin_iff _ _ _ _).mp hState))

theorem native_code : O.native.procedure.code = NativeHaltingProgram.code O.code := rfl

theorem native_budget (input : List Bool) : O.native.procedure.execution.budget input = O.budget input.length + 2 := rfl

theorem native_budget_polynomial : PolynomiallyBounded (fun size => O.budget size + 2) :=
  O.budget_polynomial.add (PolynomiallyBounded.const 2)

/-- Reading the designated cell after the actual wrapper reproduces the
original observer's decision distribution. No output decoder is inserted. -/
theorem native_observe (input : List Bool) :
    (O.native.procedure.execution.semantics input).map
      (fun state => (O.native.procedure.execution.exit input state).outputTape.current.getD false) =
      O.observe input := by
  change (evalConfigWithin O.code (Configuration.initial input) (O.budget input.length)).map
    (fun state => state.outputTape.current.getD false) = _
  rw [O.horizon_distribution, PMF.map_comp]
  rfl

theorem opposite_native_observe (input : List Bool) :
    (O.native.swapTapes.procedure.execution.semantics input).map
      (fun state => (O.native.swapTapes.procedure.execution.exit input state).inputTape.current.getD false) =
      O.observe input := O.native_observe input

end Machine.PolynomialObserver
