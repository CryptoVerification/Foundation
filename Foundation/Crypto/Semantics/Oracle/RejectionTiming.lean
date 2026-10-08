import Foundation.Crypto.Semantics.Machine.PreparationShape
import Foundation.Crypto.Semantics.Oracle.OneUseRejection
import Foundation.Crypto.Semantics.Oracle.OneUseInvocation

/-! Invalid-length rejection timing is independent of operand bit values.
The first-return distribution retains the actual cost, including physical
restoration and failure writing. Equal tape shapes are explicit hypotheses. -/
namespace CryptoOracle.Interactive.RejectionTiming
open Foundation.Probability TimedExecution
open Machine.PreparationShape
universe u

theorem boundary_shape (start : Machine.PreparationCheck.Control) :
    FailureCallback.boundary (check start) = FailureCallback.boundary start := by
  cases start with
  | preparing phase => cases phase <;> rfl
  | failure phase => cases phase <;> rfl

theorem stopped_shape (fuel : Nat) (start : Machine.PreparationCheck.Control) :
    runToBoundary Machine.PreparationCheck.step FailureCallback.boundary fuel (check start) =
      (runToBoundary Machine.PreparationCheck.step FailureCallback.boundary fuel start).map
        (fun result => (check result.1, result.2)) :=
  runToBoundary_map _ _ _ _ check boundary_shape (fun start _ => check_step start) fuel start

noncomputable def costs (fuel : Nat) (start : Machine.PreparationCheck.Control) : PMF (Unit × Nat) :=
  (runToBoundary Machine.PreparationCheck.step FailureCallback.boundary fuel start).map
    (fun result => ((), result.2))

theorem costs_shape (fuel : Nat) (start : Machine.PreparationCheck.Control) :
    costs fuel start = costs fuel (check start) := by
  unfold costs
  rw [stopped_shape, PMF.map_comp]
  rfl

def initial (input : Machine.PreparationCheck.FailureInput) : Machine.PreparationCheck.Control :=
  .preparing (.reading (Machine.PairPreparation.operand [] input.first input.firstTail)
    (Machine.PairPreparation.operand [] input.second input.secondTail) {})

theorem initial_shape (first second : Machine.PreparationCheck.FailureInput)
    (hFirst : first.first.length = second.first.length)
    (hSecond : first.second.length = second.second.length)
    (hFirstTail : first.firstTail.map cell = second.firstTail.map cell)
    (hSecondTail : first.secondTail.map cell = second.secondTail.map cell) :
    check (initial first) = check (initial second) := by
  simp only [initial, check, preparation, operand_shape]
  rw [hFirst, hSecond, hFirstTail, hSecondTail]

/-- The actual costed contract for physical rejection preparation. The
native program, caller code, opaque state and trace are all unrestricted. -/
theorem preparation_cost_independence {State : Type u}
    (firstNative secondNative : Machine.Program) (firstCode secondCode : Code)
    (firstOracle secondOracle : BitOracle State) (firstSaved secondSaved : Machine.Configuration)
    (firstState secondState : State) (firstTrace secondTrace : List (List Bool × List Bool))
    (firstRequest secondRequest : List Bool) (first second : Machine.PreparationCheck.FailureInput)
    (hFirst : first.first.length = second.first.length)
    (hSecond : first.second.length = second.second.length)
    (hFirstTail : first.firstTail.map cell = second.firstTail.map cell)
    (hSecondTail : first.secondTail.map cell = second.secondTail.map cell) :
    (OneUseRejection.preparation firstNative firstCode firstOracle firstSaved firstState firstTrace firstRequest first).costed () =
      (OneUseRejection.preparation secondNative secondCode secondOracle secondSaved secondState secondTrace secondRequest second).costed () := by
  change costs (12 * Machine.PreparationCheck.consumed first + 10) (initial first) =
    costs (12 * Machine.PreparationCheck.consumed second + 10) (initial second)
  have hFuel : Machine.PreparationCheck.consumed first = Machine.PreparationCheck.consumed second := by
    simp only [Machine.PreparationCheck.consumed, hFirst, hSecond]
  calc
    _ = costs (12 * Machine.PreparationCheck.consumed first + 10) (check (initial first)) := costs_shape _ _
    _ = costs (12 * Machine.PreparationCheck.consumed second + 10) (check (initial second)) := by
      rw [initial_shape first second hFirst hSecond hFirstTail hSecondTail, hFuel]
    _ = _ := (costs_shape _ _).symm

end CryptoOracle.Interactive.RejectionTiming

namespace CryptoOracle.Interactive.RejectionTiming
open Foundation.Probability TimedExecution
universe u
set_option maxRecDepth 2048

theorem failure_delivery_cost {State : Type u} (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (first second : Machine.Tape) :
    (OneUseDelivery.packetDelivery native code oracle false saved state trace request first second).costed [false] =
      PMF.pure (([false], ()), 14) := by
  simp [OneUseDelivery.packetDelivery, OneUseDelivery.packetBody, OneUseDelivery.reply,
    OneUseDelivery.packetReady, OneUseDelivery.packetMachine, NativeCallback.exported,
    NativeCallback.exportBoundary, NativeCallback.packetRead, Machine.Procedure.ofFixed,
    Procedure.seq, Procedure.reindex, Procedure.liftBoundary, Procedure.frame, Procedure.ofFixed,
    runToBoundary, framedStep, Machine.ResponseExport.step, Machine.ResponseExport.endTape,
    Machine.Tape.moveLeft, Machine.Tape.moveRight, PMF.pure_map, PMF.pure_bind]

theorem whole_costs {State : Type u} (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (input : Machine.PreparationCheck.FailureInput) :
    (OneUseRejection.whole native code oracle saved state trace request input).costed () =
      (costs (12 * Machine.PreparationCheck.consumed input + 10) (initial input)).map
        (fun result => ((((), ()), ([false], ())), result.2 + 15)) := by
  simp only [OneUseRejection.whole, Procedure.seq, Procedure.reindex,
    OneUseRejection.handoff, Procedure.ofFixed, Function.comp_def, failure_delivery_cost, PMF.pure_map]
  change ((costs (12 * Machine.PreparationCheck.consumed input + 10) (initial input)).bind
    fun middle => PMF.pure ((middle.1, ()), middle.2 + 1)).bind
      (fun middle => PMF.pure ((middle.1, ([false], ())), middle.2 + 14)) = _
  rw [PMF.bind_bind, PMF.map]
  congr 1
  funext result
  rcases result with ⟨value, cost⟩
  cases value
  simp [PMF.pure_bind, Nat.add_assoc]

theorem whole_cost_independence {State : Type u}
    (firstNative secondNative : Machine.Program) (firstCode secondCode : Code)
    (firstOracle secondOracle : BitOracle State) (firstSaved secondSaved : Machine.Configuration)
    (firstState secondState : State) (firstTrace secondTrace : List (List Bool × List Bool))
    (firstRequest secondRequest : List Bool) (first second : Machine.PreparationCheck.FailureInput)
    (hFirst : first.first.length = second.first.length)
    (hSecond : first.second.length = second.second.length)
    (hFirstTail : first.firstTail.map Machine.PreparationShape.cell = second.firstTail.map Machine.PreparationShape.cell)
    (hSecondTail : first.secondTail.map Machine.PreparationShape.cell = second.secondTail.map Machine.PreparationShape.cell) :
    (OneUseRejection.whole firstNative firstCode firstOracle firstSaved firstState firstTrace firstRequest first).costed () =
      (OneUseRejection.whole secondNative secondCode secondOracle secondSaved secondState secondTrace secondRequest second).costed () := by
  have hp := preparation_cost_independence firstNative secondNative firstCode secondCode firstOracle secondOracle
    firstSaved secondSaved firstState secondState firstTrace secondTrace firstRequest secondRequest
    first second hFirst hSecond hFirstTail hSecondTail
  change costs (12 * Machine.PreparationCheck.consumed first + 10) (initial first) =
    costs (12 * Machine.PreparationCheck.consumed second + 10) (initial second) at hp
  rw [whole_costs, whole_costs, hp]

def publicExit {State : Type u} : OneUseSource.Control State → Option (Configuration State)
  | .source _ _ frame => some frame
  | _ => none

noncomputable def publicReturn {State : Type u} (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (input : Machine.PreparationCheck.FailureInput) : PMF (Option (Configuration State) × Nat) :=
  ((OneUseRejection.whole native code oracle saved state trace request input).costed ()).map
    (fun result => (publicExit ((OneUseRejection.whole native code oracle saved state trace request input).exit () result.1), result.2))

/-- Joint public return configuration and actual cost, not just the reply bit.
Equal key length and erased tails suffice; private key contents may differ. -/
theorem public_return_independence {State : Type u}
    (firstNative secondNative : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (request : List Bool) (first second : Machine.PreparationCheck.FailureInput)
    (hFirst : first.first.length = second.first.length)
    (hSecond : first.second.length = second.second.length)
    (hFirstTail : first.firstTail.map Machine.PreparationShape.cell = second.firstTail.map Machine.PreparationShape.cell)
    (hSecondTail : first.secondTail.map Machine.PreparationShape.cell = second.secondTail.map Machine.PreparationShape.cell) :
    publicReturn firstNative code oracle saved state trace request first =
      publicReturn secondNative code oracle saved state trace request second := by
  have hp := whole_cost_independence firstNative secondNative code code oracle oracle saved saved state state
    trace trace request request first second hFirst hSecond hFirstTail hSecondTail
  unfold publicReturn
  rw [hp]
  rfl

theorem rejected_invocation_costs {State : Type u} (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call) (input : Machine.PreparationCheck.FailureInput)
    (hTape : machine.outputTape = RequestExport.packetTape [] input.secondTail input.second) :
    ((OneUseSource.rejectedInvocation native code oracle machine state trace hActive hCall input hTape).costed ()).map
      (fun result => (publicExit ((OneUseSource.rejectedInvocation native code oracle machine state trace hActive hCall input hTape).exit () result.1), result.2)) =
      (costs (12 * Machine.PreparationCheck.consumed input + 10) (initial input)).map
        (fun result => (some (NativeCallback.resumed machine.advance state trace input.second [false]),
          2 * input.second.length + result.2 + 19)) := by
  simp only [OneUseSource.rejectedInvocation, OneUseSource.invocation, OneUseSource.capture,
    Procedure.seq, Procedure.reindex, Procedure.ofFixed, Function.comp_def, PMF.pure_map,
    PMF.pure_bind, whole_costs, PMF.map_comp]
  congr 1
  funext result
  simp [publicExit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rfl

/-- The key label retained in a joint-distribution argument agrees with
the actual private tape restored by the runtime; the use flag remains false. -/
theorem rejected_invocation_retains_key {State : Type u} (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call) (input : Machine.PreparationCheck.FailureInput)
    (hTape : machine.outputTape = RequestExport.packetTape [] input.secondTail input.second)
    (result : _ × Nat)
    (h : result ∈ ((OneUseSource.rejectedInvocation native code oracle machine state trace hActive hCall input hTape).costed ()).support) :
    (OneUseSource.rejectedInvocation native code oracle machine state trace hActive hCall input hTape).exit () result.1 =
      .source false (Machine.PairPreparation.operand [] input.first input.firstTail)
        (NativeCallback.resumed machine.advance state trace input.second [false]) := by
  have hm : (OneUseSource.rejectedInvocation native code oracle machine state trace hActive hCall input hTape).exit () result.1 ∈
      (((OneUseSource.rejectedInvocation native code oracle machine state trace hActive hCall input hTape).costed ()).map
        (fun result => (OneUseSource.rejectedInvocation native code oracle machine state trace hActive hCall input hTape).exit () result.1)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, h, rfl⟩
  rw [OneUseSource.rejectedInvocation_distribution, PMF.mem_support_pure_iff] at hm
  exact hm

end CryptoOracle.Interactive.RejectionTiming
