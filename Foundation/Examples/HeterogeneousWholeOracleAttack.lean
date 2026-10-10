import Foundation.Examples.WholeOracleAttack
import Foundation.Crypto.Logic.General.Backends

/-! A genuinely inhabited native whole-execution class with different opaque
state types. The original four-instruction adaptive code executes two queries
in both worlds; the right state is Unit and the left state is Nat. -/
namespace CryptoOracle.Examples.Heterogeneous

open Foundation.Probability Machine
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable def rightOracle : Oracle Bool Bool Unit := fun state _ => PMF.pure (state, false)

noncomputable def protocol : Protocol Bool Bool Nat Unit where
  Instance := fun _ => Unit
  games _ _ := ⟨countingOracle true, rightOracle, 0, ()⟩

def interface : WholeInterface protocol where
  instanceEncoding _ := FiniteBitEncoding.unit
  requestEncoding := FiniteBitEncoding.bool
  responseEncoding := FiniteBitEncoding.bool
  fallbackRequest := false

theorem right_typed_run : adaptive.run rightOracle () =
    PMF.pure (⟨false, (), [(false, false), (false, false)]⟩ : Outcome Bool Bool Bool Unit) := by
  simp [Program.run, adaptive, rightOracle, PMF.pure_map]

set_option maxRecDepth 10000 in
/-- The same four native instructions make two adaptive calls and finish
in 25 transitions on the Unit-state world. All transfer work is included. -/
theorem right_code_run (input : List Bool) :
    Interactive.eval adaptiveCode (interface.bitOracle rightOracle)
      (Interactive.Configuration.initial () input) 25 =
      PMF.pure (⟨(), .finished false,
        [([false], [false]), ([false], [false])]⟩ : Interactive.Configuration Unit) := by
  simp [Interactive.eval, Interactive.step, Interactive.transition, adaptiveCode,
    Interactive.Configuration.initial, Machine.Configuration.initial,
    interface, WholeInterface.bitOracle, rightOracle, FiniteBitEncoding.bool,
    Machine.Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance,
    Tape.write, Tape.moveRight, Tape.moveLeft, PMF.pure_map]

/-- No state embedding, reset, or separate code is used for the right world. -/
noncomputable def witness : WholeWitness interface (fun _ => 25) (fun _ => 2)
    (fun _ => ()) (fun _ => adaptive) where
  code := adaptiveCode
  halts := by
    intro n right
    cases right with
    | false =>
        intro finish reachable
        change finish ∈ (Interactive.eval adaptiveCode (wholeInterface.bitOracle (countingOracle true))
          (Interactive.Configuration.initial 0 (interface.input n ())) 25).support at reachable
        rw [adaptiveCode_run, PMF.mem_support_pure_iff] at reachable
        subst finish
        exact ⟨true, rfl⟩
    | true =>
        intro finish reachable
        change finish ∈ (Interactive.eval adaptiveCode (interface.bitOracle rightOracle)
          (Interactive.Configuration.initial () (interface.input n ())) 25).support at reachable
        rw [right_code_run, PMF.mem_support_pure_iff] at reachable
        subst finish
        exact ⟨false, rfl⟩
  queries := by
    intro n right
    cases right with
    | false =>
        intro finish reachable
        change finish ∈ (Interactive.eval adaptiveCode (wholeInterface.bitOracle (countingOracle true))
          (Interactive.Configuration.initial 0 (interface.input n ())) 25).support at reachable
        rw [adaptiveCode_run, PMF.mem_support_pure_iff] at reachable
        subst finish
        exact le_refl _
    | true =>
        intro finish reachable
        change finish ∈ (Interactive.eval adaptiveCode (interface.bitOracle rightOracle)
          (Interactive.Configuration.initial () (interface.input n ())) 25).support at reachable
        rw [right_code_run, PMF.mem_support_pure_iff] at reachable
        subst finish
        exact le_refl _
  realizes := by
    intro n right
    cases right with
    | false =>
        change (Interactive.eval adaptiveCode (wholeInterface.bitOracle (countingOracle true))
          (Interactive.Configuration.initial 0 (interface.input n ())) 25).map Interactive.observe =
            (adaptive.run (countingOracle true) 0).map interface.encodeOutcome
        rw [adaptiveCode_run, adaptive_left_run]
        simp [PMF.pure_map, Interactive.observe, Interactive.Configuration.result,
          WholeInterface.encodeOutcome, interface, FiniteBitEncoding.bool]
    | true =>
        change (Interactive.eval adaptiveCode (interface.bitOracle rightOracle)
          (Interactive.Configuration.initial () (interface.input n ())) 25).map Interactive.observe =
            (adaptive.run rightOracle ()).map interface.encodeOutcome
        rw [right_code_run, right_typed_run]
        simp [PMF.pure_map, Interactive.observe, Interactive.Configuration.result,
          WholeInterface.encodeOutcome, interface, FiniteBitEncoding.bool]

/-- The generalized common backend retains exactly the original emitted code. -/
theorem backend_code : (CryptoLogic.General.Backends.Interactive.witness witness).code = adaptiveCode := rfl

example : (wholeClass interface (fun _ => 25) (fun _ => 2)).admissible
    (fun _ => ()) (fun _ => adaptive) := ⟨witness⟩

end CryptoOracle.Examples.Heterogeneous
