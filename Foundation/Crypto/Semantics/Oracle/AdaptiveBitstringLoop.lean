import Foundation.Crypto.Semantics.Oracle.QueryTransfer
import Foundation.Crypto.Semantics.ProcedureFixedContinuation
import Foundation.Crypto.Semantics.ProcedureDispatch
import Foundation.Crypto.Semantics.ProcedureCompletion

/-! One fixed five-instruction oracle caller makes a public unary-bounded
number of adaptive bitstring queries. Every response becomes the next actual
request. Request export, query, response loading and rewind are all charged.
This generalizes the Boolean-only loop without specializing code to lengths
or query counts; opaque oracle state and complete transcript are preserved. -/
namespace CryptoOracle.Interactive.AdaptiveBitstringLoop
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def code : Code :=
  [.native (.branch .input 4 4 1), .native (.moveRight .input), .call, .native (.jump 0), .native .halt]

def machine (remaining : Nat) (past : List (Option Bool)) (request : List Bool) : Machine.Configuration :=
  {inputTape := { (Tape.ofBits (List.replicate remaining true)) with left := past },
   outputTape := ResponseLoading.loaded request}

def frame {State : Type u} (state : State) (remaining : Nat) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) : Configuration State :=
  ⟨state, .running (machine remaining past request), trace⟩

def callMachine (remaining : Nat) (past : List (Option Bool)) (request : List Bool) : Machine.Configuration :=
  { machine remaining (some true :: past) request with pc := 2 }

variable {State : Type u} (oracle : BitOracle State) (state : State)
    (remaining : Nat) (past : List (Option Bool)) (request : List Bool) (trace : List (List Bool × List Bool))
    (cap : Nat) (hResponse : ∀ state request answer, answer ∈ (oracle state request).support → answer.2.length ≤ cap)

noncomputable def prepareRound : Procedure (Reification.timedStep code oracle) Unit Unit :=
  Procedure.ofFixed (Reification.timedStep code oracle)
    (fun _ => frame state (remaining + 1) past request trace)
    (fun _ _ => ⟨state, .running (callMachine remaining past request), trace⟩)
    (fun _ => PMF.pure ()) (fun _ => 2) (fun _ => by
      cases remaining <;> simp [TimedExecution.eval, frame, machine, callMachine, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, code, Machine.Instruction.next,
        Machine.Configuration.tape, Machine.Configuration.updateTape, Machine.Configuration.advance,
        Tape.ofBits, Tape.moveRight, List.replicate_succ, PMF.pure_map])

noncomputable def exchange : Procedure (Reification.timedStep code oracle) Unit (State × List Bool) where
  entry := fun _ => ⟨state, .running (callMachine remaining past request), trace⟩
  exit := fun _ answer => QueryTransfer.resumed (callMachine remaining past request).advance trace request answer
  semantics := fun _ => oracle state request
  costed := fun _ => (oracle state request).map (fun answer => (answer, 2 * request.length + 3 * answer.2.length + 6))
  budget := fun _ => 2 * request.length + 3 * cap + 6
  bounded := by
    intro _ result hs
    rw [PMF.mem_support_map_iff] at hs
    obtain ⟨answer, hs, rfl⟩ := hs
    have h := hResponse state request answer hs
    dsimp
    omega
  correct := fun _ => by simp only [PMF.map_comp, Function.comp_def]; exact PMF.map_id _
  law := by
    intro _ horizon hTime
    have h := (QueryTransfer.fullStage code oracle (callMachine remaining past request) state trace request [] []
      rfl rfl (by rfl) cap (hResponse state request)).law horizon (by
        change (2 * request.length + 3) + (3 * cap + 3) ≤ horizon
        omega)
    have hCost (answer : State × List Bool) :
        (2 * request.length + 3) + (3 * answer.2.length + 3) = 2 * request.length + 3 * answer.2.length + 6 := by omega
    simpa only [QueryTransfer.fullStage, QueryTransfer.stage, PMF.bind_map, PMF.map_comp, Function.comp_def,
      id_eq, hCost] using h

noncomputable def suffix : Procedure (Reification.timedStep code oracle) (State × List Bool) Unit :=
  Procedure.ofFixed (Reification.timedStep code oracle)
    (fun answer => QueryTransfer.resumed (callMachine remaining past request).advance trace request answer)
    (fun answer _ => frame answer.1 remaining (some true :: past) answer.2 ((request, answer.2) :: trace))
    (fun _ => PMF.pure ()) (fun _ => 1) (fun answer => by
      simp [TimedExecution.eval, QueryTransfer.resumed, frame, callMachine, machine, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, code, Machine.Instruction.next,
        Machine.Configuration.advance, PMF.pure_map])

noncomputable def round : Procedure (Reification.timedStep code oracle) Unit (State × List Bool) :=
  let first := (prepareRound oracle state remaining past request trace).andThen
    (exchange oracle state remaining past request trace cap hResponse) (fun _ _ _ => rfl)
  let both := first.seq (suffix oracle remaining past request trace) (fun _ _ _ => rfl)
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)
  both.observe Prod.fst
    (fun _ answer => frame answer.1 remaining (some true :: past) answer.2 ((request, answer.2) :: trace))
    (fun _ _ _ => rfl)

theorem round_entry : (round oracle state remaining past request trace cap hResponse).entry () =
    frame state (remaining + 1) past request trace := rfl

theorem round_exit (answer : State × List Bool) :
    (round oracle state remaining past request trace cap hResponse).exit () answer =
      frame answer.1 remaining (some true :: past) answer.2 ((request, answer.2) :: trace) := rfl

theorem round_budget : (round oracle state remaining past request trace cap hResponse).budget () =
    2 * request.length + 3 * cap + 9 := by
  change 2 + (2 * request.length + 3 * cap + 6) + 1 = _
  omega

theorem round_semantics : (round oracle state remaining past request trace cap hResponse).semantics () = oracle state request := by
  simp only [round, Procedure.observe, Procedure.seq, Procedure.andThen_semantics]
  change ((oracle state request).bind (fun answer => (PMF.pure ()).map (fun output => (answer, output)))).map Prod.fst = _
  simp only [PMF.map_bind, PMF.pure_map, PMF.bind_pure]

end CryptoOracle.Interactive.AdaptiveBitstringLoop
