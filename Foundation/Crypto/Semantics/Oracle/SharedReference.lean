import Foundation.Crypto.Semantics.Oracle.QueryMap

/-! References to ONE live oracle authority. Copying a reference does not copy
State. Every service call receives the updated State of the preceding call.
This is a typed symbolic interface, not a heap allocator or native pointer
implementation. Erasing reference annotations gives the exact original
program, including its adaptive continuations and local coins. -/
namespace CryptoOracle.SharedReference
open Foundation.Probability

inductive Ref where
  | root
  deriving DecidableEq, Repr

variable {Input Response Result State : Type}

noncomputable def service (world : Oracle Input Response State) : Oracle (Ref × Input) Response State :=
  fun state request => world state request.2

def borrow (route : Nat → Ref) : Nat → Program Input Response Result → Program (Ref × Input) Response Result
  | _, .done result => .done result
  | position, .coin next => .coin (fun bit => borrow route position (next bit))
  | position, .query input next => .query (route position, input)
      (fun response => borrow route (position + 1) (next response))

theorem erase_borrow (route : Nat → Ref) (position : Nat) (program : Program Input Response Result) :
    (borrow route position program).mapQueries Prod.snd id = program := by
  induction program generalizing position with
  | done => rfl
  | coin next ih => simp only [borrow, Program.mapQueries]; congr 1; funext bit; exact ih bit position
  | query input next ih => simp only [borrow, Program.mapQueries]; congr 1; funext response; exact ih response (position + 1)

theorem borrowed_bound (route : Nat → Ref) (position : Nat)
    {program : Program Input Response Result} {bound : Nat} (bounded : program.BoundedQueries bound) :
    (borrow route position program).BoundedQueries bound := by
  induction bounded generalizing position with
  | done result bound => exact .done _ _
  | coin next bound bounded ih => exact .coin _ _ (fun bit => ih bit position)
  | query input next bound bounded ih => exact .query _ _ _ (fun response => ih response (position + 1))

theorem run_erase (route : Nat → Ref) (position : Nat) (program : Program Input Response Result)
    (world : Oracle Input Response State) (state : State) :
    ((borrow route position program).run (service world) state).map (Program.mapTranscript Prod.snd id) =
      program.run world state := by
  have adapter : Program.adaptOracle (Prod.snd : Ref × Input → Input) id world = service world := by
    funext saved request
    simp only [Program.adaptOracle, service, id_eq]
    change (world saved request.2).map id = _
    exact PMF.map_id _
  have simulation := Program.mapQueries_run (Prod.snd : Ref × Input → Input) id
    (borrow route position program) world state
  rw [erase_borrow, adapter] at simulation
  have identity (out : Outcome Input Response Result State) : Program.mapTranscript id id out = out := by
    cases out
    simp [Program.mapTranscript]
  simpa only [show Program.mapTranscript (Result := Result) (State := State)
      (id : Input → Input) (id : Response → Response) = id from funext identity, PMF.map_id] using simulation.symm

/-- Execute through the shared authority and retain physical input/response
traces, rather than counting reference names as extra oracle requests. -/
noncomputable def run (route : Nat → Ref) (program : Program Input Response Result)
    (world : Oracle Input Response State) (state : State) : PMF (Outcome Input Response Result State) :=
  ((borrow route 0 program).run (service world) state).map (Program.mapTranscript Prod.snd id)

theorem run_eq (route : Nat → Ref) (program : Program Input Response Result)
    (world : Oracle Input Response State) (state : State) : run route program world state = program.run world state :=
  run_erase route 0 program world state

end CryptoOracle.SharedReference
