import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedResponse
import Foundation.Crypto.Semantics.Oracle.Reification

/-! Concrete privacy-reduction controller around a finite source code.
The source VM owns only its original two tapes. Private generation and
authentication have separate frames. Ciphertext decoding examines at most
two cells; response rewind, collection, reversal, loading and source resumption
each use explicit cell-level transitions. Tape.bits is an observation only. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
open Machine Foundation.Probability
namespace Source
abbrev Control := CryptoOracle.Interactive.Control
abbrev Code := CryptoOracle.Interactive.Code
end Source
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

inductive Control where
  | initializing : Source.Control → PrivateKeyGeneration.Control → Control
  | source : Tape → Source.Control → Control
  | responding : Configuration → List Bool → ResponseHandoff.Control → Control
  | rewinding : Tape → Configuration → List Bool → Tape → Control
  | collecting : Tape → Configuration → List Bool → Tape → List Bool → Control
  | reversing : Tape → Configuration → List Bool → List Bool → List Bool → Control
  deriving DecidableEq, Repr

structure Frame (State : Type u) where
  state : State
  control : Control
  sourceTrace : List (List Bool × List Bool) := []
  externalTrace : List (List Bool × List Bool) := []

def initial {State : Type u} (state : State) (markers sourceInput : List Bool) : Frame State :=
  ⟨state, .initializing (.running (Configuration.initial sourceInput))
    (PrivateKeyGeneration.initial markers), [], []⟩

def decodeCiphertext : List Bool → Option Bool
  | true :: bit :: _ => some bit
  | _ => none

def terminal : Control → Bool
  | .source _ source => CryptoOracle.Interactive.Reification.terminal source
  | _ => false

/-- Only source-machine output is the attacker's final public result.
Private key generation and signing input frames are absent from this view. -/
def publicPacket : Control → Option (List Bool)
  | .source _ source => CryptoOracle.Interactive.Reification.packet source
  | _ => none

/-- Constant-size completion test and tape ownership transfer. It does not
compute the native output bitstring as part of a machine transition. -/
def responseOutput : ResponseHandoff.Control → Option (Tape × Tape)
  | .authenticating key machine => if machine.halted then some (key, machine.outputTape) else none
  | _ => none

noncomputable def step {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (frame : Frame State) : PMF (Frame State) :=
  match frame.control with
  | .initializing source generator =>
      match PrivateKeyGeneration.readyStore generator with
      | some key => PMF.pure { frame with control := .source key source }
      | none => (PrivateKeyGeneration.step generator).map fun next =>
          { frame with control := .initializing source next }
  | .source key source =>
      if CryptoOracle.Interactive.Reification.terminal source then PMF.pure frame
      else
        match CryptoOracle.Interactive.Reification.action code source with
        | .deterministic next => PMF.pure { frame with control := .source key next.control }
        | .random zero one => sampleBit.map fun bit =>
            { frame with control := .source key (if bit then one.control else zero.control) }
        | .oracleCall machine request => (oracle frame.state request).map fun answer =>
            { frame with
              state := answer.1
              control := .responding machine request (.headerWriting key (ResponseHandoff.header (decodeCiphertext answer.2)) {})
              externalTrace := (request, answer.2) :: frame.externalTrace }
  | .responding machine request responder =>
      match responseOutput responder with
      | some (key, output) => PMF.pure { frame with control := .rewinding key machine request output }
      | none => (ResponseHandoff.step responder).map fun next =>
          { frame with control := .responding machine request next }
  | .rewinding key machine request tape =>
      match tape.left with
      | [] => PMF.pure { frame with control := .collecting key machine request tape [] }
      | _ :: _ => PMF.pure { frame with control := .rewinding key machine request tape.moveLeft }
  | .collecting key machine request tape reversed =>
      match tape.current with
      | some bit => PMF.pure { frame with control := .collecting key machine request tape.moveRight (bit :: reversed) }
      | none => PMF.pure { frame with control := .reversing key machine request reversed [] }
  | .reversing key machine request remaining response =>
      match remaining with
      | bit :: rest => PMF.pure { frame with control := .reversing key machine request rest (bit :: response) }
      | [] => PMF.pure { frame with
          control := .source key (.loading machine response {}),
          sourceTrace := (request, response) :: frame.sourceTrace }

noncomputable def eval {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) : Nat → Frame State → PMF (Frame State)
  | 0, start => PMF.pure start
  | fuel + 1, start => (step code oracle start).bind (eval code oracle fuel)

theorem eval_add {State : Type u} (code : Source.Code) (oracle : CryptoOracle.Interactive.BitOracle State)
    (first second : Nat) (start : Frame State) :
    eval code oracle (first + second) start =
      (eval code oracle first start).bind (eval code oracle second) := by
  induction first generalizing start with
  | zero => simp [eval, PMF.pure_bind]
  | succ first ih =>
      simp only [Nat.succ_add, eval, PMF.bind_bind]
      congr 1
      funext next
      exact ih next

/-- A source transition selects its instruction using only the source
control. Private key cells, external oracle state and traces are not inputs. -/
theorem source_deterministic {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : Tape) (source : Source.Control)
    (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (next : CryptoOracle.Interactive.Configuration Unit)
    (hRunning : CryptoOracle.Interactive.Reification.terminal source = false)
    (hNext : CryptoOracle.Interactive.Reification.action code source = .deterministic next) :
    step code oracle ⟨state, .source key source, sourceTrace, externalTrace⟩ =
      PMF.pure ⟨state, .source key next.control, sourceTrace, externalTrace⟩ := by
  simp [step, hRunning, hNext]

theorem source_random {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : Tape) (source : Source.Control)
    (state : State) (sourceTrace externalTrace : List (List Bool × List Bool))
    (zero one : CryptoOracle.Interactive.Configuration Unit)
    (hRunning : CryptoOracle.Interactive.Reification.terminal source = false)
    (hNext : CryptoOracle.Interactive.Reification.action code source = .random zero one) :
    step code oracle ⟨state, .source key source, sourceTrace, externalTrace⟩ =
      sampleBit.map (fun bit => ⟨state, .source key (if bit then one.control else zero.control), sourceTrace, externalTrace⟩) := by
  simp [step, hRunning, hNext]

/-- After collecting an authenticated response, only the response becomes a
new public output tape. The suspended source configuration, including its
input/work tape, is resumed unchanged by the private authentication frame. -/
theorem source_resume {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : Tape) (machine : Configuration)
    (request response : List Bool) (state : State) (sourceTrace externalTrace : List (List Bool × List Bool)) :
    step code oracle ⟨state, .reversing key machine request [] response, sourceTrace, externalTrace⟩ =
      PMF.pure ⟨state, .source key (.loading machine response {}), (request, response) :: sourceTrace, externalTrace⟩ := by
  rfl

theorem reversing_run {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : Tape) (machine : Configuration)
    (request remaining response : List Bool) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    eval code oracle (remaining.length + 1)
      ⟨state, .reversing key machine request remaining response, sourceTrace, externalTrace⟩ =
      PMF.pure ⟨state, .source key (.loading machine (remaining.reverse ++ response) {}),
        (request, remaining.reverse ++ response) :: sourceTrace, externalTrace⟩ := by
  induction remaining generalizing response with
  | nil => simp [eval, step]
  | cons bit remaining ih =>
      rw [List.length_cons, eval]
      simp only [step, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

def buffer (before : List (Option Bool)) (remaining : List Bool) : Tape :=
  { ResponseHandoff.fromCells (remaining.map some ++ [none]) with left := before }

theorem collecting_run {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : Tape) (machine : Configuration)
    (request remaining reversed : List Bool) (before : List (Option Bool)) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    eval code oracle (remaining.length + 1)
      ⟨state, .collecting key machine request (buffer before remaining) reversed, sourceTrace, externalTrace⟩ =
      PMF.pure ⟨state, .reversing key machine request (remaining.reverse ++ reversed) [], sourceTrace, externalTrace⟩ := by
  induction remaining generalizing before reversed with
  | nil => simp [eval, step, buffer, ResponseHandoff.fromCells]
  | cons bit remaining ih =>
      rw [List.length_cons, eval]
      simp only [step, buffer, ResponseHandoff.fromCells, List.map_cons, List.cons_append,
        List.headD_cons, List.tail_cons, PMF.pure_bind]
      have hMove : ({ left := before, current := some bit, right := remaining.map some ++ [none] } : Tape).moveRight =
          buffer (some bit :: before) remaining := by
        cases remaining <;> rfl
      rw [hMove, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem rewinding_run {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : Tape) (machine : Configuration)
    (request left : List Bool) (current : Option Bool) (right : List (Option Bool)) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    eval code oracle (left.length + 1)
      ⟨state, .rewinding key machine request ⟨left.map some, current, right⟩, sourceTrace, externalTrace⟩ =
      PMF.pure ⟨state, .collecting key machine request
        (ResponseHandoff.fromCells (left.reverse.map some ++ current :: right)) [], sourceTrace, externalTrace⟩ := by
  induction left generalizing current right with
  | nil => simp [eval, step, ResponseHandoff.fromCells]
  | cons bit left ih =>
      rw [List.length_cons, eval]
      simp only [step, List.map_cons, Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Return a signed native output without a whole-string read at unit cost.
All three traversals and all stage transitions are included in the bound. -/
theorem return_response_run {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : Tape) (machine : Configuration)
    (request response : List Bool) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    eval code oracle (3 * response.length + 3)
      ⟨state, .rewinding key machine request { left := response.reverse.map some }, sourceTrace, externalTrace⟩ =
      PMF.pure ⟨state, .source key (.loading machine response {}), (request, response) :: sourceTrace, externalTrace⟩ := by
  rw [show 3 * response.length + 3 = (response.reverse.length + 1) +
      ((response.length + 1) + (response.reverse.length + 1)) by simp; omega,
    eval_add, rewinding_run, PMF.pure_bind]
  simp only [List.reverse_reverse]
  change eval code oracle _ ⟨state, .collecting key machine request (buffer [] response) [], sourceTrace, externalTrace⟩ = _
  rw [eval_add, collecting_run, PMF.pure_bind]
  simp only [List.append_nil]
  rw [reversing_run]
  simp

/-- A failed authentication response halts with its sole bit under the head,
rather than at a blank after that bit. This actual layout skips one rewind
move; it is not silently replaced by the successful-response layout. -/
theorem return_single_response_run {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : Tape) (machine : Configuration)
    (request : List Bool) (bit : Bool) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool)) :
    eval code oracle 5
      ⟨state, .rewinding key machine request { current := some bit }, sourceTrace, externalTrace⟩ =
      PMF.pure ⟨state, .source key (.loading machine [bit] {}), (request, [bit]) :: sourceTrace, externalTrace⟩ := by
  simp [eval, step, Tape.moveRight]

theorem step_terminal {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (frame : Frame State)
    (h : terminal frame.control = true) : step code oracle frame = PMF.pure frame := by
  cases hc : frame.control <;> simp [terminal, hc] at h
  simp [step, hc, h]

def HaltsWithin {State : Type u} (code : Source.Code) (oracle : CryptoOracle.Interactive.BitOracle State)
    (start : Frame State) (fuel : Nat) : Prop :=
  ∀ final ∈ (eval code oracle fuel start).support, terminal final.control = true

theorem eval_terminal {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (fuel : Nat) (frame : Frame State)
    (h : terminal frame.control = true) : eval code oracle fuel frame = PMF.pure frame := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [eval, step_terminal code oracle frame h, PMF.pure_bind, ih]

theorem eval_stable {State : Type u} (code : Source.Code) (oracle : CryptoOracle.Interactive.BitOracle State)
    (start : Frame State) (fuel extra : Nat) (h : HaltsWithin code oracle start fuel) :
    eval code oracle (fuel + extra) start = eval code oracle fuel start := by
  rw [eval_add, ← PMF.bindOnSupport_eq_bind]
  calc
    (eval code oracle fuel start).bindOnSupport (fun final _ => eval code oracle extra final) =
        (eval code oracle fuel start).bindOnSupport (fun final _ => PMF.pure final) := by
      congr 1
      funext final hFinal
      exact eval_terminal code oracle extra final (h final hFinal)
    _ = eval code oracle fuel start := PMF.bindOnSupport_pure _

def simulateStep {State : Type u} (code : Source.Code)
    (oracle : State → List Bool → State × List Bool) (coin : Bool) (frame : Frame State) : Frame State :=
  match frame.control with
  | .initializing source generator =>
      match PrivateKeyGeneration.readyStore generator with
      | some key => { frame with control := .source key source }
      | none => { frame with control := .initializing source (PrivateKeyGeneration.simulateStep coin generator) }
  | .source key source =>
      if CryptoOracle.Interactive.Reification.terminal source then frame
      else
        match CryptoOracle.Interactive.Reification.action code source with
        | .deterministic next => { frame with control := .source key next.control }
        | .random zero one => { frame with control := .source key (if coin then one.control else zero.control) }
        | .oracleCall machine request =>
            let answer := oracle frame.state request
            { frame with
              state := answer.1
              control := .responding machine request (.headerWriting key (ResponseHandoff.header (decodeCiphertext answer.2)) {})
              externalTrace := (request, answer.2) :: frame.externalTrace }
  | .responding machine request responder =>
      match responseOutput responder with
      | some (key, output) => { frame with control := .rewinding key machine request output }
      | none => { frame with control := .responding machine request (ResponseHandoff.simulateStep responder) }
  | .rewinding key machine request tape =>
      match tape.left with
      | [] => { frame with control := .collecting key machine request tape [] }
      | _ :: _ => { frame with control := .rewinding key machine request tape.moveLeft }
  | .collecting key machine request tape reversed =>
      match tape.current with
      | some bit => { frame with control := .collecting key machine request tape.moveRight (bit :: reversed) }
      | none => { frame with control := .reversing key machine request reversed [] }
  | .reversing key machine request remaining response =>
      match remaining with
      | bit :: rest => { frame with control := .reversing key machine request rest (bit :: response) }
      | [] => { frame with control := .source key (.loading machine response {}), sourceTrace := (request, response) :: frame.sourceTrace }

theorem simulateStep_mem_support {State : Type u} (code : Source.Code)
    (oracle : State → List Bool → State × List Bool) (coin : Bool) (frame : Frame State) :
    simulateStep code oracle coin frame ∈ (step code (fun state request => PMF.pure (oracle state request)) frame).support := by
  cases hc : frame.control with
  | initializing source generator =>
      cases hg : PrivateKeyGeneration.readyStore generator with
      | none =>
          simp only [simulateStep, step, hc, hg, PMF.mem_support_map_iff]
          exact ⟨_, PrivateKeyGeneration.simulateStep_mem_support coin generator, rfl⟩
      | some key => simp [simulateStep, step, hc, hg]
  | source key source =>
      cases ht : CryptoOracle.Interactive.Reification.terminal source with
      | true => simp [simulateStep, step, hc, ht]
      | false =>
          cases ha : CryptoOracle.Interactive.Reification.action code source with
          | deterministic next => simp [simulateStep, step, hc, ht, ha]
          | random zero one =>
              simp only [simulateStep, step, hc, ht, ha, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff]
              exact ⟨coin, by simp [sampleBit, uniform], rfl⟩
          | oracleCall machine request => simp [simulateStep, step, hc, ht, ha, PMF.pure_map]
  | responding machine request responder =>
      cases hr : responseOutput responder with
      | none =>
          simp only [simulateStep, step, hc, hr, PMF.mem_support_map_iff]
          exact ⟨_, ResponseHandoff.simulateStep_mem_support responder, rfl⟩
      | some result => cases result; simp [simulateStep, step, hc, hr]
  | rewinding key machine request tape =>
      cases hl : tape.left <;> simp [simulateStep, step, hc, hl]
  | collecting key machine request tape reversed =>
      cases ht : tape.current <;> simp [simulateStep, step, hc, ht]
  | reversing key machine request remaining response =>
      cases remaining <;> simp [simulateStep, step, hc]

def simulate {State : Type u} (code : Source.Code)
    (oracle : State → List Bool → State × List Bool) (coin : Bool) : Nat → Frame State → Frame State × Nat
  | 0, start => (start, 0)
  | fuel + 1, start =>
      if terminal start.control then (start, 0)
      else let result := simulate code oracle coin fuel (simulateStep code oracle coin start)
           (result.1, result.2 + 1)

theorem simulate_mem_support {State : Type u} (code : Source.Code)
    (oracle : State → List Bool → State × List Bool) (coin : Bool) (fuel : Nat) (start : Frame State) :
    (simulate code oracle coin fuel start).1 ∈
      (eval code (fun state request => PMF.pure (oracle state request)) fuel start).support := by
  induction fuel generalizing start with
  | zero => simp [simulate, eval]
  | succ fuel ih =>
      by_cases h : terminal start.control = true
      · rw [eval_terminal _ _ (fuel + 1) start h]
        simp [simulate, h]
      · simp only [simulate, h, eval, PMF.mem_support_bind_iff]
        exact ⟨simulateStep code oracle coin start, simulateStep_mem_support code oracle coin start, ih _⟩

end Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
