import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityPreparation
import Foundation.Crypto.Semantics.Oracle.Reification

/-! Concrete native integrity-reduction controller. Private key generation
and encryption use the proved finite primitives. Only successful ciphertexts
invoke the external signing capability. Header construction, tag copying,
rewinding, collection, reversal and source resumption are charged transitions.
The source action never receives the private key, state, or signing history. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability
abbrev SourceCode := CryptoOracle.Interactive.Code
abbrev SourceControl := CryptoOracle.Interactive.Control

inductive Control where
  | initializing : SourceControl → Configuration → Control
  | source : Bool → Bool → SourceControl → Control
  | encrypting : Bool → Bool → Configuration → List Bool → IntegrityPreparation.Control → Control
  | failure : Bool → Configuration → List Bool → Control
  | header : Bool → Configuration → List Bool → Bool → List Bool → Nat → Tape → Control
  | copying : Bool → Configuration → List Bool → List Bool → Tape → Control
  | advancing : Bool → Configuration → List Bool → List Bool → Tape → Control
  | rewinding : Bool → Configuration → List Bool → Tape → Control
  | collecting : Bool → Configuration → List Bool → Tape → List Bool → Control
  | reversing : Bool → Configuration → List Bool → List Bool → List Bool → Control
  deriving DecidableEq, Repr

structure Frame (State : Type u) where
  state : State
  control : Control
  sourceTrace : List (List Bool × List Bool) := []
  signingTrace : List (Bool × List Bool) := []

def initial (state : State) (input : List Bool) : Frame State :=
  ⟨state, .initializing (.running (Configuration.initial input)) (Configuration.initial []), [], []⟩

def terminal : Control → Bool
  | .source _ _ source => CryptoOracle.Interactive.Reification.terminal source
  | _ => false

def publicPacket : Control → Option (List Bool)
  | .source _ _ source => CryptoOracle.Interactive.Reification.packet source
  | _ => none

inductive Action (State : Type u) where
  | deterministic : Frame State → Action State
  | random : Frame State → Frame State → Action State
  | sign : Bool → (State × List Bool → Frame State) → Action State

/-- Interpret a native instruction without adding a host-language sampler. -/
def nativeAction (code : Program) (machine : Configuration)
    (embed : Configuration → Frame State) : Action State :=
  match next code machine with
  | none => .deterministic (embed machine)
  | some (.inl nextMachine) => .deterministic (embed nextMachine)
  | some (.inr (zero, one)) => .random (embed zero) (embed one)

def transition (code : SourceCode) (frame : Frame State) : Action State :=
  match frame.control with
  | .initializing source generator =>
      if generator.halted then
        .deterministic { frame with control := .source (generator.outputTape.current.getD false) false source }
      else nativeAction OneBitEncryption.Native.keygenCode generator
        (fun next => { frame with control := .initializing source next })
  | .source key used source =>
      if CryptoOracle.Interactive.Reification.terminal source then .deterministic frame
      else match CryptoOracle.Interactive.Reification.action code source with
      | .deterministic next => .deterministic { frame with control := .source key used next.control }
      | .random zero one => .random { frame with control := .source key used zero.control }
          { frame with control := .source key used one.control }
      | .oracleCall machine request => .deterministic { frame with
          control := .encrypting key used machine request IntegrityPreparation.initial }
  | .encrypting key used machine request encryption =>
      match IntegrityPreparation.ready encryption with
      | some (_, none) => .deterministic { frame with control := .failure key machine request }
      | some (_, some ciphertext) => .sign ciphertext (fun answer =>
          { frame with
            state := answer.1,
            control := .header key machine request ciphertext answer.2 0 {},
            signingTrace := (ciphertext, answer.2) :: frame.signingTrace })
      | none => match encryption with
        | .preparing phase tape => .deterministic { frame with
            control := .encrypting key used machine request
              (IntegrityPreparation.prepareNext used key (request.headD false) phase tape) }
        | .encrypting native => nativeAction OneBitEncryption.Native.encryptionCode native
            (fun next => { frame with control := .encrypting key used machine request (.encrypting next) })
  | .failure key machine request => .deterministic { frame with
      control := .rewinding key machine request (({ } : Tape).write (some false)) }
  | .header key machine request ciphertext tag phase tape =>
      .deterministic { frame with control := match phase with
        | 0 => .header key machine request ciphertext tag 1 (tape.write (some true))
        | 1 => .header key machine request ciphertext tag 2 tape.moveRight
        | 2 => .header key machine request ciphertext tag 3 (tape.write (some ciphertext))
        | _ => .copying key machine request tag tape.moveRight }
  | .copying key machine request remaining tape =>
      .deterministic { frame with control := match remaining with
        | [] => .rewinding key machine request tape
        | bit :: rest => .advancing key machine request rest (tape.write (some bit)) }
  | .advancing key machine request remaining tape =>
      .deterministic { frame with control := .copying key machine request remaining tape.moveRight }
  | .rewinding key machine request tape =>
      .deterministic { frame with control := match tape.left with
        | [] => .collecting key machine request tape []
        | _ :: _ => .rewinding key machine request tape.moveLeft }
  | .collecting key machine request tape reversed =>
      .deterministic { frame with control := match tape.current with
        | some bit => .collecting key machine request tape.moveRight (bit :: reversed)
        | none => .reversing key machine request reversed [] }
  | .reversing key machine request remaining response =>
      .deterministic { frame with
        control := (match remaining with
          | bit :: rest => .reversing key machine request rest (bit :: response)
          | [] => .source key true (.loading machine response {})),
        sourceTrace := (match remaining with
          | [] => (request, response) :: frame.sourceTrace
          | _ :: _ => frame.sourceTrace) }

noncomputable def step (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (frame : Frame State) : PMF (Frame State) :=
  match transition code frame with
  | .deterministic next => PMF.pure next
  | .random zero one => sampleBit.map (fun bit => if bit then one else zero)
  | .sign ciphertext resume => (oracle frame.state ciphertext).map resume

noncomputable def eval (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool)) :=
  TimedExecution.eval (step code oracle)

theorem eval_succ (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (fuel : Nat) (start : Frame State) :
    eval code oracle (fuel + 1) start = (step code oracle start).bind (eval code oracle fuel) := rfl

theorem eval_add (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (first second : Nat) (start : Frame State) :
    eval code oracle (first + second) start =
      (eval code oracle first start).bind (eval code oracle second) :=
  TimedExecution.eval_add (step code oracle) first second start

def HaltsWithin (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (start : Frame State) (fuel : Nat) : Prop :=
  ∀ final ∈ (eval code oracle fuel start).support, terminal final.control = true

def simulateStep (code : SourceCode) (oracle : State → Bool → State × List Bool)
    (coin : Bool) (frame : Frame State) : Frame State :=
  match transition code frame with
  | .deterministic next => next
  | .random zero one => if coin then one else zero
  | .sign ciphertext resume => resume (oracle frame.state ciphertext)

def simulateLoop (code : SourceCode) (oracle : State → Bool → State × List Bool)
    (coin : Bool) : Nat → Frame State → Nat → Frame State × Nat
  | 0, frame, used => (frame, used)
  | fuel + 1, frame, used =>
      if terminal frame.control then (frame, used) else
        simulateLoop code oracle coin fuel (simulateStep code oracle coin frame) (used + 1)

def simulate (code : SourceCode) (oracle : State → Bool → State × List Bool)
    (coin : Bool) (fuel : Nat) (start : Frame State) : Frame State × Nat :=
  simulateLoop code oracle coin fuel start 0

theorem simulateStep_mem_support (code : SourceCode)
    (oracle : State → Bool → State × List Bool) (coin : Bool) (frame : Frame State) :
    simulateStep code oracle coin frame ∈
      (step code (fun state ciphertext => PMF.pure (oracle state ciphertext)) frame).support := by
  cases h : transition code frame with
  | deterministic next => simp [simulateStep, step, h]
  | random zero one =>
      simp only [simulateStep, step, h, PMF.mem_support_map_iff]
      exact ⟨coin, by simp [sampleBit, uniform], rfl⟩
  | sign ciphertext resume => simp [simulateStep, step, h, PMF.pure_map]

theorem terminal_step (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (frame : Frame State) (h : terminal frame.control = true) : step code oracle frame = PMF.pure frame := by
  cases hc : frame.control <;> simp [terminal, hc] at h
  simp [step, transition, hc, h]

theorem terminal_eval (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (frame : Frame State) (h : terminal frame.control = true) (fuel : Nat) :
    eval code oracle fuel frame = PMF.pure frame := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change (step code oracle frame).bind (eval code oracle fuel) = _
      rw [terminal_step code oracle frame h, PMF.pure_bind, ih]

theorem simulateLoop_mem_support (code : SourceCode)
    (oracle : State → Bool → State × List Bool) (coin : Bool)
    (fuel : Nat) (start : Frame State) (used : Nat) :
    (simulateLoop code oracle coin fuel start used).1 ∈
      (eval code (fun state ciphertext => PMF.pure (oracle state ciphertext)) fuel start).support := by
  induction fuel generalizing start used with
  | zero => simp [simulateLoop, eval, TimedExecution.eval]
  | succ fuel ih =>
      by_cases h : terminal start.control = true
      · rw [simulateLoop, if_pos h, terminal_eval code _ start h]
        simp
      · rw [simulateLoop, if_neg h]
        change (simulateLoop code oracle coin fuel (simulateStep code oracle coin start) (used + 1)).1 ∈
          ((step code (fun state ciphertext => PMF.pure (oracle state ciphertext)) start).bind
            (eval code (fun state ciphertext => PMF.pure (oracle state ciphertext)) fuel)).support
        rw [PMF.mem_support_bind_iff]
        exact ⟨simulateStep code oracle coin start, simulateStep_mem_support code oracle coin start, ih _ _⟩

theorem simulate_mem_support (code : SourceCode)
    (oracle : State → Bool → State × List Bool) (coin : Bool) (fuel : Nat) (start : Frame State) :
    (simulate code oracle coin fuel start).1 ∈
      (eval code (fun state ciphertext => PMF.pure (oracle state ciphertext)) fuel start).support :=
  simulateLoop_mem_support code oracle coin fuel start 0

theorem failed_encryption_no_sign (code : SourceCode) (key : Bool) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace : List (List Bool × List Bool))
    (signingTrace : List (Bool × List Bool)) (message : Bool) :
    transition code ⟨state, .encrypting key true machine request
      (.encrypting (IntegrityEncryption.finish true key message)), sourceTrace, signingTrace⟩ =
      .deterministic ⟨state, .failure key machine request, sourceTrace, signingTrace⟩ := rfl

theorem successful_encryption_sign (code : SourceCode) (key message : Bool) (machine : Configuration)
    (request : List Bool) (state : State) (sourceTrace : List (List Bool × List Bool))
    (signingTrace : List (Bool × List Bool)) :
    transition code ⟨state, .encrypting key false machine request
      (.encrypting (IntegrityEncryption.finish false key message)), sourceTrace, signingTrace⟩ =
      .sign (Bool.xor key message) (fun answer =>
        ⟨answer.1, .header key machine request (Bool.xor key message) answer.2 0 {},
          sourceTrace, (Bool.xor key message, answer.2) :: signingTrace⟩) := rfl

theorem source_deterministic (code : SourceCode) (key used : Bool) (source : SourceControl)
    (state : State) (sourceTrace : List (List Bool × List Bool)) (signingTrace : List (Bool × List Bool))
    (next : CryptoOracle.Interactive.Configuration Unit)
    (hRunning : CryptoOracle.Interactive.Reification.terminal source = false)
    (hNext : CryptoOracle.Interactive.Reification.action code source = .deterministic next) :
    transition code ⟨state, .source key used source, sourceTrace, signingTrace⟩ =
      .deterministic ⟨state, .source key used next.control, sourceTrace, signingTrace⟩ := by
  simp [transition, hRunning, hNext]

theorem source_random (code : SourceCode) (key used : Bool) (source : SourceControl)
    (state : State) (sourceTrace : List (List Bool × List Bool)) (signingTrace : List (Bool × List Bool))
    (zero one : CryptoOracle.Interactive.Configuration Unit)
    (hRunning : CryptoOracle.Interactive.Reification.terminal source = false)
    (hNext : CryptoOracle.Interactive.Reification.action code source = .random zero one) :
    transition code ⟨state, .source key used source, sourceTrace, signingTrace⟩ =
      .random ⟨state, .source key used zero.control, sourceTrace, signingTrace⟩
        ⟨state, .source key used one.control, sourceTrace, signingTrace⟩ := by
  simp [transition, hRunning, hNext]

theorem source_resume (code : SourceCode) (key : Bool) (machine : Configuration)
    (request response : List Bool) (state : State) (sourceTrace : List (List Bool × List Bool))
    (signingTrace : List (Bool × List Bool)) :
    transition code ⟨state, .reversing key machine request [] response, sourceTrace, signingTrace⟩ =
      .deterministic ⟨state, .source key true (.loading machine response {}),
        (request, response) :: sourceTrace, signingTrace⟩ := rfl

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
