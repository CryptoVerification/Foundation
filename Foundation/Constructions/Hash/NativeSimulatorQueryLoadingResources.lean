import Foundation.Constructions.Hash.NativeSimulatorQueryLoading

/-! Faithful complete-controller storage for admission, physical request
loading and native lookup. The old halted frame and pending raw request are
encoded before admission; all retained/loading/native frames are encoded
after it. Cell-equivalence observations are not used to measure storage. -/
namespace Foundation.Hash.Native.SimulatorQueryLoading
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def encodingView {State : Type*} : Control State → Bool × Configuration State
  | .admitting state machine trace request => (false, ⟨state, .loading machine request {}, trace⟩)
  | .executing frame => (true, frame)

def controlEncoding {State : Type*} (E : FiniteBitEncoding State) : FiniteBitEncoding (Control State) where
  encode := fun control => (Machine.ConfigurationEncoding.bit.prod (ConfigurationEncoding.frame E)).encode (encodingView control)
  decode := fun raw => do
    let (tag, frame) ← (Machine.ConfigurationEncoding.bit.prod (ConfigurationEncoding.frame E)).decode raw
    if tag then some (.executing frame) else
      match frame.control with
      | .loading machine request _ => some (.admitting frame.state machine frame.reverseTrace request)
      | _ => none
  decode_encode := by
    intro control
    cases control <;> simp [encodingView, FiniteBitEncoding.decode_encode]

def fullEncoding {State : Type*} (E : FiniteBitEncoding State) := EncodedStorage.codeEncoding.prod (controlEncoding E)

theorem executing_encoding_length {State : Type*} (E : FiniteBitEncoding State) (program : Code)
    (frame : Configuration State) :
    ((fullEncoding E).encode (program, Control.executing frame)).length =
      ((NativeCode.fullEncoding E).encode (program, frame)).length + 3 := by
  simp [fullEncoding, controlEncoding, encodingView, NativeCode.fullEncoding,
    FiniteBitEncoding.prod_encode_length, Machine.ConfigurationEncoding.bit]
  omega

theorem admission_run {State : Type*} (program : Code) (n κ : Nat) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool)) (request : List Bool) :
    TimedExecution.eval (step program n κ oracle) 1 (.admitting state machine trace request) =
      PMF.pure (.executing (loadingFrame n κ state machine trace request)) := by
  simp [TimedExecution.eval, step, loadingFrame]

theorem after_admission_run {State : Type*} (program : Code) (n κ : Nat) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (request : List Bool) (fuel : Nat) :
    TimedExecution.eval (step program n κ oracle) (fuel + 1) (.admitting state machine trace request) =
      (TimedExecution.eval (Reification.timedStep program oracle) fuel
        (loadingFrame n κ state machine trace request)).map Control.executing := by
  rw [show fuel + 1 = 1 + fuel by omega, TimedExecution.eval_add, admission_run, PMF.pure_bind, executing_run]

/-- The initial PC may be an arbitrary returned caller address, so its
actual encoding is retained separately instead of pretending admission
already erased or rebased that frame. -/
def storageBound {State : Type*} (program : Code) (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (n κ : Nat) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (request : List Bool) (horizon : Nat) : Nat :=
  max (((fullEncoding E).encode (program, Control.admitting state machine trace request)).length)
    (NativeCode.storageBound program
      (NativePacketComponent.Resources.frameSize stateSize (loadingFrame n κ state machine trace request)) horizon + 3)

/-- Every supported physical intermediate controller is bounded, including
before admission and during loading. No hypothesis on the unused external
oracle's execution time, state growth or response length is required. -/
theorem encoded_peak {State : Type*} (program : Code)
    (native : ∀ op ∈ program, ∃ instruction, op = .native instruction) (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    {n κ : Nat} (oracle : BitOracle State) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (horizon elapsed : Nat) (within : elapsed ≤ horizon + 1) (target : Control State)
    (support : target ∈ (TimedExecution.eval (step program n κ oracle) elapsed
      (.admitting state machine trace request)).support) :
    ((fullEncoding E).encode (program, target)).length ≤
      storageBound program E stateSize n κ state machine trace request horizon := by
  cases elapsed with
  | zero =>
      rw [TimedExecution.eval, PMF.mem_support_pure_iff] at support
      subst target
      exact Nat.le_max_left _ _
  | succ elapsed =>
      rw [after_admission_run, PMF.mem_support_map_iff] at support
      obtain ⟨frame, reachable, rfl⟩ := support
      have bound := NativeCode.encoded_peak_from E stateSize hState oracle program
        native (loadingFrame n κ state machine trace request)
        (by trivial) horizon elapsed (by omega) frame reachable
      rw [executing_encoding_length]
      exact (Nat.add_le_add_right bound 3).trans (Nat.le_max_right _ _)

end Foundation.Hash.Native.SimulatorQueryLoading
