import Foundation.Crypto.Semantics.Oracle.OneUseRoundSemantics
import Foundation.Crypto.Semantics.Oracle.OneUseAutomaticCertificate
import Foundation.Crypto.Semantics.Oracle.OneUseInitializedRounds
import Foundation.Crypto.Semantics.Oracle.BoundaryExtent
import Foundation.Crypto.Semantics.Oracle.OneUseCallerStopping
import Foundation.Crypto.Semantics.Oracle.OneUseCallerInitialization

/-! A real finite caller sends a width-dependent message, then sends the
actual previous response as its second request, then executes native halt.
The request is read from the physical response tape, not supplied as a new
logical input. The second query uses the already-spent private key. -/
namespace Foundation.OneUseAdaptiveEchoExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open OneUseSourceRounds
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def code : Code := [.call, .call, .native .halt]

def firstMachine {width : Nat} (message : Bits width) (input : List Bool) : Machine.Configuration :=
  { inputTape := Machine.Tape.ofBits input, outputTape := RequestExport.packetTape [] [] message.toList }

def firstPacket {width : Nat} (key message : Bits width) : List Bool :=
  true :: Machine.OneTimePad.xorList key.toList message.toList

variable {width : Nat} (key message : Bits width) (input : List Bool) (state : State)
    (trace : List (List Bool × List Bool))

def initial : Boundary State := ⟨false, ⟨state, .running (firstMachine message input), trace⟩⟩

def secondMachine : Machine.Configuration :=
  { (firstMachine message input).advance with outputTape := ResponseLoading.loaded (firstPacket key message) }

def afterFirst : Boundary State :=
  ⟨true, NativeCallback.resumed (firstMachine message input).advance state trace message.toList (firstPacket key message)⟩

def thirdMachine : Machine.Configuration :=
  { (secondMachine key message input).advance with outputTape := ResponseLoading.loaded [false] }

def afterSecond : Boundary State :=
  ⟨true, NativeCallback.resumed (secondMachine key message input).advance state
    ((message.toList, firstPacket key message) :: trace) (firstPacket key message) [false]⟩

def halted : Boundary State :=
  ⟨true, { (afterSecond key message input state trace).frame with
    control := .running { thirdMachine key message input with halted := true } }⟩

def firstLayout : CallLayout code (initial message input state trace).frame where
  machine := firstMachine message input
  request := message.toList
  tail := []
  control := rfl
  active := rfl
  call := rfl
  tape := rfl

def secondLayout : CallLayout code (afterFirst key message input state trace).frame where
  machine := secondMachine key message input
  request := firstPacket key message
  tail := []
  control := rfl
  active := rfl
  call := rfl
  tape := rfl

variable (oracle : BitOracle State) (stateSize : State → Nat)

theorem first_round :
    (automaticRound stateSize code oracle key.toList [] 1).semantics (initial message input state trace) =
      PMF.pure (afterFirst key message input state trace) := by
  have h := automaticRound_call stateSize code oracle key.toList [] 1 (initial message input state trace)
    (firstLayout message input state trace)
  simpa [OneUseXorRequest.used, OneUseXorRequest.reply, firstLayout, initial, afterFirst, firstPacket] using h

theorem second_round :
    (automaticRound stateSize code oracle key.toList [] 1).semantics (afterFirst key message input state trace) =
      PMF.pure (afterSecond key message input state trace) := by
  exact automaticRound_call stateSize code oracle key.toList [] 1 (afterFirst key message input state trace)
    (secondLayout key message input state trace)

theorem halt_round :
    (automaticRound stateSize code oracle key.toList [] 1).semantics (afterSecond key message input state trace) =
      PMF.pure (halted key message input state trace) :=
  automaticRound_halt stateSize code oracle key.toList [] (afterSecond key message input state trace)
    (thirdMachine key message input) rfl rfl rfl

theorem halted_round :
    (automaticRound stateSize code oracle key.toList [] 1).semantics (halted key message input state trace) =
      PMF.pure (halted key message input state trace) :=
  automaticRound_terminal stateSize code oracle key.toList [] 1 (halted key message input state trace) rfl

def admissible (source : Boundary State) : Prop :=
  source = initial message input state trace ∨ source = afterFirst key message input state trace ∨
    source = afterSecond key message input state trace ∨ source = halted key message input state trace

def extentCap : Nat :=
  max (ControllerExtent.sourceExtent stateSize (embed (OneUseProgramInitialization.store key) (initial message input state trace)))
    (max (ControllerExtent.sourceExtent stateSize (embed (OneUseProgramInitialization.store key) (afterFirst key message input state trace)))
      (max (ControllerExtent.sourceExtent stateSize (embed (OneUseProgramInitialization.store key) (afterSecond key message input state trace)))
        (ControllerExtent.sourceExtent stateSize (embed (OneUseProgramInitialization.store key) (halted key message input state trace)))))

/-- A common cap for every key value. Original caller data is explicitly
included; no enumeration of the exponentially many keys is performed. -/
def uniformExtent (width : Nat) (input : List Bool) (state : State)
    (trace : List (List Bool × List Bool)) (stateSize : State → Nat) : Nat :=
  max (width + 2) (max (input.length + 1)
    (max (stateSize state) (ControllerExtent.traceExtent trace + 2)))

theorem firstPacket_length : (firstPacket key message).length = width + 1 := by
  simp [firstPacket, ← Machine.OneTimePad.toList_xor]

theorem extentCap_le_uniform : extentCap key message input state trace stateSize ≤
    uniformExtent width input state trace stateSize := by
  have hi := Machine.Tape.cells_ofBits_le input
  have ht := ControllerExtent.trace_cons_bound message.toList (firstPacket key message) trace
  have hu := ControllerExtent.trace_cons_bound (firstPacket key message) [false]
    ((message.toList, firstPacket key message) :: trace)
  simp only [Bits.length_toList, firstPacket_length, List.length_cons, List.length_nil] at ht hu
  have h0 : ControllerExtent.sourceExtent stateSize
      (embed (OneUseProgramInitialization.store key) (initial message input state trace)) ≤
      uniformExtent width input state trace stateSize := by
    change max (Machine.PairPreparation.operand [] key.toList []).cells
      (max (stateSize state) (max
        (max (Machine.Tape.ofBits input).cells (RequestExport.packetTape [] [] message.toList).cells)
        (ControllerExtent.traceExtent trace))) ≤ _
    rw [Machine.PairPreparation.operand_cells, RequestExport.packetTape_cells]
    simp only [Bits.length_toList, List.length_nil]
    unfold uniformExtent
    omega
  have h1 : ControllerExtent.sourceExtent stateSize
      (embed (OneUseProgramInitialization.store key) (afterFirst key message input state trace)) ≤
      uniformExtent width input state trace stateSize := by
    change max (Machine.PairPreparation.operand [] key.toList []).cells
      (max (stateSize state) (max
        (max (Machine.Tape.ofBits input).cells (ResponseLoading.loaded (firstPacket key message)).cells)
        (ControllerExtent.traceExtent ((message.toList, firstPacket key message) :: trace)))) ≤ _
    rw [Machine.PairPreparation.operand_cells, ResponseLoading.loaded_cells]
    simp only [Bits.length_toList, List.length_nil, firstPacket_length]
    unfold uniformExtent
    omega
  have h2 : ControllerExtent.sourceExtent stateSize
      (embed (OneUseProgramInitialization.store key) (afterSecond key message input state trace)) ≤
      uniformExtent width input state trace stateSize := by
    change max (Machine.PairPreparation.operand [] key.toList []).cells
      (max (stateSize state) (max
        (max (Machine.Tape.ofBits input).cells (ResponseLoading.loaded [false]).cells)
        (ControllerExtent.traceExtent ((firstPacket key message, [false]) ::
          (message.toList, firstPacket key message) :: trace)))) ≤ _
    rw [Machine.PairPreparation.operand_cells, ResponseLoading.loaded_cells]
    simp only [Bits.length_toList, List.length_nil, List.length_cons]
    unfold uniformExtent
    omega
  have h3 : ControllerExtent.sourceExtent stateSize
      (embed (OneUseProgramInitialization.store key) (halted key message input state trace)) ≤
      uniformExtent width input state trace stateSize := h2
  unfold extentCap
  omega

theorem logical_run :
    TimedExecution.eval (automaticRound stateSize code oracle key.toList [] 1).semantics 3
      (initial message input state trace) = PMF.pure (halted key message input state trace) := by
  rw [TimedExecution.eval, first_round, PMF.pure_bind,
    TimedExecution.eval, second_round, PMF.pure_bind,
    TimedExecution.eval, halt_round, PMF.pure_bind, TimedExecution.eval]

/-- Stop the actual finite caller at the logical instruction level, counting
each laid-out query once and the native halt once. No physical query budget
or generated-key enumeration is used in this source stopping proof. -/
theorem caller_run :
    TimedExecution.eval (callerStep code oracle key.toList []) 3
      (initial message input state trace) = PMF.pure (halted key message input state trace) := by
  have h1 : callerStep code oracle key.toList [] (initial message input state trace) =
      PMF.pure (afterFirst key message input state trace) := by
    have h := callerStep_call code oracle key.toList [] (initial message input state trace)
      (firstLayout message input state trace)
    simpa [OneUseXorRequest.used, OneUseXorRequest.reply, firstLayout, initial, afterFirst, firstPacket] using h
  have h2 : callerStep code oracle key.toList [] (afterFirst key message input state trace) =
      PMF.pure (afterSecond key message input state trace) :=
    callerStep_call code oracle key.toList [] (afterFirst key message input state trace)
      (secondLayout key message input state trace)
  have h3 : callerStep code oracle key.toList [] (afterSecond key message input state trace) =
      PMF.pure (halted key message input state trace) :=
    callerStep_halt code oracle key.toList [] (afterSecond key message input state trace)
      (thirdMachine key message input) rfl rfl rfl
  rw [TimedExecution.eval, h1, PMF.pure_bind, TimedExecution.eval, h2, PMF.pure_bind,
    TimedExecution.eval, h3, PMF.pure_bind, TimedExecution.eval]

noncomputable def certificate : AutomaticCertificate stateSize code oracle key.toList []
    (initial message input state trace).frame where
  fuel := 1
  predicate := admissible key message input state trace
  closed := by
    intro source hs result hr
    rcases hs with rfl | rfl | rfl | rfl
    · rw [first_round, PMF.mem_support_pure_iff] at hr
      subst result
      exact Or.inr (Or.inl rfl)
    · rw [second_round, PMF.mem_support_pure_iff] at hr
      subst result
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [halt_round, PMF.mem_support_pure_iff] at hr
      subst result
      exact Or.inr (Or.inr (Or.inr rfl))
    · rw [halted_round, PMF.mem_support_pure_iff] at hr
      subst result
      exact Or.inr (Or.inr (Or.inr rfl))
  extentCap := extentCap key message input state trace stateSize
  extentBound := by
    intro source hs
    rcases hs with rfl | rfl | rfl | rfl
    all_goals unfold extentCap; simp only [OneUseProgramInitialization.store]; omega
  count := 3
  initial := Or.inl rfl
  stops := by
    apply automatic_stops_of_caller stateSize code oracle key.toList [] 1 (by decide)
      (initial message input state trace) 3 3 (Nat.le_refl _)
    intro final hs
    rw [caller_run, PMF.mem_support_pure_iff] at hs
    subst final
    rfl

/-- Complete physical caller: the second request is the first response,
including its width-dependent ciphertext, and the second response is rejection. -/
theorem run (horizon : Nat)
    (hBudget : 3 * (1 + (33 * (width + extentCap key message input state trace stateSize + 2) + 33)) ≤ horizon) :
    TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      horizon (embed (OneUseProgramInitialization.store key) (initial message input state trace)) =
      PMF.pure (embed (OneUseProgramInitialization.store key) (halted key message input state trace)) := by
  have h := OneUseSourceRounds.run code oracle key.toList []
    (certificate key message input state trace oracle stateSize).certificate.fuel
    (certificate key message input state trace oracle stateSize).certificate.cap
    (certificate key message input state trace oracle stateSize).certificate.capProof
    (certificate key message input state trace oracle stateSize).certificate.predicate
    (certificate key message input state trace oracle stateSize).certificate.closed
    (certificate key message input state trace oracle stateSize).certificate.bound
    (certificate key message input state trace oracle stateSize).certificate.bounded 3
    (certificate key message input state trace oracle stateSize).certificate.start
    (certificate key message input state trace oracle stateSize).certificate.stops horizon (by
      simpa [certificate, AutomaticCertificate.certificate] using hBudget)
  change TimedExecution.eval _ horizon (embed (OneUseProgramInitialization.store key) (initial message input state trace)) =
    (TimedExecution.eval (automaticRound stateSize code oracle key.toList [] 1).semantics 3
      (initial message input state trace)).map _ at h
  rw [logical_run, PMF.pure_map] at h
  exact h

/-- The same consumer cap works for every native-generated key. -/
def consumerCap (width : Nat) (input : List Bool) (state : State)
    (trace : List (List Bool × List Bool)) (stateSize : State → Nat) : Nat :=
  3 * (1 + (33 * (width + uniformExtent width input state trace stateSize + 2) + 33))

theorem certificate_cap :
    (certificate key message input state trace oracle stateSize).certificate.count *
      (certificate key message input state trace oracle stateSize).certificate.bound ≤
      consumerCap width input state trace stateSize := by
  have he := extentCap_le_uniform key message input state trace stateSize
  simp only [certificate, AutomaticCertificate.certificate, Bits.length_toList, consumerCap]
  omega

/-- Reuse the invariant and extent proofs while certifying stopping only in
the caller's logical clock. This feeds the observed native registration. -/
noncomputable def callerCertificate : CallerCertificate stateSize code oracle key.toList []
    (initial message input state trace).frame where
  fuel := 1
  positive := by decide
  predicate := (certificate key message input state trace oracle stateSize).predicate
  closed := (certificate key message input state trace oracle stateSize).closed
  extentCap := (certificate key message input state trace oracle stateSize).extentCap
  extentBound := (certificate key message input state trace oracle stateSize).extentBound
  logicalBound := 3
  count := 3
  countBound := Nat.le_refl _
  initial := (certificate key message input state trace oracle stateSize).initial
  stops := by
    intro final hs
    change final ∈ (TimedExecution.eval (callerStep code oracle key.toList []) 3
      (initial message input state trace)).support at hs
    rw [caller_run, PMF.mem_support_pure_iff] at hs
    subst final
    rfl

theorem callerCertificate_cap :
    (callerCertificate key message input state trace oracle stateSize).physicalBudget ≤
      consumerCap width input state trace stateSize := by
  simpa only [callerCertificate, CallerCertificate.physicalBudget, certificate,
    AutomaticCertificate.certificate] using certificate_cap key message input state trace oracle stateSize

noncomputable def initialized :=
  OneUseInitializedRounds.complete code oracle (initial message input state trace).frame width
    (fun key => (certificate key message input state trace oracle stateSize).certificate)
    (consumerCap width input state trace stateSize)
    (fun key => certificate_cap key message input state trace oracle stateSize)

theorem initialized_budget :
    (initialized message input state trace oracle stateSize).budget () =
      105 * width + 99 * uniformExtent width input state trace stateSize + 305 := by
  rw [initialized, OneUseInitializedRounds.budget]
  unfold consumerCap
  omega

/-- Native key generation, actual adaptive ciphertext echo, spent rejection
and native halt, all in the original finite caller and physical controller. -/
theorem initialized_run (horizon : Nat)
    (hBudget : 105 * width + 99 * uniformExtent width input state trace stateSize + 305 ≤ horizon) :
    TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen
      Machine.OneTimePad.Prepared.listProcedure.code code oracle (initial message input state trace).frame)
      horizon (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      (uniform (Bits width)).map (fun key => OneUseInitialization.Control.active
        (embed (OneUseProgramInitialization.store key) (halted key message input state trace))) := by
  have hTotal : 6 * width + 5 + consumerCap width input state trace stateSize ≤ horizon := by
    have hEq : 6 * width + 5 + consumerCap width input state trace stateSize =
        105 * width + 99 * uniformExtent width input state trace stateSize + 305 := by
      unfold consumerCap
      ring
    exact hEq.trans_le hBudget
  have h := OneUseCallerInitialization.run stateSize code oracle (initial message input state trace).frame width
    (fun key => callerCertificate key message input state trace oracle stateSize)
    (consumerCap width input state trace stateSize)
    (fun key => callerCertificate_cap key message input state trace oracle stateSize) horizon hTotal
  change TimedExecution.eval _ horizon _ = (uniform (Bits width)).bind (fun key =>
    (TimedExecution.eval (callerStep code oracle key.toList []) 3
      (initial message input state trace)).map
      (OneUseInitialization.Control.active ∘ embed (OneUseProgramInitialization.store key))) at h
  simp_rw [caller_run] at h
  simp only [PMF.pure_map, Function.comp_def] at h
  exact h.trans (PMF.bind_pure_comp _ _)

theorem initial_extent_le_uniform :
    ControllerExtent.initializationExtent stateSize (initial message input state trace).frame
      (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) ≤
      uniformExtent width input state trace stateSize := by
  have hi := Machine.Tape.cells_ofBits_le input
  have hg := Machine.Tape.cells_ofBits_le (List.replicate width true)
  change max (max (stateSize state) (max
    (max (Machine.Tape.ofBits input).cells (RequestExport.packetTape [] [] message.toList).cells)
    (ControllerExtent.traceExtent trace)))
    (max (Machine.Tape.ofBits (List.replicate width true)).cells (Machine.Tape.cells {})) ≤ _
  rw [RequestExport.packetTape_cells]
  simp only [Bits.length_toList, List.length_nil, List.length_replicate, Machine.Tape.cells] at *
  unfold uniformExtent
  omega

/-- Every actual prefix, including generation and all transient copies,
is bounded using the caller's original data as well as the new key width. -/
theorem initialized_memory_peak (stateIncrement responseCap : Nat)
    (hOracle : ∀ st request answer, answer ∈ (oracle st request).support →
      stateSize answer.1 ≤ stateSize st + stateIncrement ∧ answer.2.length ≤ responseCap)
    (elapsed : Nat)
    (hElapsed : elapsed ≤ 105 * width + 99 * uniformExtent width input state trace stateSize + 305)
    (target : OneUseInitialization.Control State)
    (h : target ∈ (TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen
      Machine.OneTimePad.Prepared.listProcedure.code code oracle (initial message input state trace).frame)
      elapsed (.initializing (.generating (Machine.Configuration.initial (List.replicate width true))))).support) :
    ControllerStorage.initializationCells stateSize (initial message input state trace).frame target ≤
      4 * (uniformExtent width input state trace stateSize +
        (105 * width + 99 * uniformExtent width input state trace stateSize + 305) *
          (stateIncrement + responseCap + 2)) ^ 2 +
      11 * (uniformExtent width input state trace stateSize +
        (105 * width + 99 * uniformExtent width input state trace stateSize + 305) *
          (stateIncrement + responseCap + 2)) + 2 := by
  have hp := ControllerExtent.initialization_peak stateSize Machine.OneTimePad.keygen
    Machine.OneTimePad.Prepared.listProcedure.code code oracle (initial message input state trace).frame
    stateIncrement responseCap hOracle
    (105 * width + 99 * uniformExtent width input state trace stateSize + 305) elapsed hElapsed
    (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) target h
  have he := initial_extent_le_uniform message input state trace stateSize
  have hAdd := Nat.add_le_add_right he
    ((105 * width + 99 * uniformExtent width input state trace stateSize + 305) *
      (stateIncrement + responseCap + 2))
  have hPow := Nat.pow_le_pow_left hAdd 2
  exact hp.trans (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 4 hPow) (Nat.mul_le_mul_left 11 hAdd)) 2)

/-- Polynomial input/state/transcript profiles suffice; fixed inputs are
not silently assumed when the key width is allowed to vary. -/
theorem uniformExtent_profile_polynomial {width : Nat → Nat} {input : Nat → List Bool}
    {state : Nat → State} {trace : Nat → List (List Bool × List Bool)}
    (hWidth : PolynomiallyBounded width)
    (hInput : PolynomiallyBounded (fun n => (input n).length))
    (hState : PolynomiallyBounded (fun n => stateSize (state n)))
    (hTrace : PolynomiallyBounded (fun n => ControllerExtent.traceExtent (trace n))) :
    PolynomiallyBounded (fun n => uniformExtent (width n) (input n) (state n) (trace n) stateSize) := by
  apply PolynomiallyBounded.mono (s := fun n => (width n + 2) +
    ((input n).length + 1) + (stateSize (state n) + (ControllerExtent.traceExtent (trace n) + 2)))
  · intro n
    unfold uniformExtent
    omega
  · exact ((hWidth.add (PolynomiallyBounded.const 2)).add
      (hInput.add (PolynomiallyBounded.const 1))).add
        (hState.add (hTrace.add (PolynomiallyBounded.const 2)))

theorem initialized_time_profile_polynomial {width : Nat → Nat} {extent : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hExtent : PolynomiallyBounded extent) :
    PolynomiallyBounded (fun n => 105 * width n + 99 * extent n + 305) :=
  (((PolynomiallyBounded.const 105).mul hWidth).add
    ((PolynomiallyBounded.const 99).mul hExtent)).add (PolynomiallyBounded.const 305)

end Foundation.OneUseAdaptiveEchoExamples
