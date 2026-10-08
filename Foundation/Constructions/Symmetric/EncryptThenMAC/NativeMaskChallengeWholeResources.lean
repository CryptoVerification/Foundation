import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskChallengeResources
import Foundation.Crypto.Semantics.Machine.NativeContinuationGrowth

/-! Whole-prefix resources for the actual challenge-query reduction, including
loading, alignment, masking and native observation. Original caller data are
retained explicitly, also during loading. All finite runtime codes are counted. -/
namespace Foundation.Symmetric.EncryptThenMAC.NativeMaskChallenge.WholeResources
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Examples
open ReusableBlockPad.NativeObserver (RuntimeState boundary publicMachine)
open ReusableResponse.Initialized
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {width : Nat} (message : Bits width)

def caller := ReusableBlockPad.callerFrame () [] message
def callerExtent := ControllerExtent.frameExtent (fun _ : Unit => 0) (caller message)
def sourceExtent := ReusableResponse.Initialized.Resources.extent (fun _ : Unit => 0) (caller message)
def sourcePc := Encoded.maxPc (caller message)

def extent : NativeMaskChallenge.Control → Nat
  | .querying => callerExtent message + width + 3
  | .loading frame => max (callerExtent message) (ControllerExtent.frameExtent (fun _ : Unit => 0) frame)
  | .aligning tape => max (callerExtent message) tape.cells
  | .active target => NativeContinuation.Growth.extent (sourceExtent message) target

def pc : NativeMaskChallenge.Control → Nat
  | .querying | .aligning _ => 0
  | .loading frame => ConfigurationEncoding.pc frame.control
  | .active target => NativeContinuation.Growth.pc (sourcePc message) target

private theorem oracle_bound (state : Unit) (request : List Bool) (result : Unit × List Bool)
    (h : result ∈ (NativeMaskReduction.oracle state request).support) :
    (0 : Nat) ≤ 0 + 0 ∧ result.2.length ≤ 0 := by
  rw [NativeMaskReduction.oracle, ReusableBlockPadEncodedBackend.unitOracle, PMF.mem_support_pure_iff] at h
  subst result
  simp

theorem public_extent (target : RuntimeState Unit) :
    Machine.ControllerExtent.machine (publicMachine target) ≤ sourceExtent message target + 1 := by
  cases target with
  | initializing component =>
      simp [publicMachine, ReusableNativeObservation.publicMachine, Machine.ControllerExtent.machine,
        Tape.cells]
  | aligning tape =>
      simp [publicMachine, ReusableNativeObservation.publicMachine, Machine.ControllerExtent.machine,
        Tape.cells]
  | active source =>
      cases source with
      | processing =>
          simp [publicMachine, ReusableNativeObservation.publicMachine, Machine.ControllerExtent.machine,
            Tape.cells]
      | calling =>
          simp [publicMachine, ReusableNativeObservation.publicMachine, Machine.ControllerExtent.machine,
            Tape.cells]
      | source retained frame =>
          rcases frame with ⟨state, control, trace⟩
          cases control with
          | running machine =>
              simp only [publicMachine, ReusableNativeObservation.publicMachine, sourceExtent,
                ReusableResponse.Initialized.Resources.extent, ReusableInitializationStorage.extent,
                ReusableInitializationStorage.phaseExtent, ReusableResponseStorage.extent,
                ControllerExtent.frameExtent, ControllerExtent.controlExtent]
              omega
          | _ => simp [publicMachine, ReusableNativeObservation.publicMachine,
              Machine.ControllerExtent.machine, Tape.cells]

private theorem loader_extent (frame : CryptoOracle.Interactive.Configuration Unit) :
    (loaderMachine frame.control).outputTape.cells ≤
      ControllerExtent.frameExtent (fun _ : Unit => 0) frame + 1 := by
  rcases frame with ⟨state, control, trace⟩
  cases control <;> simp [loaderMachine, ControllerExtent.frameExtent, ControllerExtent.controlExtent,
    Machine.ControllerExtent.machine, Tape.cells] <;> omega

/-- A single constant growth allowance covers all phases. The initial
reservation covers the finite incoming challenge as well as the public input. -/
theorem extent_step (distribution : PMF (Bits width)) (code : Program)
    (start next : NativeMaskChallenge.Control)
    (h : next ∈ (NativeMaskChallenge.step distribution message code start).support) :
    extent message next ≤ extent message start + 7 := by
  cases start with
  | querying =>
      simp only [NativeMaskChallenge.step, PMF.mem_support_map_iff] at h
      obtain ⟨key, _, rfl⟩ := h
      simp [extent, loadFrame, ControllerExtent.frameExtent, ControllerExtent.controlExtent,
        Machine.ControllerExtent.machine, Tape.cells, Bits.length_toList, ControllerExtent.traceExtent]
      omega
  | loading frame =>
      cases ht : Reification.terminal frame.control with
      | true =>
          simp only [NativeMaskChallenge.step, ht, ↓reduceIte, PMF.mem_support_pure_iff] at h
          subst next
          have hl := loader_extent frame
          have hm := Tape.cells_moveLeft_le (loaderMachine frame.control).outputTape
          simp only [extent]
          omega
      | false =>
          simp only [NativeMaskChallenge.step, ht, Bool.false_eq_true, ↓reduceIte,
            PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have he := ControllerExtent.public_step (fun _ : Unit => 0) loadCode
            NativeMaskReduction.oracle 0 0 oracle_bound frame next hn
          simp only [extent]
          omega
  | aligning tape =>
      simp only [NativeMaskChallenge.step, PMF.mem_support_pure_iff] at h
      subst next
      have hm := Tape.cells_moveRight_le tape
      simp only [extent, NativeContinuation.Growth.extent, sourceExtent,
        ReusableResponse.Initialized.Resources.extent, ReusableInitializationStorage.extent,
        ReusableInitializationStorage.phaseExtent, ReusableResponseStorage.extent, callerExtent, caller]
      omega
  | active target =>
      simp only [NativeMaskChallenge.step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, rfl⟩ := h
      exact NativeContinuation.Growth.extent_step (NativeMaskReduction.sourceStep message)
        boundary publicMachine code (sourceExtent message) 5 1
        (fun start next hs => ReusableResponse.Initialized.Resources.extent_step
          (fun _ : Unit => 0) (caller message) Machine.OneTimePad.keygen FlaggedBlockXor.code
          ReusableBlockPad.code NativeMaskReduction.oracle 0 0 oracle_bound start next hs)
        (fun state _ => public_extent message state) target next hn

def addressIncrement (code : Program) :=
  Encoded.addressIncrement Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code +
    EncodedStorage.addressCap loadCode + code.addressCap + 2

theorem pc_step (distribution : PMF (Bits width)) (code : Program)
    (start next : NativeMaskChallenge.Control)
    (h : next ∈ (NativeMaskChallenge.step distribution message code start).support) :
    pc message next ≤ pc message start + addressIncrement code := by
  cases start with
  | querying =>
      simp only [NativeMaskChallenge.step, PMF.mem_support_map_iff] at h
      obtain ⟨key, _, rfl⟩ := h
      simp [pc, loadFrame, ConfigurationEncoding.pc]
  | loading frame =>
      cases ht : Reification.terminal frame.control with
      | true =>
          simp only [NativeMaskChallenge.step, ht, ↓reduceIte, PMF.mem_support_pure_iff] at h
          subst next
          simp [pc]
      | false =>
          simp only [NativeMaskChallenge.step, ht, Bool.false_eq_true, ↓reduceIte,
            PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hp := EncodedStorage.pc_step loadCode NativeMaskReduction.oracle frame next hn
          simp only [pc, addressIncrement]
          omega
  | aligning tape =>
      simp only [NativeMaskChallenge.step, PMF.mem_support_pure_iff] at h
      subst next
      simp [pc, NativeContinuation.Growth.pc, sourcePc, Encoded.maxPc,
        Encoded.phaseMaxPc, ReusableResponse.Encoded.maxPc, caller,
        ReusableBlockPad.callerFrame, ReusableBlockPad.caller, ConfigurationEncoding.pc]
  | active target =>
      simp only [NativeMaskChallenge.step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, rfl⟩ := h
      have hp := NativeContinuation.Growth.pc_step (NativeMaskReduction.sourceStep message)
        boundary publicMachine code (sourcePc message)
        (Encoded.addressIncrement Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code)
        (fun start next hs => Encoded.pc_step Machine.OneTimePad.keygen FlaggedBlockXor.code
          ReusableBlockPad.code NativeMaskReduction.oracle (caller message) start next hs) target next hn
      simp only [pc, addressIncrement] at *
      omega

/-- A faithful encoding of the active reduction includes its original caller. -/
def sourceEncoding := ReusableBlockPad.NativeObserver.Resources.sourceEncoding
  () [] message FiniteBitEncoding.unit

def fields := FiniteBitEncoding.unit.sum
  ((ConfigurationEncoding.frame FiniteBitEncoding.unit).sum
    (Machine.ConfigurationEncoding.tape.sum (NativeContinuation.Resources.encoding (sourceEncoding message))))

def encoding : FiniteBitEncoding NativeMaskChallenge.Control :=
  (fields message).retract
    (fun target => match target with
      | .querying => .inl ()
      | .loading frame => .inr (.inl frame)
      | .aligning tape => .inr (.inr (.inl tape))
      | .active target => .inr (.inr (.inr target)))
    (fun raw => match raw with
      | .inl _ => .querying
      | .inr (.inl frame) => .loading frame
      | .inr (.inr (.inl tape)) => .aligning tape
      | .inr (.inr (.inr target)) => .active target)
    (fun target => by cases target <;> rfl)

def sourceBits (p e : Nat) := 48 * p + 864 * e ^ 2 + 2616 * e + 1312
def phaseBound (p e : Nat) := 128 * p + 2048 * e ^ 2 + 8192 * e + 8200

theorem source_length (target : RuntimeState Unit) :
    ((sourceEncoding message).encode target).length ≤
      sourceBits (sourcePc message target) (sourceExtent message target) := by
  have hl := Encoded.encoding_length FiniteBitEncoding.unit (fun _ : Unit => 0)
    (fun _ => Nat.le_refl 0) (caller message) target
  have hc := ReusableResponse.Initialized.Resources.cells_bound (fun _ : Unit => 0) (caller message) target
  have hp := Encoded.pc_le_three (caller message) target
  have ht := Encoded.trace_bound (fun _ : Unit => 0) (caller message) target
  change ((Encoded.encoding FiniteBitEncoding.unit).encode (caller message, target)).length ≤ _
  unfold sourceBits sourcePc sourceExtent
  omega

private theorem active_length (target : NativeContinuation.Control (RuntimeState Unit)) :
    ((NativeContinuation.Resources.encoding (sourceEncoding message)).encode target).length + 3 ≤
      phaseBound (NativeContinuation.Growth.pc (sourcePc message) target)
        (NativeContinuation.Growth.extent (sourceExtent message) target) := by
  cases target with
  | producing state =>
      have hs := source_length message state
      simp only [NativeContinuation.Resources.encoding, FiniteBitEncoding.retract_encode_length,
        FiniteBitEncoding.sum_encode_inl_length, NativeContinuation.Growth.pc, NativeContinuation.Growth.extent]
      unfold sourceBits phaseBound at *
      omega
  | observing saved machine =>
      have hs := source_length message saved
      have hm := Machine.ConfigurationEncoding.configuration_length_le machine
      have hCells : machine.tapeCells ≤ 2 * Machine.ControllerExtent.machine machine := by
        simp only [Machine.Configuration.tapeCells, Machine.ControllerExtent.machine]
        omega
      have hq := Nat.pow_le_pow_left
        (Nat.le_max_left (sourceExtent message saved) (Machine.ControllerExtent.machine machine)) 2
      simp only [NativeContinuation.Resources.encoding, FiniteBitEncoding.retract_encode_length,
        FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.prod_encode_length,
        NativeContinuation.Growth.pc, NativeContinuation.Growth.extent]
      unfold sourceBits phaseBound at *
      omega

/-- No phase or retained producer state is omitted from this representation. -/
theorem encoding_length (target : NativeMaskChallenge.Control) :
    ((encoding message).encode target).length ≤ phaseBound (pc message target) (extent message target) := by
  cases target with
  | querying =>
      simp [encoding, fields, FiniteBitEncoding.retract_encode_length,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.unit, pc, phaseBound]
  | loading frame =>
      have hf := ConfigurationEncoding.frame_extent_length_le FiniteBitEncoding.unit (fun _ : Unit => 0)
        (fun _ => Nat.le_refl 0) frame
      have hq := Nat.pow_le_pow_left (Nat.le_max_right (callerExtent message)
        (ControllerExtent.frameExtent (fun _ : Unit => 0) frame)) 2
      simp only [encoding, fields, FiniteBitEncoding.retract_encode_length,
        FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.sum_encode_inl_length, pc, extent]
      unfold phaseBound
      omega
  | aligning tape =>
      have ht := Machine.ConfigurationEncoding.tape_length_le tape
      simp only [encoding, fields, FiniteBitEncoding.retract_encode_length,
        FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.sum_encode_inl_length, pc, extent]
      unfold phaseBound
      omega
  | active target =>
      have ht := active_length message target
      simpa only [encoding, fields, FiniteBitEncoding.retract_encode_length,
        FiniteBitEncoding.sum_encode_inr_length, pc, extent] using ht

theorem phaseBound_mono {firstPc nextPc firstExtent nextExtent : Nat}
    (hPc : firstPc ≤ nextPc) (hExtent : firstExtent ≤ nextExtent) :
    phaseBound firstPc firstExtent ≤ phaseBound nextPc nextExtent := by
  have hq := Nat.pow_le_pow_left hExtent 2
  unfold phaseBound
  omega

def callerBound (e : Nat) := 72 * (2 * e ^ 2 + 5 * e + 1) + 4 * e + 100

theorem caller_extent : callerExtent message ≤ 2 * width + 3 := by
  let c : ReusableBlockPadBackend.Context Unit :=
    ⟨NativeMaskReduction.oracle, (), [], width, message, fun _ => false⟩
  have he := ReusableBlockPadEncodedBackend.initial_extent (fun _ : Unit => 0) c
  have hl : callerExtent message ≤ ReusableResponse.Initialized.Resources.extent (fun _ : Unit => 0)
      (ReusableBlockPad.callerFrame c.state c.trace c.message)
      ((ReusableBlockPadBackend.runtime Unit).initial ReusableBlockPad.code c) := Nat.le_max_left _ _
  exact hl.trans (by simpa only [c, ControllerExtent.traceExtent, Nat.add_zero] using he)

theorem caller_length :
    ((ConfigurationEncoding.frame FiniteBitEncoding.unit).encode (caller message)).length ≤
      callerBound (2 * width + 3) := by
  have hf := ConfigurationEncoding.frame_extent_length_le FiniteBitEncoding.unit (fun _ : Unit => 0)
    (fun _ => Nat.le_refl 0) (caller message)
  have he := caller_extent message
  have hq := Nat.pow_le_pow_left he 2
  have hp : ConfigurationEncoding.pc (caller message).control = 0 := rfl
  rw [hp] at hf
  unfold callerBound callerExtent at *
  omega

/-- Fixed codes are represented outside the runtime phase to avoid creating
repeated code copies inside the state encoder. Caller data remain explicit. -/
def completeEncoding := NativeContinuation.Resources.programEncoding.prod
  (NativeContinuation.Resources.programEncoding.prod
    (NativeContinuation.Resources.programEncoding.prod
      (EncodedStorage.codeEncoding.prod (EncodedStorage.codeEncoding.prod
        (NativeContinuation.Resources.programEncoding.prod
          ((ConfigurationEncoding.frame FiniteBitEncoding.unit).prod (encoding message)))))))

def codeBits (generator copy handler : Program) (source loader : Code) (observer : Program) :=
  2 * (Program.encode generator).length + 2 * (Program.encode copy).length +
    2 * (Program.encode handler).length + 2 * (EncodedStorage.codeEncoding.encode source).length +
    2 * (EncodedStorage.codeEncoding.encode loader).length + 2 * (Program.encode observer).length + 6

theorem codes_length (generator copy handler : Program) (source loader : Code) (observer : Program)
    (target : NativeMaskChallenge.Control) :
    ((completeEncoding message).encode
      (generator, copy, handler, source, loader, observer, caller message, target)).length =
      codeBits generator copy handler source loader observer +
        2 * ((ConfigurationEncoding.frame FiniteBitEncoding.unit).encode (caller message)).length +
        ((encoding message).encode target).length + 1 := by
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length,
    NativeContinuation.Resources.programEncoding, codeBits]
  omega

def bitBound (observer : Program) (width horizon : Nat) :=
  codeBits Machine.OneTimePad.keygen PrivateKeyCopy.code FlaggedBlockXor.code
    ReusableBlockPad.code loadCode observer + 2 * callerBound (2 * width + 3) +
      phaseBound (horizon * addressIncrement observer) (3 * width + 6 + horizon * 7) + 1

/-- Every supported prefix of the full original query/loading/alignment/
masking/observation machine has a bound on its complete encoded state. -/
theorem peak (distribution : PMF (Bits width)) (observer : Program) (horizon elapsed : Nat)
    (hTime : elapsed ≤ horizon) (target : NativeMaskChallenge.Control)
    (h : target ∈ (TimedExecution.eval (NativeMaskChallenge.step distribution message observer)
      elapsed .querying).support) :
    ((completeEncoding message).encode
      (Machine.OneTimePad.keygen, PrivateKeyCopy.code, FlaggedBlockXor.code,
        ReusableBlockPad.code, loadCode, observer, caller message, target)).length ≤
      bitBound observer width horizon := by
  have he := ResourceGrowth.prefix_bound (NativeMaskChallenge.step distribution message observer)
    (extent message) 7 (extent_step message distribution observer) horizon elapsed hTime .querying target h
  have hp := ResourceGrowth.prefix_bound (NativeMaskChallenge.step distribution message observer)
    (pc message) (addressIncrement observer) (pc_step message distribution observer)
    horizon elapsed hTime .querying target h
  have hi := caller_extent message
  have hl := encoding_length message target
  have hc := caller_length message
  have hExtent : extent message target ≤ 3 * width + 6 + horizon * 7 := by
    change extent message target ≤ callerExtent message + width + 3 + horizon * 7 at he
    omega
  have hPc : pc message target ≤ horizon * addressIncrement observer := by
    simpa only [pc, Nat.zero_add] using hp
  have hb := hl.trans (phaseBound_mono hPc hExtent)
  rw [codes_length]
  unfold bitBound
  omega

/-- Fixed runtime and observer codes preserve polynomial whole-prefix space. -/
theorem bitBound_polynomial (observer : Program) {width horizon : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hTime : PolynomiallyBounded horizon) :
    PolynomiallyBounded (fun n => bitBound observer (width n) (horizon n)) := by
  have hc := ((PolynomiallyBounded.const 2).mul hWidth).add (PolynomiallyBounded.const 3)
  have hCaller : PolynomiallyBounded (fun n => callerBound (2 * width n + 3)) := by
    have h := (((PolynomiallyBounded.const 72).mul
      ((((PolynomiallyBounded.const 2).mul (hc.mul hc)).add
        ((PolynomiallyBounded.const 5).mul hc)).add (PolynomiallyBounded.const 1))).add
          ((PolynomiallyBounded.const 4).mul hc)).add (PolynomiallyBounded.const 100)
    simpa only [callerBound, pow_two] using h
  have hp := hTime.mul (PolynomiallyBounded.const (addressIncrement observer))
  have he := (((PolynomiallyBounded.const 3).mul hWidth).add (PolynomiallyBounded.const 6)).add
    (hTime.mul (PolynomiallyBounded.const 7))
  have hPhase : PolynomiallyBounded (fun n => phaseBound
      (horizon n * addressIncrement observer) (3 * width n + 6 + horizon n * 7)) := by
    have h := ((((PolynomiallyBounded.const 128).mul hp).add
      ((PolynomiallyBounded.const 2048).mul (he.mul he))).add
        ((PolynomiallyBounded.const 8192).mul he)).add (PolynomiallyBounded.const 8200)
    simpa only [phaseBound, pow_two] using h
  exact (((PolynomiallyBounded.const (codeBits Machine.OneTimePad.keygen PrivateKeyCopy.code
    FlaggedBlockXor.code ReusableBlockPad.code loadCode observer)).add
      ((PolynomiallyBounded.const 2).mul hCaller)).add hPhase).add (PolynomiallyBounded.const 1)

end Foundation.Symmetric.EncryptThenMAC.NativeMaskChallenge.WholeResources
