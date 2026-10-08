import Foundation.Examples.ReusableBlockPadBackend

/-! Register whole-prefix storage bounds alongside the actual pad execution.
The observation predicate is mathematical; its implementation and storage
are not part of this encryption execution's measured state. -/
namespace Foundation.Examples.ReusableBlockPadEncodedBackend
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ReusableResponse.Initialized
open CryptoLogic.General ContractObservedBackend ReusableBlockPadBackend
universe v
set_option backward.isDefEq.respectTransparency false
variable {State : Type v} (width : Nat → Nat) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (F : InstanceFamily (goal width))
    (A : AdversaryFamily (goal width) F)
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (initialPc initialExtent increments responses : Nat → Nat)
    (hWidth : PolynomiallyBounded width) (hPc : PolynomiallyBounded initialPc)
    (hExtent : PolynomiallyBounded initialExtent) (hIncrement : PolynomiallyBounded increments)
    (hResponse : PolynomiallyBounded responses)
    (hAddress : ∀ n side,
      Encoded.maxPc (ReusableBlockPad.callerFrame state trace (context width oracle state trace F A n side).message)
        ((runtime State).initial ReusableBlockPad.code (context width oracle state trace F A n side)) ≤ initialPc n)
    (hInitial : ∀ n side,
      Resources.extent stateSize (ReusableBlockPad.callerFrame state trace (context width oracle state trace F A n side).message)
        ((runtime State).initial ReusableBlockPad.code (context width oracle state trace F A n side)) ≤ initialExtent n)
    (hOracle : ∀ n state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + increments n ∧ result.2.length ≤ responses n)

def measure (code : Code) (c : Context State) (target : Control State) :=
  ((Encoded.completeEncoding E).encode
    (Machine.OneTimePad.keygen, PrivateKeyCopy.code, FlaggedBlockXor.code, code,
      (ReusableBlockPad.callerFrame c.state c.trace c.message, target))).length

def bitCap : Nat → Nat := fun n =>
  Encoded.bound Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
    (initialPc n) (initialExtent n) (55 * width n + 41) (increments n) (responses n)

theorem initial_address (c : Context State) :
    Encoded.maxPc (ReusableBlockPad.callerFrame c.state c.trace c.message)
      ((runtime State).initial ReusableBlockPad.code c) = 0 := rfl

private theorem loaded_cells (bits : List Bool) : (ResponseLoading.loaded bits).cells = bits.length + 1 := by
  cases bits with
  | nil => rfl
  | cons bit rest =>
      simp [ResponseLoading.loaded, ResponseLoading.fromCells, Tape.cells]
      omega

private theorem input_cells (bits : List Bool) : (Tape.ofBits bits).cells ≤ bits.length + 1 := by
  cases bits with
  | nil => exact Nat.le_refl 1
  | cons bit rest =>
      simp [Tape.ofBits, Tape.cells]
      omega

theorem initial_extent (c : Context State) :
    Resources.extent stateSize (ReusableBlockPad.callerFrame c.state c.trace c.message)
      ((runtime State).initial ReusableBlockPad.code c) ≤
        2 * c.width + stateSize c.state + ControllerExtent.traceExtent c.trace + 3 := by
  have hi := input_cells (List.replicate c.width true)
  simp only [List.length_replicate] at hi
  have ho : (ResponseLoading.loaded (FlaggedBlockXor.request c.message.toList)).cells = 2 * c.width + 2 := by
    rw [loaded_cells, FlaggedBlockXor.request_length, Bits.length_toList]
  change max (max (stateSize c.state)
    (max (max 1 (ResponseLoading.loaded (FlaggedBlockXor.request c.message.toList)).cells)
      (ControllerExtent.traceExtent c.trace)))
    (max (Tape.ofBits (List.replicate c.width true)).cells 1) ≤ _
  rw [ho]
  omega

def defaultExtent : Nat → Nat := fun n =>
  2 * width n + stateSize state + ControllerExtent.traceExtent trace + 3

theorem defaultExtent_polynomial (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (defaultExtent width state trace stateSize) :=
  ((((PolynomiallyBounded.const 2).mul hWidth).add (PolynomiallyBounded.const (stateSize state))).add
    (PolynomiallyBounded.const (ControllerExtent.traceExtent trace))).add (PolynomiallyBounded.const 3)

include hState hWidth hPc hExtent hIncrement hResponse hAddress hInitial hOracle in
theorem peak : (profile width oracle state trace F A).WithinPeak (runtime State) (measure E)
    (bitCap width initialPc initialExtent increments responses) F ReusableBlockPad.code := by
  refine ⟨ReusableBlockPad.Resources.bound_polynomial hWidth hPc hExtent hIncrement hResponse, ?_⟩
  intro n side elapsed hElapsed target hTarget
  have h := Encoded.encoded_peak E stateSize hState Machine.OneTimePad.keygen FlaggedBlockXor.code
    ReusableBlockPad.code oracle
    (ReusableBlockPad.callerFrame state trace (context width oracle state trace F A n side).message)
    (increments n) (responses n) (hOracle n) (55 * width n + 41) elapsed hElapsed
    ((runtime State).initial ReusableBlockPad.code (context width oracle state trace F A n side)) target hTarget
  exact h.trans (Encoded.bound_mono_initial Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
    (hAddress n side) (hInitial n side) (55 * width n + 41) (increments n) (responses n))

noncomputable def registration := peakRegistration (runtime State) (modelGame width) (advantage_eq width) (measure E)

include hState hWidth hPc hExtent hIncrement hResponse hAddress hInitial hOracle in
noncomputable def witness :
    (registration (State := State) width E).object.Witness F A :=
  peakWitness (runtime State) (modelGame width) (advantage_eq width) (measure E) F A
    ReusableBlockPad.code (profile width oracle state trace F A)
    (bitCap width initialPc initialExtent increments responses)
    (executes width oracle state trace F A hWidth)
    (peak width oracle state trace F A E stateSize hState initialPc initialExtent increments responses
      hWidth hPc hExtent hIncrement hResponse hAddress hInitial hOracle)
    (fun _ _ => rfl)

theorem secure : (registration (State := State) width E).object.Secure F := by
  intro adversary _
  exact negligible_advantage width F adversary

include hState hWidth hIncrement hResponse hOracle in
/-- Default initial bounds are discharged from actual tape layouts. Only
the public width and external-state/response profiles remain to be bounded. -/
noncomputable def defaultWitness : (registration (State := State) width E).object.Witness F A :=
  witness width oracle state trace F A E stateSize hState (fun _ => 0)
    (defaultExtent width state trace stateSize) increments responses hWidth
    (PolynomiallyBounded.const 0) (defaultExtent_polynomial width state trace stateSize hWidth)
    hIncrement hResponse
    (fun n side => le_of_eq (initial_address (context width oracle state trace F A n side)))
    (fun n side => initial_extent stateSize (context width oracle state trace F A n side)) hOracle

include hState hWidth hIncrement hResponse hOracle in
theorem defaultWitness_code :
    (defaultWitness width oracle state trace F A E stateSize hState increments responses
      hWidth hIncrement hResponse hOracle).code = ReusableBlockPad.code := rfl

noncomputable def unitOracle : BitOracle Unit := fun _ _ => PMF.pure ((), [])

private theorem unitOracle_bound (n : Nat) (state : Unit) (request : List Bool) (result : Unit × List Bool)
    (h : result ∈ (unitOracle state request).support) :
    (0 : Nat) ≤ 0 + (fun _ : Nat => 0) n ∧ result.2.length ≤ (fun _ : Nat => 0) n := by
  rw [unitOracle, PMF.mem_support_pure_iff] at h
  subst result
  simp

/-- A fully instantiated storage-certified witness, requiring only a
polynomial width profile. The empty external state and oracle bounds are
proved here, not supplied as cryptographic assumptions. -/
noncomputable def unitWitness (hWidth : PolynomiallyBounded width) :
    (registration (State := Unit) width FiniteBitEncoding.unit).object.Witness F A :=
  defaultWitness width unitOracle () [] F A FiniteBitEncoding.unit (fun _ => 0)
    (fun _ => Nat.le_refl 0) (fun _ => 0) (fun _ => 0)
    hWidth (PolynomiallyBounded.const 0) (PolynomiallyBounded.const 0) unitOracle_bound

theorem unitWitness_code (hWidth : PolynomiallyBounded width) :
    (unitWitness width F A hWidth).code = ReusableBlockPad.code := rfl

theorem unitWitness_bitCap (hWidth : PolynomiallyBounded width) :
    (unitWitness width F A hWidth).resources.2 = fun n =>
      Encoded.bound Machine.OneTimePad.keygen FlaggedBlockXor.code ReusableBlockPad.code
        0 (2 * width n + 3) (55 * width n + 41) 0 0 := rfl

end Foundation.Examples.ReusableBlockPadEncodedBackend
