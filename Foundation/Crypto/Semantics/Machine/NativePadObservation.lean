import Foundation.Crypto.Semantics.Machine.NativePadEncryption
import Foundation.Crypto.Semantics.Machine.NativeEndDataObservation
import Foundation.Crypto.Semantics.Machine.NativeEquivalentArrivalComposition
import Foundation.Crypto.Semantics.Machine.NativeEquivalentObservation

/-! Any supplied pad is masked, erased, serialized and observed by one
fixed native program. Its full first-halt state/time law depends only on
ciphertext. No uniform-pad assumption or PRG assumption is used here. -/
namespace Machine.NativePadObservation
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
variable (O : PolynomialObserver)

def observerInput (input : NativePadEncryption.Input) (state : Configuration) : NativeEndDataObservation.Input :=
  {data := state.inputTape.bits, sourceBlanks := 1, scratchRight := 3 * input.message.length + 2}

theorem observerInput_length (input : NativePadEncryption.Input) (state : Configuration)
    (hState : state ∈ (NativePadEncryption.link.native.execution.semantics input).support) :
    (observerInput input state).data.length = input.message.length := by
  rw [NativePadEncryption.semantics, PMF.mem_support_pure_iff] at hState
  subst state
  simp [observerInput, NativePadEncryption.finish, NativePadEncryption.publicExit, Tape.bits,
    NativePadEncryption.cipher_length]

theorem handoff (input : NativePadEncryption.Input) (state : Configuration)
    (hState : state ∈ (NativePadEncryption.link.native.execution.semantics input).support) :
    (state.resumeAt 0).Equivalent
      ((NativeEndDataObservation.link O).component.procedure.execution.entry (observerInput input state)) := by
  rw [NativePadEncryption.semantics, PMF.mem_support_pure_iff] at hState
  subst state
  change (NativePadEncryption.finish input).resumeAt 0 |>.Equivalent
    (NativeEndDataObservation.initial (observerInput input (NativePadEncryption.finish input)))
  have hEq : (NativePadEncryption.finish input).resumeAt 0 =
      NativeEndDataObservation.initial (observerInput input (NativePadEncryption.finish input)) := by
    simp [NativeEndDataObservation.initial, NativeEndDataObservation.rewindInput, NativeEndDataObservation.scratch,
      NativeBitstringRewind.initial, observerInput, NativePadEncryption.finish, NativePadEncryption.publicExit,
      Configuration.resumeAt, Tape.bits, NativePadEncryption.cipher_length]
  rw [hEq]
  exact Configuration.Equivalent.refl _

theorem bounded (input : NativePadEncryption.Input) (state : Configuration)
    (hState : state ∈ (NativePadEncryption.link.native.execution.semantics input).support) :
    (NativeEndDataObservation.link O).component.procedure.execution.budget (observerInput input state) ≤
      NativeEndDataObservation.timeBound O input.message.length := by
  change (NativeEndDataObservation.link O).native.execution.budget _ ≤ _
  rw [NativeEndDataObservation.budget, observerInput_length input state hState]

noncomputable def link : TypedNativeComposition.Link NativePadEncryption.link.native
    (NativeEndDataObservation.link O).component.equivalentEntries.procedure :=
  NativePadEncryption.link.appendEquivalent (NativeEndDataObservation.link O).component observerInput (handoff O)
    (fun input => NativeEndDataObservation.timeBound O input.message.length) (bounded O)

def fixedCode : Program := NativePadEncryption.fixedCode.followedBy (NativeEndDataObservation.fixedCode O)

theorem fixedCode_eq : fixedCode O = (link O).code := rfl

theorem code_length : (link O).code.length = O.code.length + 92 := by
  rw [(link O).code_length]
  change NativePadEncryption.link.code.length + (NativeEndDataObservation.link O).code.length + 3 = _
  rw [NativePadEncryption.code_length, NativeEndDataObservation.code_length]
  omega

def timeBound (size : Nat) : Nat := 54 * size + 40 + O.budget (2 * size + 1)

theorem budget (input : NativePadEncryption.Input) :
    (link O).native.execution.budget input = timeBound O input.message.length := by
  rw [(link O).budget, NativePadEncryption.budget]
  change 36 * input.message.length + 16 + NativeEndDataObservation.timeBound O input.message.length + 1 = _
  unfold timeBound NativeEndDataObservation.timeBound
  omega

theorem time_polynomial : PolynomiallyBounded (timeBound O) :=
  ((((PolynomiallyBounded.const 54).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 40)).add
    (O.budget_profile_polynomial
      (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))))

theorem entry (input : NativePadEncryption.Input) :
    (link O).native.execution.entry input = NativePadEncryption.initial input := by
  rw [(link O).native_entry]
  rfl

theorem observe (input : NativePadEncryption.Input) :
    ((link O).native.execution.semantics input).map NativeSerializedObservation.decision =
      O.observe (FiniteBitEncoding.delimit (NativePadEncryption.cipher input)) := by
  have h := NativePadEncryption.link.appendEquivalent_observe (NativeEndDataObservation.link O).component observerInput
    (handoff O) (fun input => NativeEndDataObservation.timeBound O input.message.length) (bounded O)
    NativeSerializedObservation.decision (fun _ _ h => congrArg (fun current => current.getD false) h.2.2.1.1) input
  change ((link O).native.execution.semantics input).map NativeSerializedObservation.decision = _ at h
  rw [h, NativePadEncryption.semantics, PMF.pure_bind]
  change ((NativeEndDataObservation.link O).native.execution.semantics
    (observerInput input (NativePadEncryption.finish input))).map NativeSerializedObservation.decision = _
  rw [NativeEndDataObservation.observe]
  simp [observerInput, NativePadEncryption.finish, NativePadEncryption.publicExit, Tape.bits]

noncomputable def costed (input : NativePadEncryption.Input) : PMF (Configuration × Nat) :=
  (link O).component.firstArrival.procedure.execution.costed input

noncomputable def publicCosted (ciphertext : List Bool) : PMF (Configuration × Nat) :=
  (runToBoundary (stepPMF (NativeEndDataObservation.link O).code) Configuration.halted
    (NativeEndDataObservation.timeBound O ciphertext.length) ((NativePadEncryption.publicExit ciphertext).resumeAt 0)).map
      (fun second => ({second.1.resumeAt (link O).finalPc with halted := true},
        36 * ciphertext.length + 16 + second.2 + 1))

/-- The original pad and plaintext are absent from the entire exit/time
law except through ciphertext. This includes observer work and randomness. -/
theorem costed_public (input : NativePadEncryption.Input) :
    costed O input = publicCosted O (NativePadEncryption.cipher input) := by
  have h := NativePadEncryption.link.appendEquivalent_firstArrival_physical (NativeEndDataObservation.link O).component
    observerInput (handoff O) (fun input => NativeEndDataObservation.timeBound O input.message.length) (bounded O) input
  change costed O input = (NativePadEncryption.link.component.firstArrival.procedure.execution.costed input).bind _ at h
  have hBudget (state : Configuration) :
      (NativeEndDataObservation.link O).component.procedure.execution.budget (observerInput input state) =
        NativeEndDataObservation.timeBound O state.inputTape.bits.length :=
    NativeEndDataObservation.budget O (observerInput input state)
  simp_rw [hBudget] at h
  rw [NativePadEncryption.firstArrival_joint, PMF.pure_bind] at h
  change costed O input =
    (runToBoundary (stepPMF (NativeEndDataObservation.link O).code) Configuration.halted
      (NativeEndDataObservation.timeBound O (NativePadEncryption.finish input).inputTape.bits.length)
      ((NativePadEncryption.finish input).resumeAt 0)).map
        (fun second => ({second.1.resumeAt (link O).finalPc with halted := true},
          36 * input.message.length + 16 + second.2 + 1)) at h
  simpa only [publicCosted, NativePadEncryption.finish, NativePadEncryption.publicExit_bits,
    NativePadEncryption.cipher_length] using h

theorem costed_distribution (inputs : PMF NativePadEncryption.Input) :
    inputs.bind (costed O) = (inputs.map NativePadEncryption.cipher).bind (publicCosted O) := by
  rw [PMF.bind_map]
  congr 1
  funext input
  exact costed_public O input

theorem costed_observe (input : NativePadEncryption.Input) :
    (costed O input).map (fun result => NativeSerializedObservation.decision result.1) =
      O.observe (FiniteBitEncoding.delimit (NativePadEncryption.cipher input)) := by
  have h := (link O).component.firstArrival.procedure.execution.correct input
  change (costed O input).map Prod.fst = ((link O).native.execution.semantics input).map id at h
  rw [PMF.map_id] at h
  rw [← observe O input, ← h, PMF.map_comp]
  rfl

theorem costed_halted (input : NativePadEncryption.Input) (result : Configuration × Nat)
    (hResult : result ∈ (costed O input).support) : result.1.halted = true :=
  (link O).component.firstArrival_halted input result hResult

theorem costed_bound (input : NativePadEncryption.Input) (result : Configuration × Nat)
    (hResult : result ∈ (costed O input).support) : result.2 ≤ timeBound O input.message.length := by
  rw [costed, (link O).component.firstArrival_costed] at hResult
  have h := runToBoundary_bounded _ _ _ _ result hResult
  change result.2 ≤ (link O).native.execution.budget input at h
  rwa [budget] at h

theorem costed_horizon (input : NativePadEncryption.Input) (horizon : Nat) (hTime : timeBound O input.message.length ≤ horizon) :
    runToBoundary (stepPMF (link O).code) Configuration.halted horizon (NativePadEncryption.initial input) = costed O input := by
  have h := (link O).component.firstArrival_costed_horizon input horizon (by
    change (link O).native.execution.budget input ≤ horizon
    rw [budget]
    exact hTime)
  change runToBoundary _ _ _ ((link O).native.execution.entry input) = _ at h
  rw [entry] at h
  exact h

def bitBound (size : Nat) : Nat := StructuredCodeEncoding.bound (fixedCode O) 0 (4 * size + 5) (timeBound O size)

theorem space_polynomial : PolynomiallyBounded (bitBound O) :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 5)) (time_polynomial O)

theorem storage_peak (input : NativePadEncryption.Input) (elapsed : Nat) (hElapsed : elapsed ≤ timeBound O input.message.length)
    (state : Configuration)
    (hState : state ∈ (eval (stepPMF (link O).code) elapsed (NativePadEncryption.initial input)).support) :
    (StructuredCodeEncoding.completeEncoding.encode ((link O).code, state)).length ≤ bitBound O input.message.length :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state hState).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (by rw [NativePadEncryption.initial_cells]) (Nat.le_refl _))

end Machine.NativePadObservation
