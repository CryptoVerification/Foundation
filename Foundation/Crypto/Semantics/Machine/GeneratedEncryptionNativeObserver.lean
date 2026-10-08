import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionPhysical
import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionCode
import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionResources
import Foundation.Crypto.Semantics.Machine.NativeEndDataObservation
import Foundation.Crypto.Semantics.Machine.NativeEquivalentArrivalComposition
import Foundation.Crypto.Semantics.Machine.NativeEquivalentObservation

/-! Encryption, physical ciphertext preparation and an arbitrary fixed
polynomial-time observer form one native program from plaintext alone.
No ciphertext loader or serializer is run outside the linked machine.
The observer receives the prefix-free ciphertext packet. Perfect secrecy
includes the linked program's entire final state and actual first-halt time. -/
namespace Machine.GeneratedBlockEncryption
open Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false
variable (O : PolynomialObserver)

def nativeObserverInput (message : List Bool) (state : Configuration) : NativeEndDataObservation.Input :=
  {data := state.inputTape.bits, sourceBlanks := 1, scratchRight := 3 * message.length + 2}

theorem nativeObserverInput_length (message : List Bool) (state : Configuration)
    (hState : state ∈ (link.native.execution.semantics message).support) :
    (nativeObserverInput message state).data.length = message.length := by
  rw [physical_semantics, PMF.mem_support_map_iff] at hState
  obtain ⟨key, _, rfl⟩ := hState
  change (physicalCipherExit (OneTimePad.xorList key.toList message)).inputTape.bits.length = _
  rw [physicalCipherExit_bits, xorList_length _ _ (Bits.length_toList key)]

theorem nativeObserver_handoff (message : List Bool) (state : Configuration)
    (hState : state ∈ (link.native.execution.semantics message).support) :
    (state.resumeAt 0).Equivalent
      ((NativeEndDataObservation.link O).component.procedure.execution.entry (nativeObserverInput message state)) := by
  rw [physical_semantics, PMF.mem_support_map_iff] at hState
  obtain ⟨key, _, rfl⟩ := hState
  have hLength := xorList_length key.toList message (Bits.length_toList key)
  change (physicalCipherExit (OneTimePad.xorList key.toList message)).resumeAt 0 |>.Equivalent
    (NativeEndDataObservation.initial (nativeObserverInput message (physicalCipherExit (OneTimePad.xorList key.toList message))))
  have hEq : (physicalCipherExit (OneTimePad.xorList key.toList message)).resumeAt 0 =
      NativeEndDataObservation.initial
        (nativeObserverInput message (physicalCipherExit (OneTimePad.xorList key.toList message))) := by
    simp [NativeEndDataObservation.initial, NativeEndDataObservation.rewindInput, NativeEndDataObservation.scratch,
      NativeBitstringRewind.initial, nativeObserverInput, physicalCipherExit,
      Configuration.resumeAt, Tape.bits, hLength]
  rw [hEq]
  exact Configuration.Equivalent.refl _

theorem nativeObserver_bounded (message : List Bool) (state : Configuration)
    (hState : state ∈ (link.native.execution.semantics message).support) :
    (NativeEndDataObservation.link O).component.procedure.execution.budget (nativeObserverInput message state) ≤
      NativeEndDataObservation.timeBound O message.length := by
  change (NativeEndDataObservation.link O).native.execution.budget _ ≤ _
  rw [NativeEndDataObservation.budget, nativeObserverInput_length message state hState]

noncomputable def observedLink : TypedNativeComposition.Link link.native
    (NativeEndDataObservation.link O).component.equivalentEntries.procedure :=
  link.appendEquivalent (NativeEndDataObservation.link O).component nativeObserverInput (nativeObserver_handoff O)
    (fun message => NativeEndDataObservation.timeBound O message.length) (nativeObserver_bounded O)

def observedCode : Program := fixedCode.followedBy (NativeEndDataObservation.fixedCode O)

theorem observedCode_eq : observedCode O = (observedLink O).code := rfl

theorem observed_code_length : (observedLink O).code.length = O.code.length + 141 := by
  rw [(observedLink O).code_length]
  change link.code.length + (NativeEndDataObservation.link O).code.length + 3 = _
  rw [code_length, NativeEndDataObservation.code_length]
  omega

def observedTimeBound (size : Nat) : Nat := 79 * size + 64 + O.budget (2 * size + 1)

theorem observed_budget (message : List Bool) :
    (observedLink O).native.execution.budget message = observedTimeBound O message.length := by
  rw [(observedLink O).budget, budget]
  change 61 * message.length + 40 + NativeEndDataObservation.timeBound O message.length + 1 = _
  unfold observedTimeBound NativeEndDataObservation.timeBound
  omega

theorem observed_time_polynomial : PolynomiallyBounded (observedTimeBound O) :=
  ((((PolynomiallyBounded.const 79).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 64)).add
    (O.budget_profile_polynomial
      (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))))

theorem observed_entry (message : List Bool) :
    (observedLink O).native.execution.entry message = Configuration.initial message := by
  rw [(observedLink O).native_entry, entry]

theorem observed_run (message : List Bool) (horizon : Nat) (hTime : observedTimeBound O message.length ≤ horizon) :
    evalConfigWithin (observedLink O).code (Configuration.initial message) horizon =
      (observedLink O).native.execution.semantics message := by
  have h := (observedLink O).run message horizon (by
    change (observedLink O).native.execution.budget message ≤ horizon
    rw [observed_budget]
    exact hTime)
  rw [entry] at h
  exact h

theorem observed_decision (message : List Bool) :
    ((observedLink O).native.execution.semantics message).map NativeSerializedObservation.decision =
      (link.native.execution.semantics message).bind
        (fun state => O.observe (FiniteBitEncoding.delimit state.inputTape.bits)) := by
  have h := link.appendEquivalent_observe (NativeEndDataObservation.link O).component nativeObserverInput
    (nativeObserver_handoff O) (fun message => NativeEndDataObservation.timeBound O message.length)
    (nativeObserver_bounded O) NativeSerializedObservation.decision
    (fun _ _ h => congrArg (fun current => current.getD false) h.2.2.1.1) message
  change ((observedLink O).native.execution.semantics message).map NativeSerializedObservation.decision = _ at h
  rw [h]
  congr 1
  funext state
  change ((NativeEndDataObservation.link O).native.execution.semantics (nativeObserverInput message state)).map
    NativeSerializedObservation.decision = _
  exact NativeEndDataObservation.observe O _

theorem observed_decision_uniform {width : Nat} (message : Bits width) :
    ((observedLink O).native.execution.semantics message.toList).map NativeSerializedObservation.decision =
      (uniform (Bits width)).bind (fun ciphertext => O.observe (FiniteBitEncoding.delimit ciphertext.toList)) := by
  rw [observed_decision, physical_semantics_uniform, PMF.bind_map]
  simp only [Function.comp_def, physicalCipherExit_bits]

noncomputable def observedCosted (message : List Bool) : PMF (Configuration × Nat) :=
  (observedLink O).component.firstArrival.procedure.execution.costed message

/-- The whole actual state/time law uses the real ciphertext endpoint.
The continuation depends on the ciphertext and O, never on plaintext. -/
theorem observed_costed_physical (message : List Bool) :
    observedCosted O message = (arrival.procedure.execution.costed message).bind (fun first =>
      (runToBoundary (stepPMF (NativeEndDataObservation.link O).code) Configuration.halted
        (NativeEndDataObservation.timeBound O first.1.inputTape.bits.length) (first.1.resumeAt 0)).map (fun second =>
          ({second.1.resumeAt (observedLink O).finalPc with halted := true}, first.2 + second.2 + 1))) := by
  have h := link.appendEquivalent_firstArrival_physical (NativeEndDataObservation.link O).component
    nativeObserverInput (nativeObserver_handoff O) (fun message => NativeEndDataObservation.timeBound O message.length)
    (nativeObserver_bounded O) message
  change observedCosted O message = (arrival.procedure.execution.costed message).bind _ at h
  have hBudget (state : Configuration) :
      (NativeEndDataObservation.link O).component.procedure.execution.budget (nativeObserverInput message state) =
        NativeEndDataObservation.timeBound O state.inputTape.bits.length :=
    NativeEndDataObservation.budget O (nativeObserverInput message state)
  simp_rw [hBudget] at h
  exact h

theorem observed_costed_perfect_secrecy {width : Nat} (left right : Bits width) :
    observedCosted O left.toList = observedCosted O right.toList := by
  rw [observed_costed_physical, observed_costed_physical]
  exact arrival_representation_perfect_secrecy left right _

theorem observed_costed_decision_uniform {width : Nat} (message : Bits width) :
    (observedCosted O message.toList).map (fun result => NativeSerializedObservation.decision result.1) =
      (uniform (Bits width)).bind (fun ciphertext => O.observe (FiniteBitEncoding.delimit ciphertext.toList)) := by
  have h := (observedLink O).component.firstArrival.procedure.execution.correct message.toList
  change (observedCosted O message.toList).map Prod.fst =
    ((observedLink O).native.execution.semantics message.toList).map id at h
  rw [PMF.map_id] at h
  rw [← observed_decision_uniform O message, ← h, PMF.map_comp]
  rfl

theorem observed_costed_halted (message : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (observedCosted O message).support) : result.1.halted = true :=
  (observedLink O).component.firstArrival_halted message result hResult

theorem observed_costed_bound (message : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (observedCosted O message).support) : result.2 ≤ observedTimeBound O message.length := by
  change result ∈ ((observedLink O).component.firstArrival.procedure.execution.costed message).support at hResult
  rw [(observedLink O).component.firstArrival_costed] at hResult
  have h := runToBoundary_bounded _ _ _ _ result hResult
  change result.2 ≤ (observedLink O).native.execution.budget message at h
  rwa [observed_budget] at h

theorem observed_costed_horizon (message : List Bool) (horizon : Nat)
    (hTime : observedTimeBound O message.length ≤ horizon) :
    runToBoundary (stepPMF (observedLink O).code) Configuration.halted horizon (Configuration.initial message) =
      observedCosted O message := by
  have h := (observedLink O).component.firstArrival_costed_horizon message horizon (by
    change (observedLink O).native.execution.budget message ≤ horizon
    rw [observed_budget]
    exact hTime)
  change runToBoundary _ _ _ ((observedLink O).native.execution.entry message) = _ at h
  rw [observed_entry] at h
  exact h

theorem observed_run_costed_perfect_secrecy {width : Nat} (left right : Bits width)
    (horizon : Nat) (hTime : observedTimeBound O width ≤ horizon) :
    runToBoundary (stepPMF (observedLink O).code) Configuration.halted horizon (Configuration.initial left.toList) =
      runToBoundary (stepPMF (observedLink O).code) Configuration.halted horizon (Configuration.initial right.toList) := by
  rw [observed_costed_horizon O left.toList horizon (by simpa only [Bits.length_toList] using hTime),
    observed_costed_horizon O right.toList horizon (by simpa only [Bits.length_toList] using hTime)]
  exact observed_costed_perfect_secrecy O left right

def observedBitBound (size : Nat) : Nat :=
  StructuredCodeEncoding.bound (observedCode O) 0 (size + 2) (observedTimeBound O size)

theorem observed_space_polynomial : PolynomiallyBounded (observedBitBound O) :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2)) (observed_time_polynomial O)

theorem observed_storage_peak (message : List Bool) (elapsed : Nat)
    (hElapsed : elapsed ≤ observedTimeBound O message.length) (state : Configuration)
    (hState : state ∈ (eval (stepPMF (observedLink O).code) elapsed (Configuration.initial message)).support) :
    (StructuredCodeEncoding.completeEncoding.encode ((observedLink O).code, state)).length ≤ observedBitBound O message.length :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state hState).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (PolynomialObserver.initial_cells_le message) (Nat.le_refl _))

theorem observed_storage_costed (message : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (observedCosted O message).support) :
    (StructuredCodeEncoding.completeEncoding.encode ((observedLink O).code, result.1)).length ≤
      StructuredCodeEncoding.bound (observedCode O) 0 (message.length + 2) result.2 := by
  have h := (observedLink O).component.firstArrival_operational message result hResult
  change result.1 ∈ (eval (stepPMF (observedLink O).code) result.2
    ((observedLink O).native.execution.entry message)).support at h
  rw [observed_entry] at h
  exact (StructuredCodeEncoding.peak _ _ result.2 (Nat.le_refl _) _ result.1 h).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (PolynomialObserver.initial_cells_le message) (Nat.le_refl _))

end Machine.GeneratedBlockEncryption
