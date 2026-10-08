import Foundation.Crypto.Semantics.Machine.NativePadObservation

/-! Preparation with physically retained blank padding. The actual return
tapes execute the original encryption/observer code. Only cell equivalence
is required; no finite tape representation is normalized for free. Full
representation equality is not asserted, and storage counts actual cells. -/
namespace Machine.NativePadPipeline
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

structure PhysicalPreparation (Input : Type u) where
  component : NativeComponent Input NativePadEncryption.Input
  read : Input → Configuration → NativePadEncryption.Input
  read_return : ∀ input output, output ∈ (component.procedure.execution.semantics input).support →
    read input ((component.procedure.execution.exit input output).resumeAt (component.procedure.code.length + 1)) = output
  handoff : ∀ input output, output ∈ (component.procedure.execution.semantics input).support →
    ((component.procedure.execution.exit input output).resumeAt 0).Equivalent (NativePadEncryption.initial output)
  width : Input → Nat
  width_eq : ∀ input output, output ∈ (component.procedure.execution.semantics input).support →
    output.message.length = width input

namespace PhysicalPreparation

variable {Input : Type u} (F : PhysicalPreparation Input) (O : PolynomialObserver)

noncomputable def observerInput (input : Input) (output : NativePadEncryption.Input) :
    (NativePadObservation.link O).component.EquivalentInput := by
  classical
  by_cases h : output ∈ (F.component.procedure.execution.semantics input).support
  · exact ⟨output, (F.component.procedure.execution.exit input output).resumeAt 0,
      by
        change ((F.component.procedure.execution.exit input output).resumeAt 0).Equivalent
          ((NativePadObservation.link O).native.execution.entry output)
        rw [NativePadObservation.entry]
        exact F.handoff input output h⟩
  · exact ⟨output, (NativePadObservation.link O).native.execution.entry output, Configuration.Equivalent.refl _⟩

theorem observerInput_logical (input : Input) (output : NativePadEncryption.Input) :
    (observerInput F O input output).logical = output := by
  classical
  unfold observerInput
  split_ifs <;> rfl

noncomputable def link : TypedNativeComposition.Link F.component.procedure
    (NativePadObservation.link O).component.equivalentEntries.procedure :=
  F.component.link (NativePadObservation.link O).component.equivalentEntries F.read F.read_return
    (observerInput F O) (by
      intro input output h
      classical
      change ((observerInput F O input output).actual).rebasePc _ = _
      simp only [observerInput, dif_pos h]
      simp [Configuration.resumeAt, Configuration.rebasePc])
    (fun input => NativePadObservation.timeBound O (F.width input)) (by
      intro input output h
      change (NativePadObservation.link O).native.execution.budget (observerInput F O input output).logical ≤ _
      rw [observerInput_logical, NativePadObservation.budget, F.width_eq input output h])

def fixedCode : Program := F.component.procedure.code.followedBy (NativePadObservation.fixedCode O)

theorem fixedCode_eq : fixedCode F O = (link F O).code := rfl

theorem code_length : (link F O).code.length = F.component.procedure.code.length + O.code.length + 95 := by
  rw [(link F O).code_length]
  change F.component.procedure.code.length + (NativePadObservation.link O).code.length + 3 = _
  rw [NativePadObservation.code_length]
  omega

def timeBound (input : Input) : Nat := F.component.procedure.execution.budget input +
  NativePadObservation.timeBound O (F.width input) + 1

theorem budget (input : Input) : (link F O).native.execution.budget input = timeBound F O input := rfl

theorem entry (input : Input) :
    (link F O).native.execution.entry input = F.component.procedure.execution.entry input :=
  (link F O).native_entry input

/-- Decision security is determined by the certified preparation distribution.
This does not assert secrecy of variable preparation time. -/
theorem observe (input : Input) :
    ((link F O).native.execution.semantics input).map NativeSerializedObservation.decision =
      (F.component.procedure.execution.semantics input).bind (fun output =>
        O.observe (FiniteBitEncoding.delimit (NativePadEncryption.cipher output))) := by
  rw [(link F O).semantics, PMF.map_bind]
  congr 1
  funext output
  rw [PMF.map_comp]
  change ((NativePadObservation.link O).component.equivalentEntries.procedure.execution.semantics
    (observerInput F O input output)).map NativeSerializedObservation.decision = _
  rw [(NativePadObservation.link O).component.equivalentEntries_observe _ NativeSerializedObservation.decision
    (fun _ _ h => congrArg (fun current => current.getD false) h.2.2.1.1)]
  change ((NativePadObservation.link O).native.execution.semantics (observerInput F O input output).logical).map
    NativeSerializedObservation.decision = _
  rw [observerInput_logical, NativePadObservation.observe]

noncomputable def costed (input : Input) : PMF (Configuration × Nat) :=
  (link F O).component.firstArrival.procedure.execution.costed input

theorem costed_observe (input : Input) :
    (costed F O input).map (fun result => NativeSerializedObservation.decision result.1) =
      (F.component.procedure.execution.semantics input).bind (fun output =>
        O.observe (FiniteBitEncoding.delimit (NativePadEncryption.cipher output))) := by
  have h := (link F O).component.firstArrival.procedure.execution.correct input
  change (costed F O input).map Prod.fst = ((link F O).native.execution.semantics input).map id at h
  rw [PMF.map_id] at h
  rw [← observe F O input, ← h, PMF.map_comp]
  rfl

theorem costed_horizon (input : Input) (horizon : Nat) (hTime : timeBound F O input ≤ horizon) :
    runToBoundary (stepPMF (fixedCode F O)) Configuration.halted horizon
      (F.component.procedure.execution.entry input) = costed F O input := by
  have h := (link F O).component.firstArrival_costed_horizon input horizon hTime
  change runToBoundary _ _ _ ((link F O).native.execution.entry input) = _ at h
  rw [entry] at h
  exact h

theorem costed_bound (input : Input) (result : Configuration × Nat)
    (h : result ∈ (costed F O input).support) : result.2 ≤ timeBound F O input := by
  rw [costed, (link F O).component.firstArrival_costed] at h
  exact runToBoundary_bounded _ _ _ _ result h

theorem time_polynomial (profile : Nat → Input)
    (hPreparation : PolynomiallyBounded (fun n => F.component.procedure.execution.budget (profile n)))
    (hWidth : PolynomiallyBounded (fun n => F.width (profile n))) :
    PolynomiallyBounded (fun n => timeBound F O (profile n)) :=
  (hPreparation.add
    ((((PolynomiallyBounded.const 54).mul hWidth).add (PolynomiallyBounded.const 40)).add
      (O.budget_profile_polynomial (((PolynomiallyBounded.const 2).mul hWidth).add (PolynomiallyBounded.const 1))))).add
    (PolynomiallyBounded.const 1)

/-- Storage includes every represented cell at preparation entry, including
any seed, plaintext, workspace and explicit blank padding. -/
def bitBound (input : Input) : Nat := StructuredCodeEncoding.bound (fixedCode F O)
  (F.component.procedure.execution.entry input).pc (F.component.procedure.execution.entry input).tapeCells (timeBound F O input)

theorem storage_peak (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ timeBound F O input)
    (state : Configuration)
    (h : state ∈ (eval (stepPMF (fixedCode F O)) elapsed (F.component.procedure.execution.entry input)).support) :
    (StructuredCodeEncoding.completeEncoding.encode (fixedCode F O, state)).length ≤ bitBound F O input :=
  StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state h

theorem space_polynomial (profile : Nat → Input)
    (hPreparation : PolynomiallyBounded (fun n => F.component.procedure.execution.budget (profile n)))
    (hWidth : PolynomiallyBounded (fun n => F.width (profile n)))
    (hPc : PolynomiallyBounded (fun n => (F.component.procedure.execution.entry (profile n)).pc))
    (hCells : PolynomiallyBounded (fun n => (F.component.procedure.execution.entry (profile n)).tapeCells)) :
    PolynomiallyBounded (fun n => bitBound F O (profile n)) :=
  StructuredCodeEncoding.bound_polynomial _ hPc hCells (time_polynomial F O profile hPreparation hWidth)

end PhysicalPreparation
end Machine.NativePadPipeline
