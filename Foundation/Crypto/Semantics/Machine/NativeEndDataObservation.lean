import Foundation.Crypto.Semantics.Machine.NativeSerializedObservation
import Foundation.Crypto.Semantics.Machine.BlankPadding

/-! Observe data left behind at an input tape's end. The scratch tape and
the source suffix may contain any finite amounts of blank padding. Actual
rewind and serialization run on these representations. Their full sizes
are charged; no canonical tape is loaded at the boundary. -/
namespace Machine.NativeEndDataObservation
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
variable (O : PolynomialObserver)

structure Input where
  data : List Bool
  sourceBlanks : Nat := 0
  scratchLeft : Nat := 0
  scratchRight : Nat := 0

def scratch (input : Input) : Tape :=
  {left := List.replicate input.scratchLeft none, right := List.replicate input.scratchRight none}

theorem scratch_blank (input : Input) : (scratch input).Equivalent ({} : Tape) :=
  (Tape.blank_padding_equivalent _ _).trans
    (Tape.append_left_blank_equivalent {} (List.replicate input.scratchLeft none) (by simp))

def rewindInput (input : Input) : NativeBitstringRewind.Input :=
  {bits := input.data, right := List.replicate input.sourceBlanks none, other := scratch input}

def initial (input : Input) : Configuration := NativeBitstringRewind.initial (rewindInput input)

theorem rewind_entry (input : Input) :
    ((NativeBitstringRewind.finish (rewindInput input)).resumeAt 0).Equivalent
      (NativeSerializedObservation.initial input.data) := by
  rw [NativeSerializedObservation.initial_eq]
  refine ⟨rfl, rfl, ?_, (scratch_blank input).trans (Tape.blank_padding_equivalent [] _).symm⟩
  have h := (Tape.append_right_blank_equivalent
    ({right := input.data.map some ++ [none]} : Tape)
    (List.replicate input.sourceBlanks none) (by simp)).moveRight
  change (({right := input.data.map some ++ none :: List.replicate input.sourceBlanks none} : Tape).moveRight).Equivalent _
  have hLayout :
      (({right := input.data.map some ++ [none]} : Tape).moveRight) =
        {OneTimePad.delimitedTape input.data [] with left := [none]} := by
    cases input.data <;> simp [Tape.moveRight, OneTimePad.delimitedTape]
  simpa only [List.append_assoc, List.cons_append, List.nil_append, hLayout] using h

noncomputable def rewind : NativeComponent Input Configuration :=
  NativeBitstringRewind.component.reindex rewindInput

noncomputable def serializedInput (input : Input) :
    (NativeSerializedObservation.link O).component.EquivalentInput :=
  ⟨input.data, (NativeBitstringRewind.finish (rewindInput input)).resumeAt 0, rewind_entry input⟩

noncomputable def link : TypedNativeComposition.Link rewind.procedure
    (NativeSerializedObservation.link O).component.equivalentEntries.procedure :=
  rewind.link (NativeSerializedObservation.link O).component.equivalentEntries
    (fun _ machine => {machine.resumeAt 3 with halted := true})
    (by
      intro input output h
      change output ∈ (PMF.pure (NativeBitstringRewind.finish (rewindInput input))).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun input _ => serializedInput O input)
    (by
      intro input output h
      change output ∈ (PMF.pure (NativeBitstringRewind.finish (rewindInput input))).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      change ((NativeBitstringRewind.finish (rewindInput input)).resumeAt 0).rebasePc 5 =
        (NativeBitstringRewind.finish (rewindInput input)).resumeAt 5
      simp [Configuration.rebasePc, Configuration.resumeAt])
    (fun input => NativeSerializedObservation.timeBound O input.data.length)
    (by intro input _ _; change (NativeSerializedObservation.link O).native.execution.budget input.data ≤ _;
        rw [NativeSerializedObservation.budget])

def fixedCode : Program := rewindBitstring.followedBy (NativeSerializedObservation.fixedCode O)

theorem fixedCode_eq : fixedCode O = (link O).code := rfl

theorem code_length : (link O).code.length = O.code.length + 44 := by
  rw [(link O).code_length]
  change 4 + (NativeSerializedObservation.link O).code.length + 3 = _
  rw [NativeSerializedObservation.code_length]
  omega

def timeBound (size : Nat) : Nat := 18 * size + 23 + O.budget (2 * size + 1)

theorem budget (input : Input) : (link O).native.execution.budget input = timeBound O input.data.length := by
  rw [(link O).budget]
  change 2 * input.data.length + 4 + NativeSerializedObservation.timeBound O input.data.length + 1 = _
  unfold timeBound NativeSerializedObservation.timeBound
  omega

theorem time_polynomial : PolynomiallyBounded (timeBound O) :=
  ((((PolynomiallyBounded.const 18).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 23)).add
    (O.budget_profile_polynomial
      (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))))

theorem timeBound_mono {first second : Nat} (h : first ≤ second) : timeBound O first ≤ timeBound O second := by
  have hb := O.budget_mono (show 2 * first + 1 ≤ 2 * second + 1 by omega)
  unfold timeBound
  omega

theorem observe (input : Input) :
    ((link O).native.execution.semantics input).map NativeSerializedObservation.decision =
      O.observe (FiniteBitEncoding.delimit input.data) := by
  rw [(link O).semantics]
  change ((PMF.pure (NativeBitstringRewind.finish (rewindInput input))).bind _).map _ = _
  rw [PMF.pure_bind, PMF.map_comp]
  change ((NativeSerializedObservation.link O).component.equivalentEntries.procedure.execution.semantics
    (serializedInput O input)).map NativeSerializedObservation.decision = _
  rw [(NativeSerializedObservation.link O).component.equivalentEntries_observe
    (serializedInput O input) NativeSerializedObservation.decision
    (fun _ _ h => congrArg (fun current => current.getD false) h.2.2.1.1)]
  change ((NativeSerializedObservation.link O).native.execution.semantics input.data).map
    NativeSerializedObservation.decision = _
  exact NativeSerializedObservation.observe O input.data

theorem run (input : Input) (horizon : Nat) (hTime : timeBound O input.data.length ≤ horizon) :
    evalConfigWithin (link O).code (initial input) horizon = (link O).native.execution.semantics input := by
  apply (link O).run
  change (link O).native.execution.budget input ≤ horizon
  rw [budget]
  exact hTime

theorem run_observe (input : Input) (horizon : Nat) (hTime : timeBound O input.data.length ≤ horizon) :
    (evalConfigWithin (link O).code (initial input) horizon).map NativeSerializedObservation.decision =
      O.observe (FiniteBitEncoding.delimit input.data) := by
  rw [run O input horizon hTime, observe]

def inputSize (input : Input) : Nat :=
  input.data.length + input.sourceBlanks + input.scratchLeft + input.scratchRight

theorem initial_cells (input : Input) : (initial input).tapeCells = inputSize input + 2 := by
  simp [initial, NativeBitstringRewind.initial, rewindInput, scratch, Configuration.tapeCells, Tape.cells, inputSize]
  omega

def bitBound (size : Nat) : Nat :=
  StructuredCodeEncoding.bound (fixedCode O) 0 (size + 2) (timeBound O size)

theorem space_polynomial : PolynomiallyBounded (bitBound O) :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2)) (time_polynomial O)

theorem storage_peak (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ timeBound O input.data.length)
    (state : Configuration)
    (hState : state ∈ (eval (stepPMF (link O).code) elapsed (initial input)).support) :
    (StructuredCodeEncoding.completeEncoding.encode ((link O).code, state)).length ≤ bitBound O (inputSize input) :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state hState).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (by rw [initial_cells])
      (timeBound_mono O (by unfold inputSize; omega)))

end Machine.NativeEndDataObservation
