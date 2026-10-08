import Foundation.Crypto.Semantics.Machine.NativePacketHandoff
import Foundation.Crypto.Semantics.Machine.NativePolynomialObserver

/-! One fixed native program writes a delimited packet, rewinds it, erases
the original source and invokes an arbitrary polynomial-time observer on
the inherited tapes. Entry data, a preceding blank and output capacity are
explicit; a producer must separately establish this physical precondition.
The whole execution, including all preparation, has polynomial resources. -/
namespace Machine.NativeSerializedObservation
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
variable (O : PolynomialObserver)

def handoffInput (data : List Bool) : NativePacketHandoff.Input := {data := data}

noncomputable def handoff : NativeComponent (List Bool) Configuration :=
  NativePacketHandoff.link.component.reindex handoffInput

noncomputable def observerInput (data : List Bool) : O.native.swapTapes.EquivalentInput :=
  ⟨FiniteBitEncoding.delimit data, (NativePacketHandoff.finish (handoffInput data)).resumeAt 0,
    NativePacketHandoff.clean_entry (handoffInput data) rfl rfl rfl⟩

noncomputable def link : TypedNativeComposition.Link handoff.procedure
    O.native.swapTapes.equivalentEntries.procedure :=
  handoff.link O.native.swapTapes.equivalentEntries
    (fun _ machine => {machine.resumeAt 29 with halted := true})
    (by
      intro data output h
      change output ∈ (NativePacketHandoff.link.native.execution.semantics (handoffInput data)).support at h
      rw [NativePacketHandoff.semantics, PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun data _ => observerInput O data)
    (by
      intro data output h
      change output ∈ (NativePacketHandoff.link.native.execution.semantics (handoffInput data)).support at h
      rw [NativePacketHandoff.semantics, PMF.mem_support_pure_iff] at h
      subst output
      change ((NativePacketHandoff.finish (handoffInput data)).resumeAt 0).rebasePc 31 =
        (NativePacketHandoff.finish (handoffInput data)).resumeAt 31
      simp [Configuration.rebasePc, Configuration.resumeAt])
    (fun data => O.budget (FiniteBitEncoding.delimit data).length + 2)
    (fun _ _ _ => Nat.le_refl _)

def fixedCode : Program :=
  NativePacketHandoff.fixedCode.followedBy (NativeHaltingProgram.code O.code).swapTapes

theorem fixedCode_eq : fixedCode O = (link O).code := rfl

theorem code_length : (link O).code.length = O.code.length + 37 := by
  rw [(link O).code_length]
  change NativePacketHandoff.link.code.length + (NativeHaltingProgram.code O.code).swapTapes.length + 3 = _
  rw [NativePacketHandoff.code_length, Program.swapTapes_length, NativeHaltingProgram.code_length]
  omega

def initial (data : List Bool) : Configuration := NativePacketHandoff.initial (handoffInput data)

theorem initial_eq (data : List Bool) : initial data =
    { inputTape := {OneTimePad.delimitedTape data [] with left := [none]}
      outputTape := {right := List.replicate (2 * data.length + 1) none} } := by
  unfold initial NativePacketHandoff.initial NativePacketPreparation.initial
  rw [NativeDelimitedWriter.initial_eq]
  simp [NativePacketPreparation.writerInput, NativePacketHandoff.packetInput, handoffInput]

def timeBound (size : Nat) : Nat := 16 * size + 18 + O.budget (2 * size + 1)

theorem budget (data : List Bool) : (link O).native.execution.budget data = timeBound O data.length := by
  rw [(link O).budget]
  change NativePacketHandoff.link.native.execution.budget (handoffInput data) +
    (O.budget (FiniteBitEncoding.delimit data).length + 2) + 1 = _
  rw [NativePacketHandoff.budget, FiniteBitEncoding.delimit_length]
  change 16 * data.length + 15 + (O.budget (2 * data.length + 1) + 2) + 1 =
    16 * data.length + 18 + O.budget (2 * data.length + 1)
  omega

theorem time_polynomial : PolynomiallyBounded (timeBound O) :=
  ((((PolynomiallyBounded.const 16).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 18)).add
    (O.budget_profile_polynomial
      (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 1))))

theorem run (data : List Bool) (horizon : Nat) (hTime : timeBound O data.length ≤ horizon) :
    evalConfigWithin (link O).code (initial data) horizon = (link O).native.execution.semantics data := by
  apply (link O).run
  change (link O).native.execution.budget data ≤ horizon
  rw [budget]
  exact hTime

/-- The final input head is the observer's relabeled output head. -/
def decision (state : Configuration) : Bool := state.inputTape.current.getD false

theorem observe (data : List Bool) :
    ((link O).native.execution.semantics data).map decision = O.observe (FiniteBitEncoding.delimit data) := by
  rw [(link O).semantics]
  change ((NativePacketHandoff.link.native.execution.semantics (handoffInput data)).bind _).map decision = _
  rw [NativePacketHandoff.semantics, PMF.pure_bind, PMF.map_comp]
  change (O.native.swapTapes.equivalentEntries.procedure.execution.semantics (observerInput O data)).map decision = _
  rw [O.native.swapTapes.equivalentEntries_observe (observerInput O data) decision
    (fun _ _ h => congrArg (fun current => current.getD false) h.2.2.1.1)]
  exact O.opposite_native_observe (FiniteBitEncoding.delimit data)

theorem run_observe (data : List Bool) (horizon : Nat) (hTime : timeBound O data.length ≤ horizon) :
    (evalConfigWithin (link O).code (initial data) horizon).map decision =
      O.observe (FiniteBitEncoding.delimit data) := by
  rw [run O data horizon hTime, observe]

noncomputable def costed (data : List Bool) : PMF (Configuration × Nat) :=
  (link O).component.firstArrival.procedure.execution.costed data

theorem costed_observe (data : List Bool) :
    (costed O data).map (fun result => decision result.1) = O.observe (FiniteBitEncoding.delimit data) := by
  have h := (link O).component.firstArrival.procedure.execution.correct data
  change (costed O data).map Prod.fst = ((link O).native.execution.semantics data).map id at h
  rw [PMF.map_id] at h
  rw [← observe O data, ← h, PMF.map_comp]
  rfl

/-- Distributional experiments reuse the same physical program for every
data value. The observation law holds pointwise before sampling inputs. -/
theorem costed_observe_distribution (inputs : PMF (List Bool)) :
    inputs.bind (fun data => (costed O data).map (fun result => decision result.1)) =
      (inputs.map FiniteBitEncoding.delimit).bind O.observe := by
  simp only [costed_observe, PMF.bind_map]
  rfl

theorem costed_halted (data : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (costed O data).support) : result.1.halted = true :=
  (link O).component.firstArrival_halted data result hResult

theorem costed_bound (data : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (costed O data).support) : result.2 ≤ timeBound O data.length := by
  change result ∈ ((link O).component.firstArrival.procedure.execution.costed data).support at hResult
  rw [(link O).component.firstArrival_costed] at hResult
  have h := runToBoundary_bounded _ _ _ _ result hResult
  change result.2 ≤ (link O).native.execution.budget data at h
  rwa [budget] at h

theorem initial_cells (data : List Bool) : (initial data).tapeCells = 3 * data.length + 4 := by
  simpa [initial, handoffInput] using NativePacketHandoff.initial_cells (handoffInput data)

def bitBound (size : Nat) : Nat :=
  StructuredCodeEncoding.bound (fixedCode O) 0 (3 * size + 4) (timeBound O size)

theorem space_polynomial : PolynomiallyBounded (bitBound O) :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 4))
    (time_polynomial O)

theorem storage_peak (data : List Bool) (elapsed : Nat) (hElapsed : elapsed ≤ timeBound O data.length)
    (state : Configuration)
    (hState : state ∈ (eval (stepPMF (link O).code) elapsed (initial data)).support) :
    (StructuredCodeEncoding.completeEncoding.encode ((link O).code, state)).length ≤ bitBound O data.length :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state hState).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (by rw [initial_cells]) (Nat.le_refl _))

/-- The actual first-halt state's storage is bounded using its own elapsed
time, retaining correlations between the observer's result and runtime. -/
theorem storage_costed (data : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (costed O data).support) :
    (StructuredCodeEncoding.completeEncoding.encode ((link O).code, result.1)).length ≤
      StructuredCodeEncoding.bound (fixedCode O) 0 (3 * data.length + 4) result.2 := by
  have h := (link O).component.firstArrival_operational data result hResult
  change result.1 ∈ (eval (stepPMF (link O).code) result.2
    ((link O).native.execution.entry data)).support at h
  rw [(link O).native_entry] at h
  change result.1 ∈ (eval (stepPMF (link O).code) result.2 (initial data)).support at h
  exact (StructuredCodeEncoding.peak _ _ result.2 (Nat.le_refl _) _ result.1 h).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (by rw [initial_cells]) (Nat.le_refl _))

end Machine.NativeSerializedObservation
