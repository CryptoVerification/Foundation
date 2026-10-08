import Foundation.Crypto.Semantics.Oracle.CountedCaller
import Foundation.Crypto.Semantics.Oracle.SelectedRejection
import Foundation.Constructions.Symmetric.OneTimePad

/-! One real counted rejection round, with request selection and marker
consumption both charged. Its output retains the chosen bit in the public
trace; the complete physical key and both caller tapes survive the round. -/
namespace CryptoOracle.Interactive.CountedRejection
open Foundation.Probability Foundation.Symmetric TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {width : Nat} (native : Machine.Program) (oracle : BitOracle State)
    (key : Bits width) (state : State) (trace : List (List Bool × List Bool))
    (past : List (Option Bool)) (marker : Bool) (markers payload : List Bool) (hMismatch : width ≠ 1)

def call (bit : Bool) : SelectedRejection.Call State CountedCaller.code width where
  machine := CountedCaller.selected past (marker :: markers) payload bit
  state := state
  trace := trace
  request := [bit]
  tail := []
  active := rfl
  instruction := rfl
  tape := rfl
  mismatch := hMismatch

noncomputable def choose : Procedure (OneUseSource.step native CountedCaller.code oracle) Unit Bool :=
  Procedure.ofFixed _
    (fun _ => .source false (Machine.PairPreparation.operand [] key.toList [])
      ⟨state, .running (CountedCaller.waiting past (marker :: markers) payload), trace⟩)
    (fun _ bit => .source false (Machine.PairPreparation.operand [] key.toList [])
      ⟨state, .running (CountedCaller.selected past (marker :: markers) payload bit), trace⟩)
    (fun _ => sampleBit) (fun _ => 3)
    (fun _ => CountedCaller.choose native oracle _ state trace past marker markers payload)

noncomputable def reject (bit : Bool) :=
  SelectedRejection.reject native oracle key.toList [] (by simp) (call state trace past marker markers payload hMismatch bit)

noncomputable def chosenRejection :=
  (choose native oracle key state trace past marker markers payload).seq
    (Procedure.dispatch (reject native oracle key state trace past marker markers payload hMismatch))
    (fun _ _ _ => rfl) (fun _ => 12 * min width 1 + 31)
    (fun _ bit _ => by
      unfold Procedure.dispatch reject SelectedRejection.reject
      rw [OneUseSource.rejectedInvocation_budget]
      simp [SelectedRejection.input, call, Machine.PreparationCheck.consumed]
      omega)

def returned (bit : Bool) : Configuration State :=
  SelectedRejection.returned (call state trace past marker markers payload hMismatch bit)

def final (bit : Bool) : Configuration State :=
  ⟨state, .running (CountedCaller.advanced past marker markers payload), ([bit], [false]) :: trace⟩

noncomputable def consume (bit : Bool) : Procedure (OneUseSource.step native CountedCaller.code oracle) Unit Unit :=
  Procedure.ofFixed _
    (fun _ => .source false (Machine.PairPreparation.operand [] key.toList [])
      (returned state trace past marker markers payload hMismatch bit))
    (fun _ _ => .source false (Machine.PairPreparation.operand [] key.toList [])
      (final state trace past marker markers payload bit))
    (fun _ => PMF.pure ()) (fun _ => 2)
    (fun _ => by
      simpa only [returned, SelectedRejection.returned, call, NativeCallback.resumed,
        CountedCaller.selected, CountedCaller.waiting, CountedCaller.advanced, Machine.Configuration.advance,
        final, PMF.pure_map] using
        CountedCaller.advance native oracle (Machine.PairPreparation.operand [] key.toList [])
          state (([bit], [false]) :: trace) past marker markers payload)

theorem handoff (start : Unit) (output : Bool × SelectedRejection.Output)
    (h : output ∈ ((chosenRejection native oracle key state trace past marker markers payload hMismatch).semantics start).support) :
    (consume native oracle key state trace past marker markers payload hMismatch output.1).entry () =
      (chosenRejection native oracle key state trace past marker markers payload hMismatch).exit start output := by
  change output ∈ (sampleBit.bind (fun bit =>
    ((reject native oracle key state trace past marker markers payload hMismatch bit).semantics ()).map
      (fun result => (bit, result)))).support at h
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨bit, _, hOutput⟩ := h
  rw [PMF.mem_support_map_iff] at hOutput
  obtain ⟨result, hResult, he⟩ := hOutput
  subst output
  exact (SelectedRejection.reject_exit native oracle key.toList [] (by simp)
    (call state trace past marker markers payload hMismatch bit) result hResult).symm

noncomputable def round :=
  (chosenRejection native oracle key state trace past marker markers payload hMismatch).seq
    ((Procedure.dispatch (consume native oracle key state trace past marker markers payload hMismatch)).reindex Prod.fst)
    (handoff native oracle key state trace past marker markers payload hMismatch)
    (fun _ => 2) (fun _ _ _ => Nat.le_refl _)

theorem budget : (round native oracle key state trace past marker markers payload hMismatch).budget () =
    12 * min width 1 + 36 := by
  change 3 + (12 * min width 1 + 31) + 2 = _
  omega

theorem exit (start : Unit) (output : (Bool × SelectedRejection.Output) × Unit) :
    (round native oracle key state trace past marker markers payload hMismatch).exit start output =
      .source false (Machine.PairPreparation.operand [] key.toList [])
        (final state trace past marker markers payload output.1.1) := rfl

/-- Logical projection keeps the chosen bit while recovering the exact
physical return state; it does not reset the caller or insert a response. -/
noncomputable def observed :=
  (round native oracle key state trace past marker markers payload hMismatch).observe
    (fun result => result.1.1)
    (fun _ bit => .source false (Machine.PairPreparation.operand [] key.toList [])
      (final state trace past marker markers payload bit)) (fun _ _ _ => rfl)

theorem observed_semantics :
    (observed native oracle key state trace past marker markers payload hMismatch).semantics () = sampleBit := by
  simp [observed, round, chosenRejection, choose, consume, Procedure.observe, Procedure.seq,
    Procedure.dispatch, Procedure.reindex, Procedure.ofFixed, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def, PMF.map_const, PMF.pure_map, PMF.pure_bind, PMF.map_id]

noncomputable def publicCost :=
  sampleBit.bind (fun bit =>
    (SelectedRejection.kernel [] (call state trace past marker markers payload hMismatch bit)).map
      (fun result => (bit, 3 + result.2 + 2)))

theorem observed_costed :
    (observed native oracle key state trace past marker markers payload hMismatch).costed () =
      publicCost state trace past marker markers payload hMismatch := by
  simp only [observed, round, chosenRejection, choose, consume, Procedure.observe, Procedure.seq,
    Procedure.dispatch, Procedure.reindex, Procedure.ofFixed, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def, PMF.pure_map, PMF.pure_bind, PMF.bind_bind, publicCost]
  congr 1
  funext bit
  change ((reject native oracle key state trace past marker markers payload hMismatch bit).costed ()).map
    (fun result => (bit, 3 + (result.2 + 2))) = _
  have h := congrArg (fun distribution => distribution.map (fun result => (bit, 3 + result.2 + 2)))
    (SelectedRejection.reject_public_cost native oracle key.toList [] (by simp)
      (call state trace past marker markers payload hMismatch bit))
  simpa only [reject, PMF.map_comp, Function.comp_def, Nat.add_assoc] using h

/-- The copied input is not read by rejection; the chosen request and its
actual cost law are the same for every payload. -/
theorem publicCost_payload (otherPayload : List Bool) :
    publicCost state trace past marker markers payload hMismatch =
      publicCost state trace past marker markers otherPayload hMismatch := by
  simp only [publicCost, SelectedRejection.kernel, PMF.map_comp, Function.comp_def]
  rfl

end CryptoOracle.Interactive.CountedRejection
