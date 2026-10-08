import Foundation.Crypto.Semantics.Machine.OutputAppend
import Foundation.Crypto.Semantics.Machine.TypedCompositionRelation

/-! Three real native components on arbitrary inherited tapes. Two
applications of the same linker append three fixed bits. Input preparation
is the explicit entry contract; no seed loading or string concatenation is
performed for free at a runtime handoff. -/
namespace Foundation.Examples.ThreeNativeComponents
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

noncomputable def firstLink (a b : Bool) :
    TypedNativeComposition.Link (OutputAppend.native a) (OutputAppend.native b) :=
  (OutputAppend.component a).link (OutputAppend.component b)
    (fun _ machine => {machine.resumeAt 2 with halted := true})
    (by
      intro input output h
      change output ∈ ((OutputAppend.native a).execution.semantics (input.1, input.2)).support at h
      rw [OutputAppend.semantics, PMF.mem_support_pure_iff] at h
      subst output
      simp only [OutputAppend.finish, Configuration.resumeAt, Configuration.mk.injEq,
        and_true, true_and]
      exact ⟨rfl, rfl⟩)
    (fun input _ => (input.1 ++ [a], input.2))
    (by
      intro input output h
      change output ∈ ((OutputAppend.native a).execution.semantics (input.1, input.2)).support at h
      rw [OutputAppend.semantics, PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun _ => 3) (fun _ _ _ => Nat.le_refl 3)

theorem first_budget (a b : Bool) (input : List Bool × Tape) :
    (firstLink a b).native.execution.budget input = 7 := rfl

theorem first_semantics (a b : Bool) (input : List Bool × Tape) :
    (firstLink a b).native.execution.semantics input =
      PMF.pure {(OutputAppend.finish (input.1 ++ [a]) input.2 b).resumeAt 8 with halted := true} := by
  rw [TypedNativeComposition.Link.semantics, OutputAppend.semantics]
  simp only [PMF.pure_bind]
  change ((OutputAppend.native b).execution.semantics (input.1 ++ [a], input.2)).map _ = _
  rw [OutputAppend.semantics, PMF.pure_map]
  rfl

noncomputable def link (a b c : Bool) :
    TypedNativeComposition.Link (firstLink a b).native (OutputAppend.native c) :=
  (firstLink a b).append (OutputAppend.component c)
    (fun input _ => (input.1 ++ [a, b], input.2))
    (by
      intro input output h
      rw [first_semantics, PMF.mem_support_pure_iff] at h
      subst output
      change (OutputAppend.initial (input.1 ++ [a, b]) input.2).rebasePc _ = _
      simp [OutputAppend.initial, OutputAppend.finish, Configuration.resumeAt,
        Configuration.rebasePc, List.append_assoc])
    (fun _ => 3) (fun _ _ _ => Nat.le_refl 3)

theorem code (a b c : Bool) : (link a b c).code =
    ((OutputAppend.code a).followedBy (OutputAppend.code b)).followedBy (OutputAppend.code c) := rfl

theorem code_length (a b c : Bool) : (link a b c).code.length = 15 := by
  rw [code]
  simp [Program.followedBy, OutputAppend.code]

theorem budget (a b c : Bool) (input : List Bool × Tape) :
    (link a b c).native.execution.budget input = 11 := rfl

def finish (a b c : Bool) (input : List Bool × Tape) : Configuration :=
  {pc := 14, inputTape := input.2, outputTape := ResponseExport.endTape (input.1 ++ [a, b, c]), halted := true}

theorem semantics (a b c : Bool) (input : List Bool × Tape) :
    (link a b c).native.execution.semantics input = PMF.pure (finish a b c input) := by
  rw [TypedNativeComposition.Link.semantics, first_semantics]
  simp only [PMF.pure_bind]
  change ((OutputAppend.native c).execution.semantics (input.1 ++ [a, b], input.2)).map _ = _
  rw [OutputAppend.semantics, PMF.pure_map]
  simp [OutputAppend.finish, finish, Configuration.resumeAt, List.append_assoc]
  rfl

/-- The proof applies to every inherited packet and saved input tape. -/
theorem run (a b c : Bool) (input : List Bool × Tape) (horizon : Nat) (hTime : 11 ≤ horizon) :
    evalConfigWithin (link a b c).code (OutputAppend.initial input.1 input.2) horizon =
      PMF.pure (finish a b c input) :=
  ((link a b c).run input horizon hTime).trans (semantics a b c input)

theorem operational (a b c : Bool) :
    TimedExecution.Procedure.Operational (link a b c).native.execution := (link a b c).operational

noncomputable def spaceProfile (a b c : Bool) : Nat → Nat :=
  (link a b c).storageProfile (fun _ => 0) (fun size => size + 1) (fun _ => 7) (fun _ => 3)

theorem space_polynomial (a b c : Bool) : PolynomiallyBounded (spaceProfile a b c) :=
  (link a b c).storageProfile_polynomial (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))
    (PolynomiallyBounded.const 7) (PolynomiallyBounded.const 3)

theorem storage_peak (a b c : Bool) (input : List Bool × Tape) (elapsed : Nat)
    (hElapsed : elapsed ≤ 11) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF (link a b c).code) elapsed
      (OutputAppend.initial input.1 input.2)).support) :
    (NativeEncodedResources.completeEncoding.encode ((link a b c).code, target)).length ≤
      spaceProfile a b c (input.1.length + input.2.cells) := by
  apply (link a b c).storage_profile (fun _ => 0) (fun size => size + 1)
    (fun _ => 7) (fun _ => 3) (fun size value => value.1.length + value.2.cells = size)
    _ _ _ _ (input.1.length + input.2.cells) input rfl elapsed hElapsed target hTarget
  · intro size value _
    exact Nat.le_refl 0
  · intro size value hSize
    change value.2.cells + (ResponseExport.endTape value.1).cells ≤ size + 1
    have hc : (ResponseExport.endTape value.1).cells = value.1.length + 1 := by
      simp [ResponseExport.endTape, Tape.cells]
    rw [hc]
    omega
  · intro size value _
    exact Nat.le_refl 7
  · intro size value _
    exact Nat.le_refl 3

end Foundation.Examples.ThreeNativeComponents
