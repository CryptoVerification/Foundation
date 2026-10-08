import Foundation.Crypto.Semantics.Machine.ProcedureModel
import Foundation.Crypto.Semantics.Machine.OneTimePad

/-! Arbitrary-width one-time-pad instantiations of the common native model.
Fresh encryption retains the generated key in its logical result because
the complete physical exit still contains that key; observers see only the
ciphertext. -/
namespace Foundation.Symmetric.OneTimePad.ProcedureModels
open Foundation.Probability Machine
set_option backward.isDefEq.respectTransparency false

noncomputable def keygen (width : Nat) : ProcedureModel Unit (Bits width) where
  procedure := Machine.Procedure.ofFixed Machine.OneTimePad.keygen
    (fun _ => Machine.OneTimePad.state [] [] (List.replicate width true))
    (fun _ key => Machine.OneTimePad.finish 5 (List.replicate width true) key.toList)
    (fun _ => uniform (Bits width)) (fun _ => 5 * width + 2)
    (fun _ => by simpa using Machine.OneTimePad.keygen_typed_run width [] [])
  ideal := fun _ => uniform (Bits width)
  implements := fun _ => rfl
  encode := fun _ key => key.toList
  halt := fun _ _ _ => rfl
  output := fun _ key _ => Machine.OneTimePad.finish_output 5 _ key.toList

noncomputable def encryption (width : Nat) : ProcedureModel (Bits width × Bits width) Unit where
  procedure := Machine.Procedure.ofFixed Machine.OneTimePad.xorCode
    (fun input => Machine.OneTimePad.state [] []
      (Machine.OneTimePad.pairInput input.1.toList input.2.toList))
    (fun input _ => Machine.OneTimePad.finish 16
      (Machine.OneTimePad.pairInput input.1.toList input.2.toList) (encrypt input.1 input.2).toList)
    (fun _ => PMF.pure ()) (fun _ => 8 * width + 2)
    (fun input => by
      have h := Machine.OneTimePad.xor_run [] [] input.1.toList input.2.toList (by simp)
      simpa [PMF.pure_map, encrypt, Machine.OneTimePad.toList_xor] using h)
  ideal := fun _ => PMF.pure ()
  implements := fun _ => rfl
  encode := fun input _ => (encrypt input.1 input.2).toList
  halt := fun _ _ _ => rfl
  output := fun input _ _ => Machine.OneTimePad.finish_output 16 _ _

noncomputable def freshEncryption (width : Nat) : ProcedureModel (Bits width) (Bits width) where
  procedure := Machine.Procedure.ofFixed Machine.OneTimePad.freshCode
    (fun message => Machine.OneTimePad.state [] [] message.toList)
    (fun message key => Machine.OneTimePad.finish 16 key.toList (encrypt key message).toList)
    (fun _ => uniform (Bits width)) (fun _ => 8 * width + 2)
    (fun message => by simpa using Machine.OneTimePad.fresh_typed_run message [] [])
  ideal := fun _ => uniform (Bits width)
  implements := fun _ => rfl
  encode := fun message key => (encrypt key message).toList
  halt := fun _ _ _ => rfl
  output := fun message key _ => Machine.OneTimePad.finish_output 16 _ _

/-- Width changes the logical input type and its tapes, never the finite code. -/
theorem codes (width : Nat) :
    (keygen width).procedure.code = Machine.OneTimePad.keygen ∧
    (encryption width).procedure.code = Machine.OneTimePad.xorCode ∧
    (freshEncryption width).procedure.code = Machine.OneTimePad.freshCode := ⟨rfl, rfl, rfl⟩

theorem budgets (width : Nat) (key message : Bits width) :
    (keygen width).procedure.execution.budget () = 5 * width + 2 ∧
    (encryption width).procedure.execution.budget (key, message) = 8 * width + 2 ∧
    (freshEncryption width).procedure.execution.budget message = 8 * width + 2 := ⟨rfl, rfl, rfl⟩

/-- Any polynomial public width yields polynomial certified time profiles. -/
theorem time_polynomial {width : Nat → Nat} (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => 5 * width n + 2) ∧
    PolynomiallyBounded (fun n => 8 * width n + 2) :=
  ⟨((PolynomiallyBounded.const 5).mul hWidth).add (PolynomiallyBounded.const 2),
   ((PolynomiallyBounded.const 8).mul hWidth).add (PolynomiallyBounded.const 2)⟩

theorem encryption_correct {width : Nat} (key message : Bits width) (horizon : Nat)
    (hTime : 8 * width + 2 ≤ horizon) :
    (encryption width).execution (key, message) horizon = PMF.pure (some (encrypt key message).toList) := by
  rw [ProcedureModel.execution_eq _ _ horizon hTime]
  exact PMF.pure_map _ _

/-- Perfect secrecy is transferred by the common model theorem, with no
restriction to a one-bit message or to an exact inspection time. -/
theorem fresh_secrecy {width : Nat} (left right : Bits width) (leftTime rightTime : Nat)
    (hLeft : 8 * width + 2 ≤ leftTime) (hRight : 8 * width + 2 ≤ rightTime)
    (observer : Option (List Bool) → PMF Bool) :
    ((freshEncryption width).execution left leftTime).bind observer =
      ((freshEncryption width).execution right rightTime).bind observer := by
  apply ProcedureModel.indistinguishable _ left right leftTime rightTime hLeft hRight _ observer
  change (uniform (Bits width)).map (fun key => (encrypt key left).toList) =
    (uniform (Bits width)).map (fun key => (encrypt key right).toList)
  have hl := congrArg (fun p : PMF (Bits width) => p.map Bits.toList) (ciphertext_uniform left)
  have hr := congrArg (fun p : PMF (Bits width) => p.map Bits.toList) (ciphertext_uniform right)
  simp only [ciphertext, PMF.map_comp, Function.comp_def] at hl hr
  exact hl.trans hr.symm

end Foundation.Symmetric.OneTimePad.ProcedureModels
