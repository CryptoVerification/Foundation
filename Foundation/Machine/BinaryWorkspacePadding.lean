import Foundation.Machine.BinaryPowerProgramSemantics

namespace Machine.BinaryWorkspacePadding

/-- A mathematical description of the extra high workspace column. The
external-to-workspace adapter must still write these three bits natively. -/
def pad (columns : List BinaryModularAddition.Column) :
    List BinaryModularAddition.Column := columns ++ [((false, false), false)]

theorem value_append_zero (bits : List Bool) :
    Binary.value (bits ++ [false]) = Binary.value bits := by
  simp [Binary.value_append, Binary.value]

theorem encode_succ (width n : Nat) (h : n < 2 ^ width) :
    Binary.encode (width + 1) n = Binary.encode width n ++ [false] := by
  have hv : Binary.value (Binary.encode width n ++ [false]) = n := by
    rw [value_append_zero, Binary.value_encode h]
  have he := Binary.encode_value (Binary.encode width n ++ [false])
  simpa only [List.length_append, Binary.encode_length, List.length_singleton,
    hv] using he

@[simp] theorem pad_length (columns : List BinaryModularAddition.Column) :
    (pad columns).length = columns.length + 1 := by simp [pad]

@[simp] theorem pad_operand (columns : List BinaryModularAddition.Column) :
    (pad columns).map (fun c => c.1.1) = columns.map (fun c => c.1.1) ++ [false] := by
  simp [pad]

@[simp] theorem pad_multiplier (columns : List BinaryModularAddition.Column) :
    (pad columns).map (fun c => c.1.2) = columns.map (fun c => c.1.2) ++ [false] := by
  simp [pad]

@[simp] theorem pad_modulus (columns : List BinaryModularAddition.Column) :
    (pad columns).map Prod.snd = columns.map Prod.snd ++ [false] := by
  simp [pad]

@[simp] theorem interleave_pad (columns : List BinaryModularAddition.Column) :
    BinaryModularAddition.interleave (pad columns) =
      BinaryModularAddition.interleave columns ++ [false, false, false] := by
  induction columns with
  | nil => rfl
  | cons column rest ih =>
      have h := congrArg (fun bits => column.1.1 :: column.1.2 :: column.2 :: bits) ih
      simpa only [pad, BinaryModularAddition.interleave, List.cons_append,
        List.append_assoc] using h

theorem room (columns : List BinaryModularAddition.Column)
    (h : Binary.value (columns.map Prod.snd) < 2 ^ columns.length) :
    2 * Binary.value ((pad columns).map Prod.snd) ≤ 2 ^ (pad columns).length := by
  rw [pad_modulus, value_append_zero, pad_length, pow_succ]
  omega

/-- Numerical result for an already padded native multiplication request.
The adapter that writes the extra column remains a separate code obligation. -/
theorem eval_product_padded (columns : List BinaryModularAddition.Column)
    (hOperand : Binary.value (columns.map fun c => c.1.1) < Binary.value (columns.map Prod.snd))
    (hModWidth : Binary.value (columns.map Prod.snd) < 2 ^ columns.length) :
    evalWithin BinaryProductProgram.program (BinaryModularAddition.interleave (pad columns))
      (BinaryProductProgram.budget (BinaryModularAddition.interleave (pad columns)).length) =
      PMF.pure (some (Binary.encode columns.length
        (Binary.value (columns.map fun c => c.1.1) * Binary.value (columns.map fun c => c.1.2) %
          Binary.value (columns.map Prod.snd)) ++ [false])) := by
  have hOperandPad : Binary.value ((pad columns).map fun c => c.1.1) <
      Binary.value ((pad columns).map Prod.snd) := by
    simpa only [pad_operand, pad_modulus, value_append_zero] using hOperand
  have hRoom := room columns hModWidth
  have hResult : Binary.value (columns.map fun c => c.1.1) *
      Binary.value (columns.map fun c => c.1.2) % Binary.value (columns.map Prod.snd) <
      2 ^ columns.length :=
    (Nat.mod_lt _ (by omega)).trans hModWidth
  have h := BinaryProductSemantics.eval_product_encoded (pad columns) hOperandPad hRoom
  simpa only [pad_length, pad_operand, pad_multiplier, pad_modulus, value_append_zero,
    encode_succ _ _ hResult] using h

/-- The same padded workspace supports the full native power code. -/
theorem eval_power_padded (columns : List BinaryModularAddition.Column)
    (_hNonempty : columns ≠ [])
    (hOne : 1 < Binary.value (columns.map Prod.snd))
    (hOperand : Binary.value (columns.map fun c => c.1.1) < Binary.value (columns.map Prod.snd))
    (hModWidth : Binary.value (columns.map Prod.snd) < 2 ^ columns.length) :
    evalWithin BinaryPowerProgram.program (BinaryModularAddition.interleave (pad columns))
      (BinaryPowerProgram.budget (BinaryModularAddition.interleave (pad columns)).length) =
      PMF.pure (some (Binary.encode columns.length
        (Binary.value (columns.map fun c => c.1.1) ^ Binary.value (columns.map fun c => c.1.2) %
          Binary.value (columns.map Prod.snd)) ++ [false])) := by
  have hOperandPad : Binary.value ((pad columns).map fun c => c.1.1) <
      Binary.value ((pad columns).map Prod.snd) := by
    simpa only [pad_operand, pad_modulus, value_append_zero] using hOperand
  have hOnePad : 1 < Binary.value ((pad columns).map Prod.snd) := by
    simpa only [pad_modulus, value_append_zero] using hOne
  have hRoom := room columns hModWidth
  have hResult : Binary.value (columns.map fun c => c.1.1) ^
      Binary.value (columns.map fun c => c.1.2) % Binary.value (columns.map Prod.snd) <
      2 ^ columns.length :=
    (Nat.mod_lt _ (by omega)).trans hModWidth
  have h := BinaryPowerProgramSemantics.eval_power_encoded (pad columns)
    (by simp [pad]) hOnePad hOperandPad hRoom
  simpa only [pad_length, pad_operand, pad_multiplier, pad_modulus, value_append_zero,
    encode_succ _ _ hResult] using h

end Machine.BinaryWorkspacePadding
