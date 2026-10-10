import Foundation.Constructions.Hash.NativePublicWorld

/-! Faithfulness of the actual two-window request packets. The proofs use
fixed payload widths; arbitrary variable-width payloads are not injective. -/
namespace Foundation.Hash.Native
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

theorem typed_runtime_input_injective {κ : Nat} :
    Function.Injective (fun message : List (Bits κ) => runtimeInputBits (message.map Bits.toList)) := by
  have split (payload : Bits κ) (rest : List (Bits κ)) :
      runtimeInputBits ((payload :: rest).map Bits.toList) =
        false :: (payload.toList ++ runtimeInputBits (rest.map Bits.toList)) := by
    simp [runtimeInputBits, runtimePayloadBits, List.append_assoc]
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right <;> simp_all [runtimeInputBits, runtimePayloadBits]
  | cons payload rest ih =>
      intro right equal
      cases right with
      | nil => simp [runtimeInputBits, runtimePayloadBits] at equal
      | cons other tail =>
          dsimp only at equal
          rw [split, split, List.cons.injEq] at equal
          have first := congrArg (List.take κ) equal.2
          have remaining := congrArg (List.drop κ) equal.2
          have take (b : Bits κ) (r : List Bool) : (b.toList ++ r).take κ = b.toList := by
            simpa only [Bits.length_toList] using (List.take_left (l₁ := b.toList) (l₂ := r))
          have drop (b : Bits κ) (r : List Bool) : (b.toList ++ r).drop κ = r := by
            simpa only [Bits.length_toList] using (List.drop_left (l₁ := b.toList) (l₂ := r))
          rw [take, take] at first
          rw [drop, drop] at remaining
          exact congrArg₂ List.cons (List.ofFn_injective first) (ih remaining)

theorem nativeWorldPacket_injective {n κ : Nat} : Function.Injective (@nativeWorldPacket n κ) := by
  intro left right equal
  cases left <;> cases right <;> simp only [nativeWorldPacket, List.cons.injEq] at equal
  · exact congrArg Sum.inl (typed_runtime_input_injective equal.2)
  · simp at equal
  · simp at equal
  · apply congrArg Sum.inr
    apply compressionKey_injective n κ
    exact congrArg (fun packet => ((fixedBits (n + κ + 1)).decode packet).getD (fun _ => false)) equal.2
end Foundation.Hash.Native
