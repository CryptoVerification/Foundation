import Foundation.Quantum.QKD.ArbitraryReconciliation

/-! Exact padded public-message representation in the original position
count. This has a fixed type across test configurations; no syndrome bit is
silently dropped. The decoder recovers the entire message from this record. -/
namespace Foundation.Quantum.QKD.ArbitraryReconciliation

def messageRecord {m n : Nat} (_h : publicBits m ≤ n) (msg : Message m) : Word n := fun i =>
  if hi : i.val < 2*(m/3) then
    msg.1 ⟨i.val/2,by omega⟩ ⟨i.val%2,Nat.mod_lt _ (by decide)⟩
  else if hj : i.val < publicBits m then msg.2 ⟨i.val-2*(m/3),by unfold publicBits at hj; omega⟩
  else 0

def messageFromRecord {m n : Nat} (h : publicBits m ≤ n) (record : Word n) : Message m :=
  (fun j i => record ⟨2*j.val+i.val,by unfold publicBits at h; omega⟩,
    fun i => record ⟨2*(m/3)+i.val,by unfold publicBits at h; omega⟩)

theorem message_roundtrip {m n : Nat} (h : publicBits m ≤ n) (msg : Message m) :
    messageFromRecord h (messageRecord h msg) = msg := by
  apply Prod.ext
  · funext j i
    simp only [messageFromRecord, messageRecord]
    rw [dif_pos (show 2*j.val+i.val < 2*(m/3) by omega)]
    have hj : (⟨(2*j.val+i.val)/2,by omega⟩ : Fin (m/3)) = j := by
      apply Fin.ext
      dsimp
      omega
    have hi : (⟨(2*j.val+i.val)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2) = i := by
      apply Fin.ext
      dsimp
      omega
    rw [hj,hi]
  · funext i
    simp only [messageFromRecord, messageRecord]
    rw [dif_neg (show ¬ 2*(m/3)+i.val < 2*(m/3) by omega),
      dif_pos (show 2*(m/3)+i.val < publicBits m by unfold publicBits; omega)]
    apply congrArg msg.2
    apply Fin.ext
    dsimp
    omega

theorem messageRecord_injective {m n : Nat} (h : publicBits m ≤ n) :
    Function.Injective (messageRecord h) := by
  intro x y hxy
  have he := congrArg (messageFromRecord h) hxy
  simpa only [message_roundtrip] using he

end Foundation.Quantum.QKD.ArbitraryReconciliation
