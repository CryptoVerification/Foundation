import Foundation.Quantum.QKD.CommonKeyProcessing
import Foundation.Quantum.ClassicalDiscard

/-! Discard a side subsystem while retaining the entire classical record and
remaining quantum system. No independence or separability is required. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
set_option backward.isDefEq.respectTransparency false

def discardFirst (b e : Space) : Channel (.tensor b e) e :=
  (BasisChannel.channel (Equiv.prodComm b.Basis e.Basis)).seq (discardRight e b)

theorem discardFirst_entry (b e : Space) (A : Operator (.tensor b e)) (u v : e.Basis) :
    (discardFirst b e).toKraus.apply A u v = ∑ r : b.Basis, A (r,u) (r,v) := by
  unfold discardFirst
  rw [Channel.seq, Kraus.seq_apply, discardRight_apply, BasisChannel.apply]
  rfl

theorem discardFirst_retained (a b e : Space) (A : Operator (.tensor a (.tensor b e))) :
    (rightChannel a (discardFirst b e)).toKraus.apply A = (discardMiddle a b e).toKraus.apply A := by
  ext ⟨i,u⟩ ⟨j,v⟩
  rw [rightChannel_entry, discardFirst_entry, discardMiddle_apply]
  rfl

end
end Foundation.Quantum.QKD.Subnormalized
