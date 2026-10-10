import Foundation.Quantum.QKD.RepetitionReconciliation

/-! A concrete reconciliation code for every remaining length, including 0.
Full triples disclose two parity bits and correct one error each. The suffix
of length n % 3 is sent explicitly, so it is neither dropped nor padded.
This is an implementation choice, not a code theorem in the source thesis. -/
namespace Foundation.Quantum.QKD.ArbitraryReconciliation
open RepetitionReconciliation

abbrev Word (n : Nat) := Fin n → Fin 2
abbrev Message (n : Nat) := (Fin (n/3) → RepetitionReconciliation.Message) × Word (n%3)

def blockIndex (n : Nat) (j : Fin (n/3)) (i : Fin 3) : Fin n :=
  ⟨3*j.val+i.val, by have := Nat.mod_lt n (by decide : 0 < 3); omega⟩

def suffixIndex (n : Nat) (i : Fin (n%3)) : Fin n :=
  ⟨3*(n/3)+i.val, by omega⟩

def block {n : Nat} (x : Word n) (j : Fin (n/3)) : Triple := fun i => x (blockIndex n j i)

def suffix {n : Nat} (x : Word n) : Word (n%3) := fun i => x (suffixIndex n i)

def message {n : Nat} (alice : Word n) : Message n :=
  (fun j => syndrome (block alice j), suffix alice)

/-- Bob uses only his word and the public parity/suffix message. -/
def decode {n : Nat} (bob : Word n) (m : Message n) : Word n := fun i =>
  if h : i.val < 3*(n/3) then
    RepetitionReconciliation.decode (block bob ⟨i.val/3,by omega⟩)
      (m.1 ⟨i.val/3,by omega⟩) ⟨i.val%3,Nat.mod_lt _ (by decide)⟩
  else m.2 ⟨i.val-3*(n/3),by omega⟩

theorem decode_correct {n : Nat} (alice bob : Word n)
    (h : ∀ j, errors (block alice j) (block bob j) ≤ 1) :
    decode bob (message alice) = alice := by
  funext i
  unfold decode
  split_ifs with hi
  · rw [message, RepetitionReconciliation.decode_correct _ _ (h _)]
    change alice ⟨3*(i.val/3)+i.val%3,_⟩ = alice i
    apply congrArg alice
    apply Fin.ext
    dsimp
    omega
  · change alice ⟨3*(n/3)+(i.val-3*(n/3)),_⟩ = alice i
    apply congrArg alice
    apply Fin.ext
    dsimp
    omega

def reconcile {n : Nat} (keys : Word n × Word n) :=
  ((keys.1,decode keys.2 (message keys.1)),message keys.1)

theorem reconcile_correct {n : Nat} (alice bob : Word n)
    (h : ∀ j, errors (block alice j) (block bob j) ≤ 1) :
    (reconcile (alice,bob)).1.1 = (reconcile (alice,bob)).1.2 :=
  (decode_correct alice bob h).symm

/-- The actual number of disclosed bits, charging the entire suffix. -/
def publicBits (n : Nat) : Nat := 2*(n/3)+n%3

theorem message_card (n : Nat) : Fintype.card (Message n) = 2^(publicBits n) := by
  simp only [Message, Word, RepetitionReconciliation.Message, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, publicBits, ← pow_mul, ← pow_add]

/-- Exact arithmetic of the public-bit budget and the number of complete
triples. This identity alone is not a quantum entropy bound. -/
theorem publicBits_add_blocks (n : Nat) : publicBits n + n/3 = n := by
  unfold publicBits
  omega

noncomputable section

def quantumMessage {n : Nat} (x : (qubits n).Basis) : Message n := message (readBits x)

def quantumDecode {n : Nat} (bob : (qubits n).Basis) (m : Message n) : (qubits n).Basis :=
  writeBits n (decode (readBits bob) m)

theorem quantum_correct {n : Nat} (alice bob : (qubits n).Basis)
    (h : ∀ j, errors (block (readBits alice) j) (block (readBits bob) j) ≤ 1) :
    quantumDecode bob (quantumMessage alice) = alice := by
  unfold quantumDecode quantumMessage
  rw [decode_correct _ _ h]
  exact write_read n alice

end
end Foundation.Quantum.QKD.ArbitraryReconciliation
