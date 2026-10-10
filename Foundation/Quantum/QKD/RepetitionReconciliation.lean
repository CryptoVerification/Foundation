import Foundation.Quantum.QKD.PairwiseTestPrivacy

/-! A concrete binary [3,1,3] coset reconciliation code. Alice discloses
(x₀+x₁,x₀+x₂); Bob uses only his word and these two public bits. Blocks
correct one error each. This is an explicit implementation choice, not a
code or a key-rate theorem asserted in Heunen or Bouman--Fehr. -/
namespace Foundation.Quantum.QKD.RepetitionReconciliation

abbrev Triple := Fin 3 → Fin 2
abbrev Message := Fin 2 → Fin 2

def syndrome (x : Triple) : Message := ![x 0 + x 1, x 0 + x 2]

def leader (s : Message) : Triple :=
  if s 0 = 1 ∧ s 1 = 1 then ![1,0,0]
  else if s 0 = 1 then ![0,1,0]
  else if s 1 = 1 then ![0,0,1]
  else ![0,0,0]

def decode (bob : Triple) (message : Message) : Triple :=
  fun i => bob i + leader (fun j => syndrome bob j + message j) i

def errors (alice bob : Triple) : Nat :=
  (Finset.univ.filter (fun i => alice i ≠ bob i)).card

/-- Exhaustion of 64 pairs of binary words, checked by the Lean kernel. -/
theorem decode_correct : ∀ alice bob : Triple,
    errors alice bob ≤ 1 → decode bob (syndrome alice) = alice := by decide

/-- A decoder always returns the indicated coset; this alone is not correctness. -/
theorem decode_syndrome : ∀ bob : Triple, ∀ message : Message,
    syndrome (decode bob message) = message := by decide

/-- Two errors can silently select the wrong word of the same coset. -/
theorem double_error_failure :
    decode ![1,1,0] (syndrome ![0,0,0]) = ![1,1,1] := by decide

/-- The disclosed parity values leave two possible words, rather than revealing
all three bits. This counting fact is not a conditional quantum entropy bound. -/
theorem fiber_card : ∀ message : Message,
    (Finset.univ.filter (fun x : Triple => syndrome x = message)).card = 2 := by decide

def blockMessage {b : Nat} (alice : Fin b → Triple) : Fin (b*2) → Fin 2 :=
  fun i => syndrome (alice (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

def blockDecode {b : Nat} (bob : Fin b → Triple) (message : Fin (b*2) → Fin 2) :
    Fin b → Triple :=
  fun j => decode (bob j) (fun i => message (finProdFinEquiv (j,i)))

theorem block_correct {b : Nat} (alice bob : Fin b → Triple)
    (h : ∀ j, errors (alice j) (bob j) ≤ 1) :
    blockDecode bob (blockMessage alice) = alice := by
  funext j
  simpa only [blockDecode, blockMessage, Equiv.symm_apply_apply] using
    decode_correct (alice j) (bob j) (h j)

/-- A concrete public classical reconciliation map, with no access to Alice's
word in Bob's decoder beyond the transmitted message. -/
def reconcile {b : Nat} (keys : (Fin b → Triple) × (Fin b → Triple)) :=
  ((keys.1, blockDecode keys.2 (blockMessage keys.1)), blockMessage keys.1)

theorem reconcile_correct {b : Nat} (alice bob : Fin b → Triple)
    (h : ∀ j, errors (alice j) (bob j) ≤ 1) :
    (reconcile (alice,bob)).1.1 = (reconcile (alice,bob)).1.2 := by
  exact (block_correct alice bob h).symm

/-- Pack consecutive triples of an actual remaining BB84 key. The length
restriction is explicit; there is no discarded or silently padded suffix. -/
def packed {b : Nat} (x : (qubits (b*3)).Basis) : Fin b → Triple :=
  fun j i => readBits x (finProdFinEquiv (j,i))

def quantumMessage {b : Nat} (x : (qubits (b*3)).Basis) : Fin (b*2) → Fin 2 :=
  blockMessage (packed x)

def quantumDecode {b : Nat} (bob : (qubits (b*3)).Basis)
    (message : Fin (b*2) → Fin 2) : (qubits (b*3)).Basis :=
  writeBits (b*3) (fun i => blockDecode (packed bob) message
    (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)

theorem quantum_correct {b : Nat} (alice bob : (qubits (b*3)).Basis)
    (h : ∀ j, errors (packed alice j) (packed bob j) ≤ 1) :
    quantumDecode bob (quantumMessage alice) = alice := by
  unfold quantumDecode quantumMessage
  rw [block_correct _ _ h]
  simp only [packed]
  change writeBits (b*3) (fun i => readBits alice (finProdFinEquiv (finProdFinEquiv.symm i))) = alice
  simp only [Equiv.apply_symm_apply]
  exact write_read (b*3) alice

end Foundation.Quantum.QKD.RepetitionReconciliation
