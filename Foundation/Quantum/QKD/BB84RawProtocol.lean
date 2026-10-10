import Mathlib.Data.Fintype.Sigma
import Foundation.Quantum.QKD.BB84Block
import Foundation.Quantum.ClassicalMap
import Foundation.Quantum.DiscardMiddle
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

/-! The raw-key stage of block BB84: basis sifting, public test values, a
specified test mask, acceptance/abort, and private raw keys. The quantum
record is processed by verified channels and the adversary receives only the
public projection plus its retained subsystem. Error correction and privacy
amplification are not silently represented by identity operations. -/
namespace Foundation.Quantum.QKD.RawProtocol
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024

structure PublicRecord (n : Nat) where
  aliceBases : Fin n → BB84Basis
  bobBases : Fin n → BB84Basis
  tested : Finset (Fin n)
  aliceTest : Fin n → Option (Fin 2)
  bobTest : Fin n → Option (Fin 2)
  accepted : Bool
  deriving Fintype, DecidableEq

structure Output (n : Nat) where
  transcript : PublicRecord n
  aliceKey : Fin n → Option (Fin 2)
  bobKey : Fin n → Option (Fin 2)
  deriving Fintype, DecidableEq

def matched {n : Nat} (alice bob : Fin n → BB84Basis) : Finset (Fin n) :=
  Finset.univ.filter (fun i => alice i = bob i)

def keyPositions {n : Nat} (alice bob : Fin n → BB84Basis) (T : Finset (Fin n)) : Finset (Fin n) :=
  matched alice bob \ T

def errors {n : Nat} (b c : Fin n → Fin 2) (T : Finset (Fin n)) : Nat :=
  (T.filter (fun i => b i ≠ c i)).card

/-- Insufficient key length, an invalid mask, or too many sampled errors causes abort. -/
def accepts {n : Nat} (alice bob : Fin n → BB84Basis) (b c : Fin n → Fin 2)
    (T : Finset (Fin n)) (minKey tolerance : Nat) : Bool :=
  decide (T ⊆ matched alice bob ∧ minKey ≤ (keyPositions alice bob T).card ∧ errors b c T ≤ tolerance)

def output {n : Nat} (alice bob : Fin n → BB84Basis) (b c : Fin n → Fin 2)
    (T : Finset (Fin n)) (minKey tolerance : Nat) : Output n where
  transcript := ⟨alice, bob, T, (fun i => if i ∈ T then some (b i) else none),
    (fun i => if i ∈ T then some (c i) else none), accepts alice bob b c T minKey tolerance⟩
  aliceKey i := if accepts alice bob b c T minKey tolerance ∧ i ∈ keyPositions alice bob T
    then some (b i) else none
  bobKey i := if accepts alice bob b c T minKey tolerance ∧ i ∈ keyPositions alice bob T
    then some (c i) else none

theorem abort_keys {n : Nat} (alice bob : Fin n → BB84Basis) (b c : Fin n → Fin 2)
    (T : Finset (Fin n)) (minKey tolerance : Nat)
    (h : accepts alice bob b c T minKey tolerance = false) :
    (output alice bob b c T minKey tolerance).aliceKey = (fun _ => none) ∧
    (output alice bob b c T minKey tolerance).bobKey = (fun _ => none) := by
  simp [output, h]

/-- Tested positions never occur in the private raw key. -/
theorem tested_not_key {n : Nat} (alice bob : Fin n → BB84Basis) (b c : Fin n → Fin 2)
    (T : Finset (Fin n)) (minKey tolerance : Nat) (i : Fin n) (hi : i ∈ T) :
    (output alice bob b c T minKey tolerance).aliceKey i = none ∧
    (output alice bob b c T minKey tolerance).bobKey i = none := by
  simp [output, keyPositions, hi]

/-- No hypothesis about the tested sample is used to assert agreement of untested bits. -/
theorem raw_keys_agree {n : Nat} (alice bob : Fin n → BB84Basis) (b c : Fin n → Fin 2)
    (T : Finset (Fin n)) (minKey tolerance : Nat)
    (h : ∀ i ∈ keyPositions alice bob T, b i = c i) :
    (output alice bob b c T minKey tolerance).aliceKey =
      (output alice bob b c T minKey tolerance).bobKey := by
  funext i
  simp only [output]
  split_ifs with hi
  · rw [h i hi.2]
  · rfl

/-- The complete raw output is encoded in a physical finite classical register. -/
def record {n : Nat} {e : Space} (A : BlockAttack n e) (alice bob : Fin n → BB84Basis)
    (b : Fin n → Fin 2) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    Density (.tensor (.register (Fintype.card (Output n))) (.tensor (qubits n) e)) :=
  (classicalMap (.tensor (qubits n) e) (fun r => Fintype.equivFin (Output n)
    (output alice bob b (blockOutcomeBits n r) T minKey tolerance))).run
      (A.outputRecord alice bob b)

/-- Only the public record is retained on the classical interface; the private keys are discarded. -/
def publicChannel (n : Nat) (e : Space) :
    Channel (.tensor (.register (Fintype.card (Output n))) (.tensor (qubits n) e))
      (.tensor (.register (Fintype.card (PublicRecord n))) e) :=
  (classicalMap (.tensor (qubits n) e) (fun r => Fintype.equivFin (PublicRecord n)
    (((Fintype.equivFin (Output n)).symm r).transcript))).seq
      (discardMiddle (.register (Fintype.card (PublicRecord n))) (qubits n) e)

/-- The adversary's actual output is the public transcript correlated with its quantum subsystem. -/
def publicState {n : Nat} {e : Space} (A : BlockAttack n e) (alice bob : Fin n → BB84Basis)
    (b : Fin n → Fin 2) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    Density (.tensor (.register (Fintype.card (PublicRecord n))) e) :=
  (publicChannel n e).run (record A alice bob b T minKey tolerance)

theorem publicState_normalized {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2) (T : Finset (Fin n))
    (minKey tolerance : Nat) : (publicState A alice bob b T minKey tolerance).matrix.trace = 1 :=
  (publicState A alice bob b T minKey tolerance).normalized

/-- Deterministic classical processing does not erase the retained quantum marginal. -/
theorem record_quantum_marginal {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2) (T : Finset (Fin n))
    (minKey tolerance : Nat) (i j : (qubits n).Basis × e.Basis) :
    (∑ r : Fin (Fintype.card (Output n)), (record A alice bob b T minKey tolerance).matrix (r,i) (r,j)) =
      ∑ s : Fin (Fintype.card (qubits n).Basis), (A.outputRecord alice bob b).matrix (s,i) (s,j) :=
  classicalMap_quantum_marginal (.tensor (qubits n) e) _ (A.outputRecord alice bob b).matrix i j

end
end Foundation.Quantum.QKD.RawProtocol
