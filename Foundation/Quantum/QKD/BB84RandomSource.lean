import Foundation.Quantum.MixtureLaws
import Foundation.Quantum.QKD.BB84RawSource
import Foundation.Quantum.QKD.BB84Finalization

/-! The complete randomized raw experiment using delayed entangled sources.
The two basis strings are independently uniform; the test set uses the existing
fresh nonreplacement distribution and insufficient-population abort guard. -/
namespace Foundation.Quantum.QKD.BB84RandomSource
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure Bases (n : Nat) where
  alice : Fin n → BB84Basis
  bob : Fin n → BB84Basis
  deriving Fintype, DecidableEq

instance (n : Nat) : Nonempty (Bases n) := ⟨⟨fun _ => .Z, fun _ => .Z⟩⟩

def Bases.seed {n : Nat} (b : Bases n) : Randomized.Seed n :=
  ⟨b.alice, b.bob, fun _ => 0⟩

def seedEquiv (n : Nat) : Bases n × (qubits n).Basis ≃ Randomized.Seed n where
  toFun p := ⟨p.1.alice, p.1.bob, readBits p.2⟩
  invFun s := (⟨s.alice,s.bob⟩, writeBits n s.bits)
  left_inv := by intro ⟨⟨alice,bob⟩,x⟩; simp [write_read]
  right_inv := by intro ⟨alice,bob,bits⟩; simp [read_write]

def record {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Density (BB84RawSource.outputSpace n e) :=
  Density.mixture (Foundation.Probability.uniform (Bases n)) (fun b =>
    Density.mixture (Randomized.testDistribution b.seed k) (fun T =>
      BB84RawSource.state A b.alice b.bob T
        (Randomized.requiredLength b.seed k minKey) tolerance))

/-- Exact decomposition of the original probability distribution, including
the test set. Private bits cannot change either the sampling or abort guard. -/
theorem randomized_decomposed {n : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    (Randomized.record A k minKey tolerance).matrix =
      (Density.mixture (Foundation.Probability.uniform (Bases n)) (fun b =>
        Density.mixture (Randomized.testDistribution b.seed k) (fun T =>
          Density.mixture (Foundation.Probability.uniform (qubits n).Basis) (fun x =>
            RawProtocol.record A b.alice b.bob (readBits x) T
              (Randomized.requiredLength b.seed k minKey) tolerance)))).matrix := by
  calc
    _ = (Density.mixture (Randomized.seedDistribution n) (fun s =>
        Density.mixture (Randomized.testDistribution s k) (fun T =>
          Randomized.conditionalRecord A ⟨s,T⟩ k minKey tolerance))).matrix := by
      rw [Randomized.record, Randomized.configurationDistribution, Density.mixture_bind]
      apply Density.mixture_congr_matrix
      intro s
      exact Density.mixture_map _ _ _
    _ = (Density.mixture (Foundation.Probability.uniform (Bases n × (qubits n).Basis)) (fun p =>
        Density.mixture (Randomized.testDistribution (seedEquiv n p) k) (fun T =>
          Randomized.conditionalRecord A ⟨seedEquiv n p,T⟩ k minKey tolerance))).matrix :=
      (Density.mixture_uniform_equiv (seedEquiv n) _).symm
    _ = (Density.mixture (Foundation.Probability.uniform (Bases n)) (fun b =>
        Density.mixture (Foundation.Probability.uniform (qubits n).Basis) (fun x =>
          Density.mixture (Randomized.testDistribution b.seed k) (fun T =>
            RawProtocol.record A b.alice b.bob (readBits x) T
              (Randomized.requiredLength b.seed k minKey) tolerance)))).matrix := by
      rw [Density.mixture_uniform_product]
      rfl
    _ = _ := by
      apply Density.mixture_congr_matrix
      intro b
      exact Density.mixture_commute _ _ _

/-- Equality of the actual entire randomized experiment, not just the
classical outcome probabilities or Eve's marginal. -/
theorem record_eq {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    (record A k minKey tolerance).matrix = (Randomized.record A k minKey tolerance).matrix := by
  rw [randomized_decomposed]
  apply Density.mixture_congr_matrix
  intro b
  apply Density.mixture_congr_matrix
  intro T
  exact BB84RawSource.interpreted A b.alice b.bob T
    (Randomized.requiredLength b.seed k minKey) tolerance

theorem keyState_eq {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
      (record A k minKey tolerance)).matrix = (Randomized.keyState A k minKey tolerance).matrix := by
  exact congrArg (discardMiddle (.register (Fintype.card (RawProtocol.Output n)))
    (qubits n) e).toKraus.apply (record_eq A k minKey tolerance)

theorem publicState_eq {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    ((RawProtocol.publicChannel n e).run (record A k minKey tolerance)).matrix =
      (Randomized.publicState A k minKey tolerance).matrix := by
  exact congrArg (RawProtocol.publicChannel n e).toKraus.apply (record_eq A k minKey tolerance)

/-- Fresh public hash randomness is sampled after the whole raw experiment.
This definition makes no assumption that the chosen hash is secure. -/
def finalState {n length : Nat} {S : Type} [Fintype S] {e : Space}
    (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    Density (.tensor (IdealKey.register (Finalization.Transcript n S) length) e) :=
  Density.mixture p (fun seed => (Finalization.channel e seed hash).run
    ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
      (record A k minKey tolerance)))

theorem finalState_eq {n length : Nat} {S : Type} [Fintype S] {e : Space}
    (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    (finalState A k minKey tolerance p hash).matrix =
      (Finalization.state A k minKey tolerance p hash).matrix := by
  apply Density.mixture_congr_matrix
  intro seed
  exact congrArg (Finalization.channel e seed hash).toKraus.apply
    (keyState_eq A k minKey tolerance)

/-- An exact change of source preserves the existing ideal-key security
judgment in both directions. It supplies no missing secrecy premise. -/
theorem secure_iff {n length : Nat} {S : Type} [Fintype S] {e : Space}
    (A : BlockAttack n e) (k minKey tolerance : Nat) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) (ε : ℝ) :
    IdealKey.Secure (finalState A k minKey tolerance p hash) ε ↔
      IdealKey.Secure (Finalization.state A k minKey tolerance p hash) ε := by
  have ext_matrix {a : Space} {ρ σ : Density a} (h : ρ.matrix = σ.matrix) : ρ = σ := by
    cases ρ
    cases σ
    cases h
    rfl
  rw [ext_matrix (finalState_eq A k minKey tolerance p hash)]

end
end Foundation.Quantum.QKD.BB84RandomSource
