import Foundation.Quantum.QKD.BB84PreparedRaw
import Foundation.Quantum.QKD.BB84CNOTLogic

/-! Interpret the closed error-first derivation on the basis-independent
source attacked by an actual finite-Kraus block channel. Its output is the
existing uniform prepare/attack raw record, retaining Eve and discarding Bob.
The restriction to common bases is explicit; no final-key security is claimed. -/
namespace Foundation.Quantum.QKD.BB84PreparedRawInterpretation
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem interpreted {n : Nat} {e : Space} (A : BlockAttack n e)
    (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    (BB84DecisionRaw.decided θ e T minKey tolerance).toKraus.apply
        (BB84PreparedInput.input A).matrix =
      (BB84PreparedRaw.prepared A θ T minKey tolerance).matrix := by
  have h := BB84CNOTLogic.sound (BB84PreparedInput.input A)
    (fun _ => Channel.identity (BB84CNOTLogic.recordSpace n e))
    (BB84CNOTLogic.decidedRawProof θ T minKey tolerance) (fun i => Fin.elim0 i)
  change (BB84DecisionRaw.decided θ e T minKey tolerance).toKraus.apply
      (BB84PreparedInput.input A).matrix =
    (BB84DeferredRaw.reference θ e T minKey tolerance).toKraus.apply
      (BB84PreparedInput.input A).matrix at h
  exact h.trans (BB84PreparedRaw.reference_prepared A θ T minKey tolerance)

/-- Project the same interpreted equality to the public transcript and Eve.
Private raw keys are physically forgotten by the classical channel. -/
theorem public_interpreted {n : Nat} {e : Space} (A : BlockAttack n e)
    (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    (BB84DeferredRaw.publicChannel n e).toKraus.apply
      ((BB84DecisionRaw.decided θ e T minKey tolerance).toKraus.apply
        (BB84PreparedInput.input A).matrix) =
    ((BB84DeferredRaw.publicChannel n e).run
      (BB84PreparedRaw.prepared A θ T minKey tolerance)).matrix :=
  congrArg (BB84DeferredRaw.publicChannel n e).toKraus.apply
    (interpreted A θ T minKey tolerance)

/-- The public projection is the existing prepare/attack public state itself,
including its quantum correlation with Eve, not just a transcript law. -/
theorem public_experiment {n : Nat} {e : Space} (A : BlockAttack n e)
    (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    (BB84DeferredRaw.publicChannel n e).toKraus.apply
      ((BB84DecisionRaw.decided θ e T minKey tolerance).toKraus.apply
        (BB84PreparedInput.input A).matrix) =
      (Density.mixture (Foundation.Probability.uniform (qubits n).Basis) (fun a =>
        RawProtocol.publicState A θ θ (readBits a) T minKey tolerance)).matrix :=
  (public_interpreted A θ T minKey tolerance).trans
    (BB84PreparedRaw.public_prepared A θ T minKey tolerance)

end
end Foundation.Quantum.QKD.BB84PreparedRawInterpretation
