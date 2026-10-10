import Foundation.Quantum.DilationAuxiliary
import Foundation.Quantum.QKD.BB84SourceReplacement

/-! An explicit pure joint source after every represented finite-Kraus BB84
attack. Its added environment can be given to an adversary; discarding only
that environment recovers the original attack with Alice still retained. -/
namespace Foundation.Quantum.QKD.BB84PurifiedSource
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev jointSpace {n : Nat} {e : Space} (A : BlockAttack n e) :=
  Space.tensor (.tensor (.tensor (qubits n) e) (.register (Fintype.card A.index))) (qubits n)

def vector {n : Nat} {e : Space} (A : BlockAttack n e) : (jointSpace A).Basis → ℂ :=
  A.pureDilationVector (qubits n) (SourceReplacement.pairVector (qubits n) (hadamardCoefficient^n))

theorem unit {n : Nat} {e : Space} (A : BlockAttack n e) :
    PureProjection.bracket (vector A) (vector A) = 1 :=
  A.pure_dilation_unit (qubits n) _
    (SourceReplacement.pair_unit (qubits n) _ (BB84Source.normalized n))

def state {n : Nat} {e : Space} (A : BlockAttack n e) : Density (jointSpace A) :=
  (A.dilated.amplify (qubits n)).run (BB84Source.entangled n)

theorem pure {n : Nat} {e : Space} (A : BlockAttack n e) :
    (state A).matrix = PureProjection.rank (vector A) (vector A) :=
  A.pure_dilation (qubits n) _

theorem recover {n : Nat} {e : Space} (A : BlockAttack n e) :
    (((discardRight (.tensor (qubits n) e) (.register (Fintype.card A.index))).amplify
      (qubits n)).run (state A)).matrix =
      ((A.amplify (qubits n)).run (BB84Source.entangled n)).matrix :=
  A.discard_dilation_amplify (qubits n) _

end
end Foundation.Quantum.QKD.BB84PurifiedSource
