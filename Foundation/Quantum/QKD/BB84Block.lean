import Foundation.Quantum.QKD.Qubits
import Foundation.Quantum.QKD.BB84Instrument

/-! Multi-signal BB84 quantum experiments. A single arbitrary finite-Kraus
channel attacks the whole block; product or per-signal independence is not
assumed. This supplies the experiment, not its finite-key security bound. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem basisInstrument_probability (a : Space) (ρ : Density a)
    (r : Fin (Fintype.card a.Basis)) :
    (basisInstrument a).probability ρ r =
      (basisEffect a ((Fintype.equivFin a.Basis).symm r)).probability ρ := by
  unfold Instrument.probability
  rw [Instrument.branch_trace]
  simp only [basisInstrument, Kraus.single_effect]
  change ((projector a _).conjTranspose * projector a _ * ρ.matrix).trace.re = _
  rw [projector_adjoint, projector_square]
  rfl

def blockMeasurement (n : Nat) (θ : Fin n → BB84Basis) :
    Instrument (qubits n) (qubits n) (Fintype.card (qubits n).Basis) :=
  (basisInstrument (qubits n)).pre (blockBasisChannel n θ)

def blockOutcomeBits (n : Nat) (r : Fin (Fintype.card (qubits n).Basis)) : Fin n → Fin 2 :=
  readBits ((Fintype.equivFin (qubits n).Basis).symm r)

def blockInputLabel (n : Nat) (b : Fin n → Fin 2) : Fin (Fintype.card (qubits n).Basis) :=
  Fintype.equivFin (qubits n).Basis (writeBits n b)

@[simp] theorem blockOutcomeBits_input (n : Nat) (b : Fin n → Fin 2) :
    blockOutcomeBits n (blockInputLabel n b) = b := by
  simp [blockOutcomeBits, blockInputLabel, read_write]

/-- For any block length and bases, honest matched decoding recovers the entire string. -/
theorem block_matched_correct (n : Nat) (θ : Fin n → BB84Basis) (b : Fin n → Fin 2) :
    (blockMeasurement n θ).probability (blockPrepare n θ b) (blockInputLabel n b) = 1 := by
  rw [blockMeasurement, Instrument.pre_probability, basisInstrument_probability,
    BB84Attack.basisEffect_probability, block_matched_matrix]
  simp [blockInputLabel, basisDensity]

/-- An arbitrary operation on the entire signal block, with a retained output environment. -/
abbrev BlockAttack (n : Nat) (e : Space) := Channel (qubits n) (.tensor (qubits n) e)

namespace BlockAttack
variable {n : Nat} {e : Space}

def jointState (A : BlockAttack n e) (alice : Fin n → BB84Basis) (b : Fin n → Fin 2) :
    Density (.tensor (qubits n) e) := A.run (blockPrepare n alice b)

def outputRecord (A : BlockAttack n e) (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2) :
    Density (.tensor (.register (Fintype.card (qubits n).Basis)) (.tensor (qubits n) e)) :=
  (((blockMeasurement n bob).amplify e).record).run (A.jointState alice b)

def outcome (A : BlockAttack n e) (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2) :
    Foundation.Probability.ProbComp (Fin (Fintype.card (qubits n).Basis)) :=
  ((blockMeasurement n bob).amplify e).classicalOutcome (A.jointState alice b)

theorem outcome_event (A : BlockAttack n e) (alice bob : Fin n → BB84Basis)
    (b : Fin n → Fin 2) (r : Fin (Fintype.card (qubits n).Basis)) :
    Foundation.Probability.eventProb (A.outcome alice bob b) (fun s => s = r) =
      ENNReal.ofReal ((blockMeasurement n bob).probability
        ((discardRight (qubits n) e).run (A.jointState alice b)) r) := by
  rw [outcome, Instrument.classicalOutcome_event, Instrument.amplify_probability]

theorem outputRecord_normalized (A : BlockAttack n e) (alice bob : Fin n → BB84Basis)
    (b : Fin n → Fin 2) : (A.outputRecord alice bob b).matrix.trace = 1 :=
  (A.outputRecord alice bob b).normalized

/-- Correlations with the environment remain in the complete block state after measurement. -/
theorem record_forget (A : BlockAttack n e) (alice bob : Fin n → BB84Basis)
    (b : Fin n → Fin 2) (i j : (qubits n).Basis × e.Basis) :
    (∑ r : Fin (Fintype.card (qubits n).Basis), (A.outputRecord alice bob b).matrix (r,i) (r,j)) =
      (((blockMeasurement n bob).amplify e).forget.run (A.jointState alice b)).matrix i j :=
  Instrument.record_forget_marginal ((blockMeasurement n bob).amplify e)
    (A.jointState alice b).matrix i j

end BlockAttack
end
end Foundation.Quantum.QKD
