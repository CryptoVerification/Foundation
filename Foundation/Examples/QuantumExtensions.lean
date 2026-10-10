import Foundation.Quantum.Security
import Foundation.Quantum.PredicateLogic
import Foundation.Quantum.Contexts
import Foundation.Quantum.Infinite
import Foundation.Quantum.PartialTrace

namespace Foundation.Quantum.ExtensionExamples
open Foundation.Logic
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

def bitInstrument : Instrument .bit .bit 2 where
  branch r := Kraus.single (projector .bit r)
  complete := by simpa only [Kraus.single_effect] using projector_complete .bit

def mixedInput : Density .bit := mixChannel.run (basisDensity .bit 0)

theorem measured_probability (r : Fin 2) : bitInstrument.probability mixedInput r = 1 / 2 := by
  dsimp [Instrument.probability, bitInstrument, mixedInput, mixChannel,
    Channel.ofIsometry, Channel.run]
  simp only [Kraus.single_apply]
  fin_cases r <;>
    norm_num [Instrument.probability, bitInstrument, Kraus.single_apply,
      mixedInput, mixChannel, Channel.ofIsometry, Channel.run, basisDensity,
      projector, Kraus.apply, Kraus.single, Matrix.trace, Matrix.diag, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply, Fin.sum_univ_two,
      Op.mix, Space.Basis, Space.basisFintype, Space.basisDecidableEq,
      map_ofNat, Complex.div_re, Complex.div_im]

/-- Recorded outcomes are actual normalized states, and their distribution is verified. -/
theorem recorded_normalized : (bitInstrument.record.run mixedInput).matrix.trace = 1 :=
  (bitInstrument.record.run mixedInput).normalized

def channelAssignment : Security.Assignment := fun a _ => dephase a

/-- The error calculus has a concrete, auxiliary-system-complete closed derivation. -/
def dephaseProof : Security.Proof (Context.empty Security.presentation)
    (.seq (.dephase .bit) (.dephase .bit)) (.dephase .bit) 0 :=
  Security.Proof.dephaseIdem .bit

theorem interpreted_dephase :
    Approx ((dephase .bit).seq (dephase .bit)) (dephase .bit) 0 :=
  Security.sound channelAssignment dephaseProof (fun i => Fin.elim0 i)

/-- A proved cryptographic primitive is composed syntactically with a following operation. -/
def protectedOtp : Security.Proof (Context.empty Security.presentation)
    (.seq .otpAverage (.variable .bit 0)) (.seq .otpIdeal (.variable .bit 0)) (0 + 0) :=
  Security.Proof.seq Security.Proof.otpPrivacy (Security.Proof.refl _)

theorem otp_interpreted : Approx (OneTimePad.average.seq (dephase .bit))
    (OneTimePad.ideal.seq (dephase .bit)) 0 := by
  have h := Security.sound channelAssignment protectedOtp (fun i => Fin.elim0 i)
  change Approx (OneTimePad.average.seq (dephase .bit))
    (OneTimePad.ideal.seq (dephase .bit)) (0 + 0) at h
  simpa only [zero_add] using h

/-- Two independent assumptions become one error bound through an actual derivation. -/
example (ε δ : ℝ) (hε : Approx (dephase .bit) (dephase .bit) ε)
    (hδ : Approx (dephase .bit) (dephase .bit) δ) :
    Approx ((dephase .bit).seq (dephase .bit)) ((dephase .bit).seq (dephase .bit)) (ε + δ) :=
  Security.sound channelAssignment
    (Security.twoStage (.variable .bit 0) (.variable .bit 1)
      (.variable .bit 2) (.variable .bit 3) ε δ)
    (Fin.cases hε (fun _ => hδ))

/-- The source's non-distributive lattice law is a derivation, not a semantic axiom. -/
def orthomodularProof (P Q : PredicateLogic.Formula .bit) :
    Derivation PredicateLogic.presentation (.singleton (PredicateLogic.entails P Q))
      (PredicateLogic.entails Q (.join P (.meet (.orth P) Q))) :=
  .apply (T := PredicateLogic.presentation) (.orthomodular P Q) (fun _ => .hypothesis 0)

/-- Existential transport along the concrete measurement gate has a closed proof. -/
def mixTransport (P : PredicateLogic.Formula .bit) :
    Derivation PredicateLogic.presentation (Context.empty PredicateLogic.presentation)
      (PredicateLogic.entails P (.pull .mix (.existsAlong .mix P))) :=
  .apply (T := PredicateLogic.presentation) (.existsElim .mix P (.existsAlong .mix P)) (fun _ =>
    .apply (T := PredicateLogic.presentation) (.refl (.existsAlong .mix P)) (fun i => Fin.elim0 i))

theorem mix_transport_interpreted (σ : Quantum.Assignment) (ν : PredicateLogic.Assignment)
    (P : PredicateLogic.Formula .bit) :
    P.eval σ ν ≤ Predicate.pull Op.mix (Predicate.existsAlong Op.mix (P.eval σ ν)) :=
  PredicateLogic.sound σ ν (mixTransport P) (fun i => Fin.elim0 i)

/-- These rank-one projectors do not commute; measurement order is observable. -/
theorem noncommuting_measurements :
    projector .bit 0 * (Op.mix * projector .bit 0 * Op.mix.conjTranspose) ≠
      (Op.mix * projector .bit 0 * Op.mix.conjTranspose) * projector .bit 0 := by
  intro h
  have he := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [projector, Op.mix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Space.Basis, Space.basisFintype, Space.basisDecidableEq,
    Complex.ext_iff] at he

/-- Intuitionistic implication has a closed proof interpreted in every context model. -/
def implicationProof (P : Bohr.Formula) :
    Derivation Bohr.presentation (Context.empty Bohr.presentation) (.top, .imp P P) :=
  .apply (T := Bohr.presentation) (.impIntro .top P P) (fun _ =>
    .apply (T := Bohr.presentation) (.meetRight .top P) (fun i => Fin.elim0 i))

theorem implication_interpreted (A : Type) [CStarAlgebra A] (ν : Nat → Bohr.Persistent A)
    (P : Bohr.Formula) : (Bohr.model A ν).Carrier (.top, .imp P P) :=
  Bohr.sound A ν (implicationProof P) (fun i => Fin.elim0 i)

end
end Foundation.Quantum.ExtensionExamples
