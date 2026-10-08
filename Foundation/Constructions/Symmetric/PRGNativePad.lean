import Foundation.Constructions.Symmetric.PRGEncryption
import Foundation.Crypto.Semantics.Machine.NativePadObservation

/-! PRG encryption reuses the actual native masking/erasure/serialization/
observer code. The pad is sampled from G.real as an experiment distribution.
Its computation and preparation of the physical packet are not free native
instructions: NativePadPipeline supplies their separately certified code.
PRG security of both message-dependent reductions remains a premise. -/
namespace Foundation.Symmetric.PRGNativePad
open Machine Foundation.Probability TimedExecution
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

def input {width : Nat} (pad message : Bits width) : NativePadEncryption.Input :=
  {pad := pad.toList, message := message.toList, sameLength := by simp}

theorem cipher_input {width : Nat} (pad message : Bits width) :
    NativePadEncryption.cipher (input pad message) = (Bits.xor message pad).toList := by
  change OneTimePad.xorList pad.toList message.toList = (Bits.xor message pad).toList
  rw [Bits.xor_comm message pad, OneTimePad.toList_xor]

noncomputable def observer (O : PolynomialObserver) {width : Nat} : Bits width → PMF Bool :=
  fun ciphertext => O.observe (FiniteBitEncoding.delimit ciphertext.toList)

noncomputable def game (G : Generator) (n : Nat) (O : PolynomialObserver) (message : Bits (G.outputLength n)) : PMF Bool :=
  (G.real n).bind (fun pad => (NativePadObservation.costed O (input pad message)).map
    (fun result => NativeSerializedObservation.decision result.1))

theorem game_eq (G : Generator) (n : Nat) (O : PolynomialObserver) (message : Bits (G.outputLength n)) :
    game G n O message = (G.ciphertext n message).bind (observer O) := by
  unfold game Generator.ciphertext
  rw [PMF.bind_map]
  congr 1
  funext pad
  rw [NativePadObservation.costed_observe, cipher_input]
  rfl

theorem run_game_eq (G : Generator) (n : Nat) (O : PolynomialObserver) (message : Bits (G.outputLength n))
    (horizon : Nat) (hTime : NativePadObservation.timeBound O (G.outputLength n) ≤ horizon) :
    (G.real n).bind (fun pad =>
      (runToBoundary (stepPMF (NativePadObservation.link O).code) Configuration.halted horizon
        (NativePadEncryption.initial (input pad message))).map
          (fun result => NativeSerializedObservation.decision result.1)) = game G n O message := by
  unfold game
  congr 1
  funext pad
  rw [NativePadObservation.costed_horizon O (input pad message) horizon (by simpa [input] using hTime)]

theorem advantage_le (G : Generator) (n : Nat) (O : PolynomialObserver) (messages : G.Messages n) :
    probabilityGap (eventProb (game G n O messages.1) (· = true))
      (eventProb (game G n O messages.2) (· = true)) ≤
        G.prgGoal.advantage n messages (G.reduce messages false (observer O)) +
        G.prgGoal.advantage n messages (G.reduce messages true (observer O)) := by
  rw [game_eq, game_eq]
  exact G.advantage_le n messages (observer O)

theorem advantage_le_sum (G : Generator) (n : Nat) (O : PolynomialObserver) (messages : G.Messages n)
    (leftBound rightBound : ℝ≥0∞)
    (hLeft : G.prgGoal.advantage n messages (G.reduce messages false (observer O)) ≤ leftBound)
    (hRight : G.prgGoal.advantage n messages (G.reduce messages true (observer O)) ≤ rightBound) :
    probabilityGap (eventProb (game G n O messages.1) (· = true))
      (eventProb (game G n O messages.2) (· = true)) ≤ leftBound + rightBound :=
  (advantage_le G n O messages).trans (add_le_add hLeft hRight)

theorem time_polynomial (G : Generator) (O : PolynomialObserver) (hWidth : PolynomiallyBounded G.outputLength) :
    PolynomiallyBounded (fun n => NativePadObservation.timeBound O (G.outputLength n)) :=
  ((((PolynomiallyBounded.const 54).mul hWidth).add (PolynomiallyBounded.const 40)).add
    (O.budget_profile_polynomial (((PolynomiallyBounded.const 2).mul hWidth).add (PolynomiallyBounded.const 1))))

end Foundation.Symmetric.PRGNativePad
