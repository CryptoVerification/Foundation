import Foundation.Constructions.Symmetric.PRGNativeReductionConcrete
import Foundation.Crypto.Semantics.Machine.NativeSingleChallengeExecution

/-! Execute the concrete PRG reduction from a public message alone. The
external challenge is queried once, loaded in delimiter encoding, and passed
to the actual fixed native packet preparer and observer. The controller is
explicit; no flattening into the native instruction set is assumed. -/
namespace Foundation.Symmetric.PRGNativeQueryExecution
open Machine Foundation.Probability TimedExecution
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

variable (G : Generator) (hWidth : PolynomiallyBounded G.outputLength) (O : PolynomialObserver)

def publicInput (n : Nat) (message : Bits (G.outputLength n)) : List Bool :=
  List.replicate n true ++ false :: FiniteBitEncoding.delimit message.toList

theorem publicInput_length (n : Nat) (message : Bits (G.outputLength n)) :
    (publicInput G n message).length = n + 2 * G.outputLength n + 2 := by
  simp [publicInput, FiniteBitEncoding.delimit_length]
  omega

noncomputable def component :=
  (NativePadPipeline.PhysicalPreparation.link NativePadPacketPreparation.physical O).component

def adapt (n : Nat) (message challenge : Bits (G.outputLength n)) : NativePadPacketPreparation.Input :=
  (n, PRGNativePad.input challenge message)

theorem entry (n : Nat) (message challenge : Bits (G.outputLength n)) :
    (component O).procedure.execution.entry (adapt G n message challenge) =
      Configuration.initial (publicInput G n message ++ FiniteBitEncoding.delimit challenge.toList) := by
  change (NativePadPipeline.PhysicalPreparation.link NativePadPacketPreparation.physical O).native.execution.entry
    (adapt G n message challenge) = _
  rw [NativePadPipeline.PhysicalPreparation.entry]
  change Configuration.initial (PRGNativeReduction.rawInput n message challenge) = _
  simp [PRGNativeReduction.rawInput, publicInput, List.append_assoc]

include hWidth in
theorem consumer_budget (n : Nat) (message challenge : Bits (G.outputLength n)) :
    (component O).procedure.execution.budget (adapt G n message challenge) ≤
      PRGNativeReductionConcrete.timeBound G O n := by
  change (NativePadPipeline.PhysicalPreparation.link
    (PRGNativeReductionConcrete.preparation G hWidth).native O).native.execution.budget
    ((PRGNativeReductionConcrete.preparation G hWidth).source n message challenge) ≤ _
  rw [← PRGNativeReductionConcrete.timeBound_eq G hWidth O n]
  exact PRGNativeReduction.budget_le (PRGNativeReductionConcrete.preparation G hWidth) O n message challenge

def timeBound (n : Nat) : Nat :=
  9 * n + 102 * G.outputLength n + 90 + O.budget (2 * G.outputLength n + 1)

theorem timeBound_eq (n : Nat) (message : Bits (G.outputLength n)) :
    Machine.NativeSingleChallenge.Execution.timeBound (publicInput G n message) (G.outputLength n)
      (PRGNativeReductionConcrete.timeBound G O n) = timeBound G O n := by
  unfold Machine.NativeSingleChallenge.Execution.timeBound timeBound PRGNativeReductionConcrete.timeBound
  rw [publicInput_length]
  omega

noncomputable def game (n : Nat) (message : Bits (G.outputLength n)) (distribution : PMF (Bits (G.outputLength n))) : PMF Bool :=
  (eval (NativeSingleChallenge.step (distribution.map Bits.toList) (component O).procedure.code)
    (timeBound G O n) (NativeSingleChallenge.initial (publicInput G n message))).map
      (Machine.NativeSingleChallenge.Execution.result NativeSerializedObservation.decision)

include hWidth in
theorem run_game (n : Nat) (messages : G.Messages n) (side : Bool)
    (distribution : PMF (Bits (G.outputLength n))) (horizon : Nat) (hTime : timeBound G O n ≤ horizon) :
    (eval (NativeSingleChallenge.step (distribution.map Bits.toList) (component O).procedure.code)
      horizon (NativeSingleChallenge.initial (publicInput G n (G.message messages side)))).map
        (Machine.NativeSingleChallenge.Execution.result NativeSerializedObservation.decision) =
      distribution.bind (G.reduce messages side (PRGNativePad.observer O)) := by
  change (eval (NativeSingleChallenge.step (Machine.NativeSingleChallenge.Execution.wire distribution Bits.toList)
    (component O).procedure.code) horizon (NativeSingleChallenge.initial (publicInput G n (G.message messages side)))).map
    (Machine.NativeSingleChallenge.Execution.result NativeSerializedObservation.decision) = _
  rw [Machine.NativeSingleChallenge.Execution.run_game distribution Bits.toList _ (component O) (adapt G n (G.message messages side))
    (entry G O n (G.message messages side)) (G.outputLength n) (PRGNativeReductionConcrete.timeBound G O n)
    (fun _ _ => by simp) (fun challenge _ => consumer_budget G hWidth O n _ challenge)
    NativeSerializedObservation.decision
    (fun _ _ h => congrArg (fun current => current.getD false) h.2.2.1.1) horizon
    (by rw [timeBound_eq]; exact hTime)]
  congr 1
  funext challenge
  change ((component O).procedure.execution.semantics (adapt G n (G.message messages side) challenge)).map
    NativeSerializedObservation.decision = _
  change ((NativePadPipeline.PhysicalPreparation.link NativePadPacketPreparation.physical O).native.execution.semantics
    (adapt G n (G.message messages side) challenge)).map NativeSerializedObservation.decision = _
  rw [NativePadPipeline.PhysicalPreparation.observe]
  change (PMF.pure (PRGNativePad.input challenge (G.message messages side))).bind _ = _
  rw [PMF.pure_bind, PRGNativePad.cipher_input]
  rfl

include hWidth in
theorem game_eq (n : Nat) (messages : G.Messages n) (side : Bool)
    (distribution : PMF (Bits (G.outputLength n))) :
    game G O n (G.message messages side) distribution =
      distribution.bind (G.reduce messages side (PRGNativePad.observer O)) :=
  run_game G hWidth O n messages side distribution _ (Nat.le_refl _)

include hWidth in
theorem run_halted (n : Nat) (message : Bits (G.outputLength n))
    (distribution : PMF (Bits (G.outputLength n))) (horizon : Nat) (hTime : timeBound G O n ≤ horizon)
    (state : NativeSingleChallenge.Control)
    (h : state ∈ (eval (NativeSingleChallenge.step (distribution.map Bits.toList) (component O).procedure.code)
      horizon (NativeSingleChallenge.initial (publicInput G n message))).support) : NativeSingleChallenge.terminal state := by
  exact Machine.NativeSingleChallenge.Execution.run_halted distribution Bits.toList _ (component O) (adapt G n message)
    (entry G O n message) (G.outputLength n) (PRGNativeReductionConcrete.timeBound G O n)
    (fun _ _ => by simp) (fun challenge _ => consumer_budget G hWidth O n message challenge)
    horizon (by rw [timeBound_eq]; exact hTime) state h

include hWidth in
theorem exactly_one_query (n : Nat) (message : Bits (G.outputLength n))
    (distribution : PMF (Bits (G.outputLength n))) (horizon : Nat) (hTime : timeBound G O n ≤ horizon)
    (frame : NativeSingleChallenge.Control × Nat)
    (h : frame ∈ (eval (OneUseCounter.countedStep
      (NativeSingleChallenge.step (distribution.map Bits.toList) (component O).procedure.code) NativeSingleChallenge.queryEvent)
      horizon (NativeSingleChallenge.initial (publicInput G n message), 0)).support) : frame.2 = 1 := by
  exact Machine.NativeSingleChallenge.Execution.run_exactly_one_query distribution Bits.toList _ (component O) (adapt G n message)
    (entry G O n message) (G.outputLength n) (PRGNativeReductionConcrete.timeBound G O n)
    (fun _ _ => by simp) (fun challenge _ => consumer_budget G hWidth O n message challenge)
    horizon (by rw [timeBound_eq]; exact hTime) frame h

include hWidth in
/-- The encryption bound now uses complete query/loading/native executions
on both the real and ideal external challenge laws. -/
theorem advantage_le {EncryptionInput : Type*} (I : PRGNativePipeline.Implementation G EncryptionInput)
    (n : Nat) (messages : G.Messages n) :
    probabilityGap (eventProb (PRGNativePipeline.game I O n messages.1) (· = true))
      (eventProb (PRGNativePipeline.game I O n messages.2) (· = true)) ≤
      probabilityGap (eventProb (game G O n (G.message messages false) (G.real n)) (· = true))
        (eventProb (game G O n (G.message messages false) (G.ideal n)) (· = true)) +
      probabilityGap (eventProb (game G O n (G.message messages true) (G.real n)) (· = true))
        (eventProb (game G O n (G.message messages true) (G.ideal n)) (· = true)) := by
  rw [game_eq G hWidth O n messages false, game_eq G hWidth O n messages false,
    game_eq G hWidth O n messages true, game_eq G hWidth O n messages true]
  exact PRGNativePipeline.advantage_le I O n messages

include hWidth in
theorem time_polynomial : PolynomiallyBounded (timeBound G O) :=
  ((((PolynomiallyBounded.const 9).mul PolynomiallyBounded.id).add
    ((PolynomiallyBounded.const 102).mul hWidth)).add (PolynomiallyBounded.const 90)).add
    (O.budget_profile_polynomial (((PolynomiallyBounded.const 2).mul hWidth).add (PolynomiallyBounded.const 1)))

end Foundation.Symmetric.PRGNativeQueryExecution
