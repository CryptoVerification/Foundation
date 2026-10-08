import Foundation.Constructions.Symmetric.PRGNativeReduction
import Foundation.Crypto.Semantics.Machine.NativePadPacketPreparation

/-! Instantiate the native reduction constructor with the actual 62-command
packet preparer. Its code is independent of the generator, parameter,
messages and challenge bits. Only polynomial output length is a premise;
no implementation certificate for packet preparation is left to the user. -/
namespace Foundation.Symmetric.PRGNativeReductionConcrete
open Machine Foundation.Probability TimedExecution
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

noncomputable def preparation (G : Generator) (hWidth : PolynomiallyBounded G.outputLength) :
    PRGNativeReduction.Preparation G NativePadPacketPreparation.Input where
  native := NativePadPacketPreparation.physical
  source := fun n message challenge => (n, PRGNativePad.input challenge message)
  entry := fun _ _ _ => rfl
  semantics := fun _ _ _ => rfl
  width := fun _ _ _ => by simp [NativePadPacketPreparation.physical, PRGNativePad.input]
  preparationBound := fun n => 4 * n + 30 * G.outputLength n + 25
  bounded := fun n message challenge => by
    change NativePadPacketPreparation.timeBound (n, PRGNativePad.input challenge message) ≤ _
    simp [NativePadPacketPreparation.timeBound, PRGNativePad.input]
  polynomial := (((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add
    ((PolynomiallyBounded.const 30).mul hWidth)).add (PolynomiallyBounded.const 25)

def fixedCode (O : PolynomialObserver) : Program :=
  NativePadPacketPreparation.fixedCode.followedBy (NativePadObservation.fixedCode O)

theorem fixedCode_eq (G : Generator) (hWidth : PolynomiallyBounded G.outputLength) (O : PolynomialObserver) :
    fixedCode O = PRGNativeReduction.fixedCode (preparation G hWidth) O := rfl

theorem code_length (O : PolynomialObserver) : (fixedCode O).length = O.code.length + 157 := by
  simp only [fixedCode, Program.followedBy, List.length_append, Program.asSubroutine_length, List.length_singleton]
  rw [NativePadPacketPreparation.code_length, NativePadObservation.fixedCode_eq, NativePadObservation.code_length]
  omega

def timeBound (G : Generator) (O : PolynomialObserver) (n : Nat) : Nat :=
  4 * n + 84 * G.outputLength n + 66 + O.budget (2 * G.outputLength n + 1)

theorem timeBound_eq (G : Generator) (hWidth : PolynomiallyBounded G.outputLength) (O : PolynomialObserver) (n : Nat) :
    PRGNativeReduction.timeBound (preparation G hWidth) O n = timeBound G O n := by
  change (4 * n + 30 * G.outputLength n + 25) + NativePadObservation.timeBound O (G.outputLength n) + 1 = _
  unfold NativePadObservation.timeBound timeBound
  omega

/-- Direct execution of one concrete fixed finite program computes each
PRG reduction from the public parameter, public message and received challenge. -/
theorem run_reduce_eq (G : Generator) (hWidth : PolynomiallyBounded G.outputLength) (O : PolynomialObserver)
    (n : Nat) (messages : G.Messages n) (side : Bool) (challenge : Bits (G.outputLength n))
    (horizon : Nat) (hTime : timeBound G O n ≤ horizon) :
    (runToBoundary (stepPMF (fixedCode O)) Configuration.halted horizon
      (Configuration.initial (PRGNativeReduction.rawInput n (G.message messages side) challenge))).map
        (fun result => NativeSerializedObservation.decision result.1) =
      G.reduce messages side (PRGNativePad.observer O) challenge :=
  PRGNativeReduction.run_reduce_eq (preparation G hWidth) O n messages side challenge horizon
    (by rw [timeBound_eq]; exact hTime)

theorem time_polynomial (G : Generator) (hWidth : PolynomiallyBounded G.outputLength) (O : PolynomialObserver) :
    PolynomiallyBounded (timeBound G O) :=
  ((((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add
    ((PolynomiallyBounded.const 84).mul hWidth)).add (PolynomiallyBounded.const 66)).add
    (O.budget_profile_polynomial (((PolynomiallyBounded.const 2).mul hWidth).add (PolynomiallyBounded.const 1)))

def bitBound (G : Generator) (O : PolynomialObserver) (n : Nat) : Nat :=
  StructuredCodeEncoding.bound (fixedCode O) 0 (n + 4 * G.outputLength n + 5) (timeBound G O n)

theorem space_polynomial (G : Generator) (hWidth : PolynomiallyBounded G.outputLength) (O : PolynomialObserver) :
    PolynomiallyBounded (bitBound G O) :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    ((PolynomiallyBounded.id.add ((PolynomiallyBounded.const 4).mul hWidth)).add (PolynomiallyBounded.const 5))
    (time_polynomial G hWidth O)

theorem storage_peak (G : Generator) (O : PolynomialObserver)
    (n : Nat) (message challenge : Bits (G.outputLength n)) (elapsed : Nat)
    (hElapsed : elapsed ≤ timeBound G O n) (state : Configuration)
    (h : state ∈ (eval (stepPMF (fixedCode O)) elapsed
      (Configuration.initial (PRGNativeReduction.rawInput n message challenge))).support) :
    (StructuredCodeEncoding.completeEncoding.encode (fixedCode O, state)).length ≤ bitBound G O n :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state h).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (PRGNativeReduction.initial_cells n message challenge) (Nat.le_refl _))

/-- The adversary is the direct execution of the fixed native code, not
an abstract XOR function with an unproved execution correspondence. -/
noncomputable def adversary (G : Generator) (O : PolynomialObserver) (n : Nat)
    (messages : G.Messages n) (side : Bool) : G.Observer n := fun challenge =>
  (runToBoundary (stepPMF (fixedCode O)) Configuration.halted (timeBound G O n)
    (Configuration.initial (PRGNativeReduction.rawInput n (G.message messages side) challenge))).map
      (fun result => NativeSerializedObservation.decision result.1)

theorem adversary_eq (G : Generator) (hWidth : PolynomiallyBounded G.outputLength) (O : PolynomialObserver)
    (n : Nat) (messages : G.Messages n) (side : Bool) :
    adversary G O n messages side = G.reduce messages side (PRGNativePad.observer O) := by
  funext challenge
  exact run_reduce_eq G hWidth O n messages side challenge (timeBound G O n) (Nat.le_refl _)

theorem advantage_le {G : Generator} {Input : Type*} (I : PRGNativePipeline.Implementation G Input)
    (hWidth : PolynomiallyBounded G.outputLength) (O : PolynomialObserver) (n : Nat) (messages : G.Messages n) :
    probabilityGap (eventProb (PRGNativePipeline.game I O n messages.1) (· = true))
      (eventProb (PRGNativePipeline.game I O n messages.2) (· = true)) ≤
        G.prgGoal.advantage n messages (adversary G O n messages false) +
        G.prgGoal.advantage n messages (adversary G O n messages true) := by
  rw [adversary_eq G hWidth, adversary_eq G hWidth]
  exact PRGNativePipeline.advantage_le I O n messages

theorem advantage_le_sum {G : Generator} {Input : Type*} (I : PRGNativePipeline.Implementation G Input)
    (hWidth : PolynomiallyBounded G.outputLength) (O : PolynomialObserver) (n : Nat) (messages : G.Messages n)
    (leftBound rightBound : ℝ≥0∞)
    (hLeft : G.prgGoal.advantage n messages (adversary G O n messages false) ≤ leftBound)
    (hRight : G.prgGoal.advantage n messages (adversary G O n messages true) ≤ rightBound) :
    probabilityGap (eventProb (PRGNativePipeline.game I O n messages.1) (· = true))
      (eventProb (PRGNativePipeline.game I O n messages.2) (· = true)) ≤ leftBound + rightBound :=
  (advantage_le I hWidth O n messages).trans (add_le_add hLeft hRight)

end Foundation.Symmetric.PRGNativeReductionConcrete
