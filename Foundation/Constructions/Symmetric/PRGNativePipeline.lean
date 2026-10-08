import Foundation.Constructions.Symmetric.PRGNativePad
import Foundation.Crypto.Semantics.Machine.NativePadPhysicalPreparation

/-! A uniform native implementation interface for PRG encryption.
A single fixed preparation code receives only the public parameter and
plaintext. It must certify seed sampling, PRG evaluation, packet preparation
and cleanup by its actual output law, cell-equivalent physical handoff and time bound.
This interface does not manufacture a secure PRG or its implementation. -/
namespace Foundation.Symmetric.PRGNativePipeline
open Machine Foundation.Probability TimedExecution
open scoped ENNReal
universe u
set_option backward.isDefEq.respectTransparency false

/-- Unary parameter followed by a delimited message. No precomputed pad,
random seed, private advice or preallocated workspace is supplied. -/
def rawInput (n : Nat) {width : Nat} (message : Bits width) : List Bool :=
  List.replicate n true ++ false :: FiniteBitEncoding.delimit message.toList

structure Implementation (G : Generator) (Input : Type u) where
  preparation : NativePadPipeline.PhysicalPreparation Input
  source : ∀ n, Bits (G.outputLength n) → Input
  entry : ∀ n message, preparation.component.procedure.execution.entry (source n message) =
    Configuration.initial (rawInput n message)
  semantics : ∀ n message, preparation.component.procedure.execution.semantics (source n message) =
    (G.real n).map (fun pad => PRGNativePad.input pad message)
  width : ∀ n message, preparation.width (source n message) = G.outputLength n
  preparationBound : Nat → Nat
  bounded : ∀ n message,
    preparation.component.procedure.execution.budget (source n message) ≤ preparationBound n
  polynomial : PolynomiallyBounded preparationBound

variable {G : Generator} {Input : Type u} (I : Implementation G Input) (O : PolynomialObserver)

def fixedCode : Program := NativePadPipeline.PhysicalPreparation.fixedCode I.preparation O

def timeBound (n : Nat) : Nat := I.preparationBound n + NativePadObservation.timeBound O (G.outputLength n) + 1

theorem budget_le (n : Nat) (message : Bits (G.outputLength n)) :
    (NativePadPipeline.PhysicalPreparation.link I.preparation O).native.execution.budget (I.source n message) ≤ timeBound I O n := by
  rw [NativePadPipeline.PhysicalPreparation.budget]
  unfold NativePadPipeline.PhysicalPreparation.timeBound timeBound
  rw [I.width]
  exact Nat.add_le_add_right (Nat.add_le_add_right (I.bounded n message) _) _

noncomputable def game (n : Nat) (message : Bits (G.outputLength n)) : PMF Bool :=
  (NativePadPipeline.PhysicalPreparation.costed I.preparation O (I.source n message)).map
    (fun result => NativeSerializedObservation.decision result.1)

theorem game_eq (n : Nat) (message : Bits (G.outputLength n)) :
    game I O n message = PRGNativePad.game G n O message := by
  unfold game
  rw [NativePadPipeline.PhysicalPreparation.costed_observe, I.semantics, PMF.bind_map]
  unfold PRGNativePad.game
  congr 1
  funext pad
  rw [NativePadObservation.costed_observe]
  rfl

/-- Raw execution starts with public parameter and message only; generation
and preparation are executed inside the same fixed code as encryption. -/
theorem run_game_eq (n : Nat) (message : Bits (G.outputLength n)) (horizon : Nat)
    (hTime : timeBound I O n ≤ horizon) :
    (runToBoundary (stepPMF (fixedCode I O)) Configuration.halted horizon
      (Configuration.initial (rawInput n message))).map
        (fun result => NativeSerializedObservation.decision result.1) = PRGNativePad.game G n O message := by
  unfold fixedCode
  rw [← I.entry n message,
    NativePadPipeline.PhysicalPreparation.costed_horizon I.preparation O (I.source n message) horizon
      ((budget_le I O n message).trans hTime)]
  exact game_eq I O n message

theorem advantage_le (n : Nat) (messages : G.Messages n) :
    probabilityGap (eventProb (game I O n messages.1) (· = true))
      (eventProb (game I O n messages.2) (· = true)) ≤
        G.prgGoal.advantage n messages (G.reduce messages false (PRGNativePad.observer O)) +
        G.prgGoal.advantage n messages (G.reduce messages true (PRGNativePad.observer O)) := by
  rw [game_eq, game_eq]
  exact PRGNativePad.advantage_le G n O messages

theorem time_polynomial (hWidth : PolynomiallyBounded G.outputLength) :
    PolynomiallyBounded (timeBound I O) :=
  (I.polynomial.add (PRGNativePad.time_polynomial G O hWidth)).add (PolynomiallyBounded.const 1)

theorem rawInput_length (n : Nat) (message : Bits (G.outputLength n)) :
    (rawInput n message).length = n + 2 * G.outputLength n + 2 := by
  simp [rawInput, FiniteBitEncoding.delimit_length]
  omega

theorem initial_cells (n : Nat) (message : Bits (G.outputLength n)) :
    (Configuration.initial (rawInput n message)).tapeCells ≤ n + 2 * G.outputLength n + 4 := by
  have h : ∀ raw : List Bool, (Configuration.initial raw).tapeCells ≤ raw.length + 2 := by
    intro raw
    cases raw <;> simp [Configuration.initial, Tape.ofBits, Configuration.tapeCells, Tape.cells] <;> omega
  simpa only [rawInput_length] using h (rawInput n message)

def bitBound (n : Nat) : Nat := StructuredCodeEncoding.bound (fixedCode I O) 0
  (n + 2 * G.outputLength n + 4) (timeBound I O n)

theorem space_polynomial (hWidth : PolynomiallyBounded G.outputLength) :
    PolynomiallyBounded (bitBound I O) :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    ((PolynomiallyBounded.id.add ((PolynomiallyBounded.const 2).mul hWidth)).add (PolynomiallyBounded.const 4))
    (time_polynomial I O hWidth)

theorem storage_peak (n : Nat) (message : Bits (G.outputLength n)) (elapsed : Nat)
    (hElapsed : elapsed ≤ timeBound I O n) (state : Configuration)
    (h : state ∈ (eval (stepPMF (fixedCode I O)) elapsed (Configuration.initial (rawInput n message))).support) :
    (StructuredCodeEncoding.completeEncoding.encode (fixedCode I O, state)).length ≤ bitBound I O n :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state h).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (initial_cells n message) (Nat.le_refl _))

end Foundation.Symmetric.PRGNativePipeline
