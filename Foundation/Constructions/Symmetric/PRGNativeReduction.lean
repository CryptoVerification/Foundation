import Foundation.Constructions.Symmetric.PRGNativePipeline

/-! Charged native PRG reductions with public message/challenge preparation.
The code constructor accepts a certified native packet preparer. Its entry
contains only the public parameter, message and external PRG challenge.
The challenge is already received here: oracle query/receipt costs are a
separate interaction contract. Preparing the native packet is charged. -/
namespace Foundation.Symmetric.PRGNativeReduction
open Machine Foundation.Probability TimedExecution
open scoped ENNReal
universe u
set_option backward.isDefEq.respectTransparency false

def rawInput (n : Nat) {width : Nat} (message challenge : Bits width) : List Bool :=
  List.replicate n true ++ false ::
    (FiniteBitEncoding.delimit message.toList ++ FiniteBitEncoding.delimit challenge.toList)

/-- One preparer code handles all parameters, messages and challenges.
Its output law and both inherited tapes must be certified by native execution. -/
structure Preparation (G : Generator) (Input : Type u) where
  native : NativePadPipeline.PhysicalPreparation Input
  source : ∀ n, Bits (G.outputLength n) → Bits (G.outputLength n) → Input
  entry : ∀ n message challenge, native.component.procedure.execution.entry (source n message challenge) =
    Configuration.initial (rawInput n message challenge)
  semantics : ∀ n message challenge, native.component.procedure.execution.semantics (source n message challenge) =
    PMF.pure (PRGNativePad.input challenge message)
  width : ∀ n message challenge, native.width (source n message challenge) = G.outputLength n
  preparationBound : Nat → Nat
  bounded : ∀ n message challenge,
    native.component.procedure.execution.budget (source n message challenge) ≤ preparationBound n
  polynomial : PolynomiallyBounded preparationBound

variable {G : Generator} {Input : Type u} (P : Preparation G Input) (O : PolynomialObserver)

def fixedCode : Program := NativePadPipeline.PhysicalPreparation.fixedCode P.native O

def timeBound (n : Nat) : Nat := P.preparationBound n + NativePadObservation.timeBound O (G.outputLength n) + 1

theorem code_length : (fixedCode P O).length = P.native.component.procedure.code.length + O.code.length + 95 :=
  NativePadPipeline.PhysicalPreparation.code_length P.native O

theorem budget_le (n : Nat) (message challenge : Bits (G.outputLength n)) :
    (NativePadPipeline.PhysicalPreparation.link P.native O).native.execution.budget (P.source n message challenge) ≤ timeBound P O n := by
  rw [NativePadPipeline.PhysicalPreparation.budget]
  unfold NativePadPipeline.PhysicalPreparation.timeBound timeBound
  rw [P.width]
  exact Nat.add_le_add_right (Nat.add_le_add_right (P.bounded n message challenge) _) _

noncomputable def decision (n : Nat) (message challenge : Bits (G.outputLength n)) : PMF Bool :=
  (NativePadPipeline.PhysicalPreparation.costed P.native O (P.source n message challenge)).map
    (fun result => NativeSerializedObservation.decision result.1)

theorem decision_eq (n : Nat) (message challenge : Bits (G.outputLength n)) :
    decision P O n message challenge = O.observe (FiniteBitEncoding.delimit (Bits.xor message challenge).toList) := by
  unfold decision
  rw [NativePadPipeline.PhysicalPreparation.costed_observe, P.semantics, PMF.pure_bind, PRGNativePad.cipher_input]

/-- Both branches use the same finite native code. The selected public
message is data at entry, not code specialization or secret advice. -/
theorem reduce_eq (n : Nat) (messages : G.Messages n) (side : Bool) :
    decision P O n (G.message messages side) = G.reduce messages side (PRGNativePad.observer O) := by
  funext challenge
  exact decision_eq P O n (G.message messages side) challenge

theorem run_reduce_eq (n : Nat) (messages : G.Messages n) (side : Bool)
    (challenge : Bits (G.outputLength n)) (horizon : Nat) (hTime : timeBound P O n ≤ horizon) :
    (runToBoundary (stepPMF (fixedCode P O)) Configuration.halted horizon
      (Configuration.initial (rawInput n (G.message messages side) challenge))).map
        (fun result => NativeSerializedObservation.decision result.1) =
      G.reduce messages side (PRGNativePad.observer O) challenge := by
  unfold fixedCode
  rw [← P.entry n (G.message messages side) challenge,
    NativePadPipeline.PhysicalPreparation.costed_horizon P.native O (P.source n (G.message messages side) challenge) horizon
      ((budget_le P O n _ challenge).trans hTime)]
  exact decision_eq P O n (G.message messages side) challenge

theorem time_polynomial (hWidth : PolynomiallyBounded G.outputLength) :
    PolynomiallyBounded (timeBound P O) :=
  (P.polynomial.add (PRGNativePad.time_polynomial G O hWidth)).add (PolynomiallyBounded.const 1)

theorem rawInput_length (n : Nat) (message challenge : Bits (G.outputLength n)) :
    (rawInput n message challenge).length = n + 4 * G.outputLength n + 3 := by
  simp [rawInput, FiniteBitEncoding.delimit_length]
  omega

theorem initial_cells (n : Nat) (message challenge : Bits (G.outputLength n)) :
    (Configuration.initial (rawInput n message challenge)).tapeCells ≤ n + 4 * G.outputLength n + 5 := by
  have h : ∀ raw : List Bool, (Configuration.initial raw).tapeCells ≤ raw.length + 2 := by
    intro raw
    cases raw <;> simp [Configuration.initial, Tape.ofBits, Configuration.tapeCells, Tape.cells] <;> omega
  simpa only [rawInput_length] using h (rawInput n message challenge)

def bitBound (n : Nat) : Nat := StructuredCodeEncoding.bound (fixedCode P O) 0
  (n + 4 * G.outputLength n + 5) (timeBound P O n)

theorem space_polynomial (hWidth : PolynomiallyBounded G.outputLength) :
    PolynomiallyBounded (bitBound P O) :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    ((PolynomiallyBounded.id.add ((PolynomiallyBounded.const 4).mul hWidth)).add (PolynomiallyBounded.const 5))
    (time_polynomial P O hWidth)

theorem storage_peak (n : Nat) (message challenge : Bits (G.outputLength n)) (elapsed : Nat)
    (hElapsed : elapsed ≤ timeBound P O n) (state : Configuration)
    (h : state ∈ (eval (stepPMF (fixedCode P O)) elapsed (Configuration.initial (rawInput n message challenge))).support) :
    (StructuredCodeEncoding.completeEncoding.encode (fixedCode P O, state)).length ≤ bitBound P O n :=
  (StructuredCodeEncoding.peak _ _ elapsed hElapsed _ state h).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (initial_cells n message challenge) (Nat.le_refl _))

/-- The encryption advantage is bounded by the advantages of these actual
native continuations, including their certified packet preparation. -/
theorem advantage_le {EncryptionInput : Type*} (I : PRGNativePipeline.Implementation G EncryptionInput) (n : Nat) (messages : G.Messages n) :
    probabilityGap (eventProb (PRGNativePipeline.game I O n messages.1) (· = true))
      (eventProb (PRGNativePipeline.game I O n messages.2) (· = true)) ≤
        probabilityGap (eventProb ((G.real n).bind (decision P O n (G.message messages false))) (· = true))
          (eventProb ((G.ideal n).bind (decision P O n (G.message messages false))) (· = true)) +
        probabilityGap (eventProb ((G.real n).bind (decision P O n (G.message messages true))) (· = true))
          (eventProb ((G.ideal n).bind (decision P O n (G.message messages true))) (· = true)) := by
  rw [reduce_eq, reduce_eq]
  exact PRGNativePipeline.advantage_le I O n messages

end Foundation.Symmetric.PRGNativeReduction
