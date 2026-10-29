import Foundation.Crypto.Logic.Polygraph.NativePreparedExperiment
import Foundation.Crypto.Semantics.Probability.ClassicalBitDecisionCoupling

/-! Statistical diagrams for the native-written decision bit. Each local
comparison supplies an explicit Fin 256 coupling with checked marginals.
This diagram observes the decision only; it does not identify private states
or assert coherence of arbitrary endpoint couplings. -/
namespace CryptoLogic.Polygraph.Experiment.NativePrepared.Decision
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped ENNReal

def read (output : Output) : Bool := (output.bind (fun bits => bits[1]?)).getD false

theorem read_accepted (output : Output) : read output = true ↔ Machine.NativePreparedKeyDecision.acceptedPacket output := by
  unfold read Machine.NativePreparedKeyDecision.acceptedPacket
  cases output.bind (fun bits => bits[1]?) <;> simp

noncomputable def nativeLaw (v : OrderedGridVertex 32) (message : Bool) : PMF Bool :=
  (Machine.evalWithin Machine.NativePreparedKeyDecision.code
    (Machine.NativePreparedKeyDecision.rawInput v message) 930).map read

noncomputable def game (v : OrderedGridVertex 32) (message : Bool) : Observed :=
  ⟨Bool, .sample (nativeLaw v message), (· = true)⟩

theorem nativeLaw_eq (v : OrderedGridVertex 32) (message : Bool) :
    nativeLaw v message = (tableEightBitLaw v message).map keyPairTest := by
  unfold nativeLaw
  rw [Machine.NativePreparedKeyDecision.evalWithin_law, PMF.map_comp]
  have h : (read ∘ (fun result : Fin 5 × Bool => some [!result.2, keyPairTest result])) = keyPairTest := by
    funext result
    rfl
  exact congrArg (fun f => (tableEightBitLaw v message).map f) h

theorem native_realization (v : OrderedGridVertex 32) (message : Bool) :
    (game v message).program.eval =
      (Machine.evalWithin bounded.program (Machine.NativePreparedKeyDecision.rawInput v message)
        (bounded.budget 39)).map read := rfl

theorem probability_native (v : OrderedGridVertex 32) (message : Bool) :
    (game v message).probability =
      eventProb (Machine.evalWithin Machine.NativePreparedKeyDecision.code
        (Machine.NativePreparedKeyDecision.rawInput v message) 930) Machine.NativePreparedKeyDecision.acceptedPacket := by
  change eventProb (nativeLaw v message) (· = true) = _
  unfold nativeLaw
  rw [eventProb_map]
  have h : (fun output => read output = true) = Machine.NativePreparedKeyDecision.acceptedPacket :=
    funext (fun output => propext (read_accepted output))
  rw [h]

theorem marginal (v : OrderedGridVertex 32) (message : Bool) :
    (uniform (Fin 256)).map (FiniteBooleanThreshold.bit (decisionCount v message)) = (game v message).program.eval := by
  change FiniteBooleanThreshold.law (decisionCount v message) = nativeLaw v message
  rw [← decision_threshold_marginal, nativeLaw_eq]

noncomputable def coupledHop (u v : OrderedGridVertex 32) (message : Bool) :
    Hop (game u message) (game v message) (eventProb (uniform (Fin 256)) (decisionBad u v message)) :=
  .coupling (uniform (Fin 256)) (FiniteBooleanThreshold.bit (decisionCount u message))
    (FiniteBooleanThreshold.bit (decisionCount v message)) (marginal u message) (marginal v message)
    (decisionBad u v message) (by
      intro draw _ good
      change FiniteBooleanThreshold.bit (decisionCount u message) draw = true ↔
        FiniteBooleanThreshold.bit (decisionCount v message) draw = true
      have he : FiniteBooleanThreshold.bit (decisionCount u message) draw = FiniteBooleanThreshold.bit (decisionCount v message) draw :=
        not_ne_iff.mp good
      rw [he])

noncomputable def edgeHop (u v : OrderedGridVertex 32)
    (edge : faceEdge (orderedGridComplex 32) u v) (message : Bool) :
    Hop (game u message) (game v message) (37 / 128 : ℝ≥0∞) :=
  .weaken (coupledHop u v message) (decisionBad_edge_bound u v edge message)

noncomputable def edgeDiagram (u v : OrderedGridVertex 32)
    (edge : faceEdge (orderedGridComplex 32) u v) (message : Bool) :=
  Statistical.diagram (edgeHop u v edge message)

theorem edge_sound (u v : OrderedGridVertex 32)
    (edge : faceEdge (orderedGridComplex 32) u v) (message : Bool) :
    probabilityGap (game u message).probability (game v message).probability ≤ (37 / 128 : ℝ≥0∞) :=
  Statistical.sound (edgeHop u v edge message)

theorem native_edge_sound (u v : OrderedGridVertex 32)
    (edge : faceEdge (orderedGridComplex 32) u v) (message : Bool) :
    probabilityGap
      (eventProb (Machine.evalWithin Machine.NativePreparedKeyDecision.code
        (Machine.NativePreparedKeyDecision.rawInput u message) 930) Machine.NativePreparedKeyDecision.acceptedPacket)
      (eventProb (Machine.evalWithin Machine.NativePreparedKeyDecision.code
        (Machine.NativePreparedKeyDecision.rawInput v message) 930) Machine.NativePreparedKeyDecision.acceptedPacket) ≤
          (37 / 128 : ℝ≥0∞) := by
  rw [← probability_native u message, ← probability_native v message]
  exact edge_sound u v edge message

theorem sharp_coupling_error (message : Bool) :
    eventProb (uniform (Fin 256)) (decisionBad (sharpTableChain 0) (sharpTableChain 2) message) =
      (37 / 128 : ℝ≥0∞) := decisionBad_sharp message

noncomputable def chainHop (n : ℕ) (vertices : Fin (n + 1) → OrderedGridVertex 32)
    (edges : ∀ i : Fin n, faceEdge (orderedGridComplex 32) (vertices i.castSucc) (vertices i.succ))
    (message : Bool) :
    Hop (game (vertices 0) message) (game (vertices (Fin.last n)) message)
      ((n : ℝ≥0∞) * (37 / 128)) := by
  induction n with
  | zero =>
    have h : Hop (game (vertices 0) message) (game (vertices 0) message) 0 := .exact (.refl _) (· = true)
    simpa only [Nat.cast_zero, zero_mul, Fin.last_zero] using h
  | succ n ih =>
    have first := edgeHop (vertices 0) (vertices (Fin.succ 0)) (edges 0) message
    have tail := ih (fun i => vertices i.succ) (fun i => edges i.succ)
    have combined := Hop.comp first tail
    have hError : ((n + 1 : ℕ) : ℝ≥0∞) * (37 / 128) = 37 / 128 + (n : ℝ≥0∞) * (37 / 128) := by
      simp [Nat.cast_add, add_mul, add_comm]
    rw [hError]
    exact combined

noncomputable def chainDiagram (n : ℕ) (vertices : Fin (n + 1) → OrderedGridVertex 32)
    (edges : ∀ i : Fin n, faceEdge (orderedGridComplex 32) (vertices i.castSucc) (vertices i.succ))
    (message : Bool) := Statistical.diagram (chainHop n vertices edges message)

theorem chain_sound (n : ℕ) (vertices : Fin (n + 1) → OrderedGridVertex 32)
    (edges : ∀ i : Fin n, faceEdge (orderedGridComplex 32) (vertices i.castSucc) (vertices i.succ))
    (message : Bool) :
    probabilityGap (game (vertices 0) message).probability (game (vertices (Fin.last n)) message).probability ≤
      (n : ℝ≥0∞) * (37 / 128) := Statistical.sound (chainHop n vertices edges message)

theorem native_chain_sound (n : ℕ) (vertices : Fin (n + 1) → OrderedGridVertex 32)
    (edges : ∀ i : Fin n, faceEdge (orderedGridComplex 32) (vertices i.castSucc) (vertices i.succ))
    (message : Bool) :
    probabilityGap
      (eventProb (Machine.evalWithin Machine.NativePreparedKeyDecision.code
        (Machine.NativePreparedKeyDecision.rawInput (vertices 0) message) 930) Machine.NativePreparedKeyDecision.acceptedPacket)
      (eventProb (Machine.evalWithin Machine.NativePreparedKeyDecision.code
        (Machine.NativePreparedKeyDecision.rawInput (vertices (Fin.last n)) message) 930) Machine.NativePreparedKeyDecision.acceptedPacket) ≤
      (n : ℝ≥0∞) * (37 / 128) := by
  rw [← probability_native, ← probability_native]
  exact chain_sound n vertices edges message

end CryptoLogic.Polygraph.Experiment.NativePrepared.Decision
