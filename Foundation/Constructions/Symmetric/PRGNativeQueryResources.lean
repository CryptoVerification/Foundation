import Foundation.Constructions.Symmetric.PRGNativeQueryExecution
import Foundation.Crypto.Semantics.Machine.NativeSingleChallengeResources

/-! Whole-prefix memory for the concrete PRG query reduction, including
query receipt, loader buffers, padded tapes and all executable code blocks.
No canonical-entry storage bound is substituted for the actual runtime. -/
namespace Foundation.Symmetric.PRGNativeQueryExecution
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
variable (G : Generator) (O : PolynomialObserver)

def bitBound (n : Nat) : Nat :=
  NativeSingleChallenge.Resources.bitBound (PRGNativeReductionConcrete.fixedCode O) (G.outputLength n)
    0 (n + 2 * G.outputLength n + 4) (timeBound G O n)

theorem initial_cells (n : Nat) (message : Bits (G.outputLength n)) :
    (Configuration.initial (publicInput G n message)).tapeCells ≤ n + 2 * G.outputLength n + 4 := by
  have h := Tape.cells_ofBits_le (publicInput G n message)
  have hLength := publicInput_length G n message
  change (Tape.ofBits (publicInput G n message)).cells + 1 ≤ _
  omega

theorem storage_peak (n : Nat) (message : Bits (G.outputLength n))
    (distribution : PMF (Bits (G.outputLength n))) (elapsed : Nat) (hElapsed : elapsed ≤ timeBound G O n)
    (state : NativeSingleChallenge.Control)
    (h : state ∈ (eval (NativeSingleChallenge.step (distribution.map Bits.toList) (component O).procedure.code)
      elapsed (NativeSingleChallenge.initial (publicInput G n message))).support) :
    (NativeSingleChallenge.Resources.completeEncoding.encode ((component O).procedure.code, state)).length ≤ bitBound G O n := by
  have hResponse : ∀ response ∈ (distribution.map Bits.toList).support, response.length ≤ G.outputLength n := by
    intro response hs
    rw [PMF.mem_support_map_iff] at hs
    obtain ⟨reply, _, rfl⟩ := hs
    simp
  exact (NativeSingleChallenge.Resources.peak (distribution.map Bits.toList) (component O).procedure.code
    (G.outputLength n) hResponse (timeBound G O n) elapsed hElapsed (publicInput G n message) state h).trans
    (NativeSingleChallenge.Resources.bitBound_mono (component O).procedure.code
      (Nat.le_refl _) (Nat.le_refl _) (initial_cells G n message) (Nat.le_refl _))

theorem space_polynomial (hWidth : PolynomiallyBounded G.outputLength) : PolynomiallyBounded (bitBound G O) :=
  NativeSingleChallenge.Resources.bitBound_polynomial (component O).procedure.code hWidth (PolynomiallyBounded.const 0)
    ((PolynomiallyBounded.id.add ((PolynomiallyBounded.const 2).mul hWidth)).add (PolynomiallyBounded.const 4))
    (time_polynomial G hWidth O)

end Foundation.Symmetric.PRGNativeQueryExecution
