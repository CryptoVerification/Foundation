import Foundation.Constructions.Symmetric.OneTimePad
import Foundation.Crypto.Semantics.Probability.Facts

/-! Exact uniform bitstring decomposition into an independent prefix and
last bit, including the empty prefix. These are distribution laws and do not
assert constant-time native operations on whole strings. -/
namespace Foundation.Symmetric.Bits
open Foundation.Probability

theorem uniform_snoc (width : Nat) :
    uniform (Bits (width + 1)) = sampleBit.bind
      (fun bit => (uniform (Bits width)).map (fun headBits => Fin.snoc headBits bit)) := by
  have h := uniform_map_equiv (Fin.snocEquiv (fun _ : Fin (width + 1) => Bool))
  rw [← uniform_pair, PMF.map_bind] at h
  simp only [PMF.map_comp, Function.comp_def] at h
  exact h.symm

theorem uniform_last (width : Nat) :
    (uniform (Bits (width + 1))).map (fun bits => bits (Fin.last width)) = sampleBit := by
  rw [uniform_snoc, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, Fin.snoc_last]
  change sampleBit.bind (fun bit => (uniform (Bits width)).map (Function.const (Bits width) bit)) = sampleBit
  simp only [PMF.map_const, PMF.bind_pure]

end Foundation.Symmetric.Bits
