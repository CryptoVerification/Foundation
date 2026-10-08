import Foundation.Constructions.Symmetric.PRGResource
import Foundation.Crypto.Semantics.Machine.ControlStorage

/-! Reuse native control-and-tape encoding bounds for the PRG encryption
attack class. The finite program and all public-message/ciphertext input
are retained. Challenger generator evaluation and masking preprocessing
are outside this native-attack bound. -/
namespace Foundation.Symmetric.Generator
open Foundation.Probability Machine CryptoLogic
set_option backward.isDefEq.respectTransparency false
variable (G : Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (A : AdversaryFamily G.encryptionGoal F)
    (W : G.NativeWitness time F A)

def nativeStorageBound (n : Nat) : Nat :=
  W.program.storageBound 0 (n + 5 * G.outputLength n + 5) (time n)

theorem native_initial_cells (n : Nat) (challenge : Bits (G.outputLength n)) :
    (Machine.Configuration.initial (G.header n (F n) ++ challenge.toList)).tapeCells ≤
      n + 5 * G.outputLength n + 5 := by
  have hi := Tape.cells_ofBits_le (G.header n (F n) ++ challenge.toList)
  simp only [List.length_append, G.header_length, Bits.length_toList] at hi
  change (Tape.ofBits (G.header n (F n) ++ challenge.toList)).cells + 1 ≤ _
  omega

/-- Every random execution prefix of the registered native attack satisfies
the same bit bound for every legal ciphertext challenge and public family. -/
theorem native_codeAndStateBits_peak (n : Nat) (challenge : Bits (G.outputLength n))
    (elapsed : Nat) (hElapsed : elapsed ≤ time n) (target : Machine.Configuration)
    (hTarget : Masking.Configuration.running target ∈
      (Masking.eval (.native W.program)
        (Masking.initial (.native W.program) (G.header n (F n))
          (F n).1.toList (F n).2.toList challenge.toList) elapsed).support) :
    target.codeAndStateBits W.program ≤ G.nativeStorageBound time F A W n := by
  change Masking.Configuration.running target ∈
    (Masking.eval (.native W.program)
      (.running (Machine.Configuration.initial (G.header n (F n) ++ challenge.toList))) elapsed).support at hTarget
  rw [Masking.running_eval, PMF.mem_support_map_iff] at hTarget
  obtain ⟨machine, hMachine, hSame⟩ := hTarget
  have heq : machine = target := Masking.Configuration.running.inj hSame
  subst machine
  rw [← Machine.timed_eval_eq] at hMachine
  have hp := Machine.codeAndStateBits_prefix W.program (time n) elapsed hElapsed
    (Machine.Configuration.initial (G.header n (F n) ++ challenge.toList)) target hMachine
  have hi := G.native_initial_cells F n challenge
  have hPc : (Machine.Configuration.initial (G.header n (F n) ++ challenge.toList)).pc = 0 := rfl
  rw [hPc] at hp
  change target.codeAndStateBits W.program ≤ W.program.storageBound 0 (n + 5 * G.outputLength n + 5) (time n)
  apply hp.trans
  unfold Program.storageBound
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left 18 (Nat.add_le_add_right hi (time n))) _) 14

theorem nativeStorageBound_polynomial (hLength : PolynomiallyBounded G.outputLength)
    (hTime : PolynomiallyBounded time) : PolynomiallyBounded (G.nativeStorageBound time F A W) := by
  have hi := ((PolynomiallyBounded.id.add ((PolynomiallyBounded.const 5).mul hLength)).add
    (PolynomiallyBounded.const 5))
  exact Machine.storageBound_polynomial W.program (PolynomiallyBounded.const 0) hi hTime

end Foundation.Symmetric.Generator
