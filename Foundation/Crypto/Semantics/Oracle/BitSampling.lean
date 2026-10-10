import Foundation.Crypto.Semantics.Oracle.Composition
import Foundation.Constructions.Symmetric.BitSampling

/-! Uniform finite bitstrings compiled into the existing fair-coin syntax.
This sampler makes exactly `width` local draws and no oracle queries. Host
continuations still need separate certified machine implementations. -/
namespace CryptoOracle.Program

open Foundation.Probability Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

variable {Request Response Result State : Type}

def sampleBitsWith : (width : Nat) → (Bits width → Program Request Response Result) →
    Program Request Response Result
  | 0, next => next Fin.elim0
  | width + 1, next => .coin fun bit =>
      sampleBitsWith width (fun bits => next (Fin.snoc bits bit))

/-- Sequencing after the sampler keeps exactly the same fair-coin program.
This algebraic equation does not assign costs to host continuations. -/
theorem sampleBitsWith_bind {NextResult : Type} (width : Nat)
    (next : Bits width → Program Request Response Result)
    (more : Result → Program Request Response NextResult) :
    (sampleBitsWith width next).bind more =
      sampleBitsWith width (fun bits => (next bits).bind more) := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [sampleBitsWith, Program.bind]
      congr 1
      funext bit
      exact ih _

/-- Full outcome distribution, including state and trace, is preserved. -/
theorem sampleBitsWith_run (width : Nat) (next : Bits width → Program Request Response Result)
    (oracle : Oracle Request Response State) (state : State) :
    (sampleBitsWith width next).run oracle state =
      (uniform (Bits width)).bind (fun bits => (next bits).run oracle state) := by
  induction width with
  | zero =>
      have he : uniform (Bits 0) = PMF.pure Fin.elim0 := by
        ext bits
        have hb : bits = Fin.elim0 := Subsingleton.elim _ _
        subst bits
        simp [uniform]
      simp [sampleBitsWith, he]
  | succ width ih =>
      rw [Bits.uniform_snoc]
      simp only [sampleBitsWith, run, ih, PMF.bind_bind, PMF.bind_map, Function.comp_def]

theorem sampleBitsWith_queries (width : Nat)
    (next : Bits width → Program Request Response Result) (q : Nat)
    (bound : ∀ bits, (next bits).BoundedQueries q) :
    (sampleBitsWith width next).BoundedQueries q := by
  induction width with
  | zero => exact bound _
  | succ width ih => exact .coin _ q (fun bit => ih _ (fun bits => bound (Fin.snoc bits bit)))

end CryptoOracle.Program
