import Foundation.Crypto.Semantics.CostedIteration
import Foundation.Crypto.Semantics.Oracle.SpentSource
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! A public, cost-preserving stopped iteration is implemented by the real
spent-key runtime. The key is retained physically and omitted only from the
public observation. Caller branching and query repetition remain unrestricted. -/
namespace CryptoOracle.Interactive.SpentIteration
open Foundation.Probability TimedExecution
universe u
variable {State : Type u} (code : Code) (oracle : BitOracle State)
    (native : Machine.Program) (key : Machine.Tape)

noncomputable def transition :=
  (Procedure.transition (SpentSource.step code oracle)).transport
    (OneUseSource.step native code oracle) (SpentSource.embed key)
    (SpentSource.step_embedding code oracle native key)

theorem transition_bound (start : SpentSource.Control State) :
    (transition code oracle native key).budget start ≤ 1 := Nat.le_refl 1

theorem transition_return (start finish : SpentSource.Control State)
    (_ : finish ∈ ((transition code oracle native key).semantics start).support) :
    (transition code oracle native key).exit start finish = (transition code oracle native key).entry finish := rfl

noncomputable def execution (stop : SpentSource.Control State → Bool) (fuel : Nat) :=
  (transition code oracle native key).iterateUntil stop 1
    (transition_bound code oracle native key) (transition_return code oracle native key) fuel

noncomputable def publicKernel (start : SpentSource.Control State) :=
  (SpentSource.step code oracle start).map (fun next => (next, 1))

theorem costed_public (stop : SpentSource.Control State → Bool) (fuel : Nat)
    (start : SpentSource.Control State) :
    (execution code oracle native key stop fuel).costed start =
      CostedIteration.eval (CostedIteration.guarded (publicKernel code oracle) stop) fuel start := by
  have h := Procedure.iterateUntil_public_cost (transition code oracle native key) 1
    (transition_bound code oracle native key) (transition_return code oracle native key)
    stop stop (publicKernel code oracle) id (fun _ => rfl)
    (fun _ => by exact PMF.map_id _) fuel start
  change ((execution code oracle native key stop fuel).costed start).map id = _ at h
  rw [PMF.map_id] at h
  exact h

/-- Observe the actual physical exit and its cost, rather than an abstract
value that might have discarded the key before runtime execution. -/
noncomputable def publicJoint (stop : SpentSource.Control State → Bool) (fuel : Nat)
    (start : SpentSource.Control State) :=
  ((execution code oracle native key stop fuel).costed start).map (fun result =>
    (SpentSource.erase ((execution code oracle native key stop fuel).exit start result.1), result.2))

theorem public_joint (stop : SpentSource.Control State → Bool) (fuel : Nat)
    (start : SpentSource.Control State) :
    publicJoint code oracle native key stop fuel start =
      (CostedIteration.eval (CostedIteration.guarded (publicKernel code oracle) stop) fuel start).map
        (fun result => (some result.1, result.2)) := by
  unfold publicJoint
  rw [costed_public]
  congr 1
  funext result
  have he : (execution code oracle native key stop fuel).exit start result.1 = SpentSource.embed key result.1 := by
    unfold execution Procedure.iterateUntil
    rw [Procedure.iterate_exit]
    rfl
  rw [he, SpentSource.erase_embed]

theorem key_independence (firstNative secondNative : Machine.Program)
    (firstKey secondKey : Machine.Tape) (stop : SpentSource.Control State → Bool)
    (fuel : Nat) (start : SpentSource.Control State) :
    publicJoint code oracle firstNative firstKey stop fuel start =
      publicJoint code oracle secondNative secondKey stop fuel start := by
  rw [public_joint, public_joint]

end CryptoOracle.Interactive.SpentIteration
