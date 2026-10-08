import Foundation.Constructions.Symmetric.EncryptThenMAC.SeededGeneratorImplementation
import Foundation.Crypto.Semantics.Machine.RankedFamily

/-! Construct native expander contracts from local program assertions and
ranks, without supplying an endpoint PMF or a whole-program run proof.
Assertions may depend on the original seed; they are proof metadata only.
The finite code must physically produce the specified exported output tape. -/
namespace Foundation.Symmetric.EncryptThenMAC.SeededGeneratorImplementation
open Machine Foundation.Probability TimedExecution

structure RankedExpander (G : Generator) where
  code : Machine.Program
  closed : ∀ start target, start.pc < code.length → Step code start target →
    target.halted = false → target.pc < code.length
  nonempty : 0 < code.length
  assertions : ∀ n, Bits (G.seedLength n) → Program.Assertions
  verified : ∀ n seed, (assertions n seed).Verified code
  ranking : ∀ n seed, Program.Ranking (assertions n seed) code
  initial : ∀ n seed, (assertions n seed).Holds ((seedEntry G n seed).resumeAt 0)
  cap : Nat → Nat
  bounded : ∀ n seed, (ranking n seed).rank ((seedEntry G n seed).resumeAt 0) + 1 ≤ cap n
  output : ∀ n seed (machine : Machine.Configuration),
    (assertions n seed).stopped machine.pc machine.inputTape machine.outputTape →
      machine.outputTape = ResponseExport.endTape (G.generate n seed).toList

namespace RankedExpander
variable {G : Generator} (E : RankedExpander G)

noncomputable def family (n : Nat) : Program.RankedFamily E.code (Bits (G.seedLength n)) where
  assertions := E.assertions n
  verified := E.verified n
  ranking := E.ranking n
  entry := fun seed => (seedEntry G n seed).resumeAt 0
  valid := E.initial n

/-- The usual seeded assembly interface is derived from local obligations.
Only actual sampled-seed layouts require these certificates. -/
noncomputable def toExpander : Expander G where
  Output := fun _ => Configuration
  code := E.code
  execution := fun n => (E.family n).execution
  closed := E.closed
  entry := fun _ _ => rfl
  nonempty := E.nonempty
  halted := fun n seed machine h => (E.family n).halted seed machine h
  cap := E.cap
  bounded := fun n seed => E.bounded n seed
  tape := fun n seed machine h => E.output n seed machine ((E.family n).stopped seed machine h)

theorem toExpander_code : E.toExpander.code = E.code := rfl

theorem entry (n : Nat) (seed : Bits (G.seedLength n)) :
    (E.toExpander.execution n).entry seed = (seedEntry G n seed).resumeAt 0 := rfl

theorem budget (n : Nat) (seed : Bits (G.seedLength n)) :
    (E.toExpander.execution n).budget seed =
      (E.ranking n seed).rank ((seedEntry G n seed).resumeAt 0) + 1 := rfl

/-- Full endpoints and actual first-arrival times remain correlated. -/
theorem costed (n : Nat) (seed : Bits (G.seedLength n)) :
    (E.toExpander.execution n).costed seed =
      runToBoundary (stepPMF E.code) Configuration.halted
        ((E.ranking n seed).rank ((seedEntry G n seed).resumeAt 0) + 1)
        ((seedEntry G n seed).resumeAt 0) :=
  (E.family n).costed seed

theorem operational (n : Nat) : TimedExecution.Procedure.Operational (E.toExpander.execution n) :=
  (E.family n).operational

end RankedExpander
end Foundation.Symmetric.EncryptThenMAC.SeededGeneratorImplementation
