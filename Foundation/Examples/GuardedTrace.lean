import Foundation.Machine.GuardedTrace
import Foundation.Examples.GuardedTape

namespace Machine.Examples

open GuardedCompiler

example (source : Program) (start finish : Configuration) (steps : Nat)
    (run : RunsFor source start finish steps)
    (beforeInput beforeOutput : List (Option Bool)) :
    ∃ used, used ≤ steps * (17 * (sourceStorage start + steps) + 23) ∧
      RunsFor (compile source) (encodeConfiguration source.length beforeInput beforeOutput start)
        (encodeConfiguration source.length beforeInput beforeOutput finish) used :=
  compile_runs run beforeInput beforeOutput

example (q : Nat → Nat) (h : PolynomiallyBounded q) : PolynomiallyBounded (traceBudget q) :=
  traceBudget_polynomiallyBounded h

example : PolynomiallyBounded (traceBudget (fun m => (m + 1) ^ 2)) :=
  traceBudget_polynomiallyBounded
    ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).pow 2)

example : traceBudget (fun m => (m + 1) ^ 2) 2 = 2196 := rfl

/-- A particular halted source branch gives a halted compiled branch at
the polynomial majorant. This example deliberately quantifies one source
trace; it does not claim that every compiled branch has been classified. -/
example (source : Program) (input : List Bool) (finish : Configuration) (steps : Nat)
    (q : Nat → Nat) (run : RunsFor source (Configuration.initial input) finish steps)
    (hSteps : steps ≤ q input.length) (hHalted : finish.halted = true)
    (beforeInput beforeOutput : List (Option Bool)) :
    ∃ used, used ≤ traceBudget q input.length ∧
      RunsFor (compile source)
        (encodeConfiguration source.length beforeInput beforeOutput (Configuration.initial input))
        (encodeConfiguration source.length beforeInput beforeOutput finish) used ∧
      (encodeConfiguration source.length beforeInput beforeOutput finish).halted = true := by
  obtain ⟨used, hUsed, compiled⟩ := compile_runs_initial q run hSteps beforeInput beforeOutput
  exact ⟨used, hUsed, compiled, hHalted⟩

end Machine.Examples
