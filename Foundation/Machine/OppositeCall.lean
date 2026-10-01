import Foundation.Machine.TapeSwap
import Foundation.Machine.GuardedResult

namespace Machine.GuardedCompiler

/-- Run the actual guarded source-call code using the opposite physical
tapes. The caller prepares raw source input on its output tape, and reserves
fresh cells after saved DDH data on its input tape for source output. Code
construction relabels finite tape operands; no runtime tape-swap operation
or uncharged initialization is inserted. -/
def rawCompileOpposite (source : Program) : Program :=
  Program.swapTapes (rawCompile source)

/-- Full native source-call probability law. Only the physical tape roles
change; the original source input length and source budget are identical.
The returned configuration includes both saved prefixes, physical scratch
storage, tape heads, program counter, and halt status. -/
theorem rawCompileOpposite_configuration_eval (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    evalConfigWithin (rawCompileOpposite source)
      (packInputStart beforeInput beforeOutput input).swapTapes (rawTraceBudget q input.length) =
      (evalConfigWithin source (preparedSource input) (q input.length)).map
        (fun c => (rawResultFrom source input beforeInput beforeOutput c).swapTapes) := by
  rw [rawCompileOpposite, evalConfigWithin_swapTapes,
    rawCompile_configuration_eval_from source input beforeInput beforeOutput q halts,
    PMF.map_comp]
  rfl

/-- All random branches of the opposite-tape call reach a native halt within
the same polynomial overhead bound, provided the raw source call halts.
This is a contextual invocation law, not a fresh-input `PolynomialTime`
assertion with the ordinary physical input/output convention. -/
theorem rawCompileOpposite_haltsFrom (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (q : Nat → Nat)
    (halts : HaltsWithin source input (q input.length)) :
    ∀ finish, PaddedRunsFor (rawCompileOpposite source)
      (packInputStart beforeInput beforeOutput input).swapTapes finish
      (rawTraceBudget q input.length) → finish.halted = true := by
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [rawCompileOpposite_configuration_eval source input beforeInput beforeOutput q halts,
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, rfl⟩ := hMem
  rfl

/-- Raw source output is now physically on the input tape. Its copied bits
precede the saved caller data, which are preserved exactly behind the guard.
There is no opportunity for source head moves to inspect that caller prefix. -/
theorem rawCompileOpposite_preserves_saved_data (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (c : Configuration) :
    ((rawResultFrom source input beforeInput beforeOutput c).swapTapes).inputTape.left.drop
      c.outputBits.length = beforeOutput :=
  (rawResultFrom_preserves_saved_data source input beforeInput beforeOutput c).2

theorem rawCompileOpposite_length (source : Program) :
    (rawCompileOpposite source).length = 68 * source.length + 155 := by
  rw [rawCompileOpposite, Program.swapTapes_length]
  exact rawCompile_length source

/-- On the physical input tape, protected caller bits precede the copied
raw source output. Blank padding remains represented but adds no data bits. -/
theorem rawCompileOpposite_result_bits (source : Program) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (c : Configuration) :
    ((rawResultFrom source input beforeInput beforeOutput c).swapTapes).inputTape.bits =
      beforeOutput.reverse.filterMap id ++ c.outputBits := by
  simp [rawResultFrom, Configuration.swapTapes, extractOutputFinish,
    copyScratchFinish, Tape.bits, Configuration.outputBits, List.reverse_append,
    List.filterMap_append]

end Machine.GuardedCompiler
