import Foundation.Crypto.Semantics.Machine.ScalarGeneratorPower
import Foundation.Crypto.Semantics.Machine.NativeKeygenReturn

namespace Machine.NativeKeygenContinuation

def program : Program := ScalarGeneratorPower.program.followedBy NativeKeygenReturn.program

def powerBudget (n : Nat) : Nat := 1000*(n+3)+
  GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget (3*(n+3))

def budget (n : Nat) : Nat := 9*powerBudget n+2000*(n+3)

/-- An accepted scalar becomes the secret key, and its actual generator
power becomes the public key. Every stage uses the same retained tapes. -/
theorem runs_numbers (n modulus order generator scalar : Nat)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hOrder : order < 2^(n+3)) (hScalar : scalar < 2^(n+3)) (hGenerator : generator < modulus) :
    let p := Binary.encode (n+3) modulus
    let q := Binary.encode (n+3) order
    let g := Binary.encode (n+3) generator
    let s := Binary.encode (n+3) scalar
    let raw := encodeSecurityParameter n ++ frame (p++q++g)
    ∃ target used, used ≤ budget n ∧
      RunsFor program
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some}, outputTape := {left := s.reverse.map some}} : Configuration) target used ∧
      target.halted = true ∧ target.outputBits =
        frame (Binary.encode (n+3) (generator^scalar % modulus)) ++ frame s := by
  dsimp only
  let p := Binary.encode (n+3) modulus
  let q := Binary.encode (n+3) order
  let g := Binary.encode (n+3) generator
  let s := Binary.encode (n+3) scalar
  let raw := encodeSecurityParameter n ++ frame (p++q++g)
  let modified := encodeSecurityParameter n ++ frame (p++s++g)
  let columns := BinaryColumnSlotFill.fullSlots g s p
  obtain ⟨c, powered, u, hu, powerRun, powerHalt, _, coreBits, powerInput, powerOutput, _⟩ :=
    ScalarGeneratorPower.runs_numbers n modulus order generator scalar hOne hModulus hOrder hScalar hGenerator
  have hPowerLength : c.outputBits.length = n+3 := by rw [coreBits]; simp
  have hPowerBudget : u ≤ powerBudget n := by
    have columnsLength : columns.length = 3*(n+3) := by
      simp [columns, BinaryColumnSlotFill.fullSlots_length, p, s, g]
    have rawLength : raw.length = n+6*(n+3)+2 := by simp [raw, p, q, g, frame, encodeSecurityParameter]; omega
    have validLength : FramedExponentPreparation.validBudget n p s g ≤ 200*(n+3) := by
      simp [FramedExponentPreparation.validBudget, BinaryThirdColumnTemplate.columns_length, p, s, g]
      omega
    change u ≤ 20*raw.length+40*(n+3)+100+
      FramedExponentPreparation.validBudget n p s g+4*columns.length+8*g.length+32+
      GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length at hu
    rw [rawLength, columnsLength] at hu
    have glen : g.length = n+3 := by simp [g]
    rw [glen] at hu
    unfold powerBudget
    omega
  obtain ⟨keys, v, hv, keyRun, keyHalt, keyBits⟩ := NativeKeygenReturn.runs
    BinaryPowerExternalWidth.program n p s g columns c (by simp [p, hPowerLength])
    (by simp [s, hPowerLength]) (by simp [g,s]) (by intro empty; have len := congrArg List.length empty; simp [s] at len)
  have boundary : ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
      (none::modified.reverse.map some) c).swapTapes.resumeAt 0).Equivalent (powered.resumeAt 0) :=
    ⟨rfl, rfl, powerInput.symm, powerOutput.symm⟩
  obtain ⟨target, used, bound, run, halt, _, tout⟩ := powerRun.followedBy_equivalent keyRun boundary
    (Nat.zero_le _) rfl powerHalt keyHalt
  refine ⟨target, used, ?_, run, halt, ?_⟩
  · have sourceStorage := NativeKeygenReturn.source_cells_le_of_run columns modified c powerRun powerOutput
    have startCells :
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some}, outputTape := {left := s.reverse.map some}} : Configuration).inputTape.cells+
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some}, outputTape := {left := s.reverse.map some}} : Configuration).outputTape.cells = raw.length+2*(n+3)+3 := by
      simp [Tape.cells, s]; omega
    rw [startCells] at sourceStorage
    have returnBound := NativeKeygenReturn.budget_le n p s g columns c (by simp [p,s]) (by simp [g,s]) (by simp [s,hPowerLength])
    have rawLength : raw.length = n+6*(n+3)+2 := by simp [raw, p, q, g, frame, encodeSecurityParameter]; omega
    have columnsLength : columns.length = 3*(n+3) := by simp [columns, BinaryColumnSlotFill.fullSlots_length, p, s, g]
    have scalarLength : s.length = n+3 := by simp [s]
    rw [rawLength] at sourceStorage
    rw [columnsLength, scalarLength] at returnBound
    change v ≤ NativeKeygenReturn.budget n p s g columns c at hv
    unfold budget
    omega
  · change target.outputTape.bits = _
    have outputKeys : keys.outputTape.bits = frame c.outputBits ++ frame s := keyBits
    rw [tout.bits.symm, outputKeys, coreBits]

/-- The explicit bound is polynomial in the public security parameter. -/
theorem budget_polynomiallyBounded : PolynomiallyBounded budget := by
  have width := PolynomiallyBounded.id.add (PolynomiallyBounded.const 3)
  have columns := (PolynomiallyBounded.const 3).mul width
  have source := ((PolynomiallyBounded.const 5).mul columns).add
    (PolynomiallyBounded.const 19)
  have power := (PolynomiallyBounded.const 100000000000000000000000).mul
    ((columns.add (PolynomiallyBounded.const 4)).pow 10)
  have sourceBound : PolynomiallyBounded (fun n => BinaryPowerExternalWidth.budget (3*(n+3))) := by
    simpa [BinaryPowerExternalWidth.budget, BinaryPowerPadded.budget,
      BinaryWorkspacePreparation.budget, BinaryPowerProgram.budget,
      Nat.add_assoc] using (source.add power).add (PolynomiallyBounded.const 5)
  have guarded := ((PolynomiallyBounded.const 125).mul
    (columns.add (PolynomiallyBounded.const 1))).mul
      ((sourceBound.add (PolynomiallyBounded.const 1)).pow 2)
  have actual := guarded.mono (fun n => GuardedCompiler.rawTraceBudget_bound
    BinaryPowerExternalWidth.budget (3*(n+3)))
  exact ((PolynomiallyBounded.const 9).mul
    (((PolynomiallyBounded.const 1000).mul width).add actual)).add
      ((PolynomiallyBounded.const 2000).mul width)

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ ScalarGeneratorPower.no_randomBit NativeKeygenReturn.no_randomBit tape

end Machine.NativeKeygenContinuation
