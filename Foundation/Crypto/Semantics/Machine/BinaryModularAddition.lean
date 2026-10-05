import Foundation.Crypto.Semantics.Machine.BinaryAddition
import Foundation.Crypto.Semantics.Machine.BinarySubtraction
import Foundation.Crypto.Semantics.Machine.BitstringRewind

set_option maxRecDepth 4096

namespace Machine.BinaryModularAddition

/-- One fixed finite bit program adds two equal-width residues and performs
one conditional subtraction. Carry and borrow occupy finite control, not
unbounded registers. The original operands are preserved so the underflow
path can rewind and overwrite the tentative difference with their sum. -/
def program : Program :=
  [
   .jump 10,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .branch .input 266 11 14,
   .moveRight .input,
   .branch .input 267 18 21,
   .halt,
   .moveRight .input,
   .branch .input 267 24 27,
   .halt,
   .halt,
   .moveRight .input,
   .branch .input 267 30 34,
   .halt,
   .moveRight .input,
   .branch .input 267 38 42,
   .halt,
   .moveRight .input,
   .branch .input 267 46 50,
   .halt,
   .moveRight .input,
   .branch .input 267 54 58,
   .halt,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 138,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 74,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 202,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .branch .input 266 75 78,
   .moveRight .input,
   .branch .input 267 82 85,
   .halt,
   .moveRight .input,
   .branch .input 267 88 91,
   .halt,
   .halt,
   .moveRight .input,
   .branch .input 267 94 98,
   .halt,
   .moveRight .input,
   .branch .input 267 102 106,
   .halt,
   .moveRight .input,
   .branch .input 267 110 114,
   .halt,
   .moveRight .input,
   .branch .input 267 118 122,
   .halt,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 74,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 202,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 74,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 202,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 74,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 74,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .branch .input 269 139 142,
   .moveRight .input,
   .branch .input 267 146 149,
   .halt,
   .moveRight .input,
   .branch .input 267 152 155,
   .halt,
   .halt,
   .moveRight .input,
   .branch .input 267 158 162,
   .halt,
   .moveRight .input,
   .branch .input 267 166 170,
   .halt,
   .moveRight .input,
   .branch .input 267 174 178,
   .halt,
   .moveRight .input,
   .branch .input 267 182 186,
   .halt,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 138,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 138,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 138,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 138,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 202,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 202,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .branch .input 269 203 206,
   .moveRight .input,
   .branch .input 267 210 213,
   .halt,
   .moveRight .input,
   .branch .input 267 216 219,
   .halt,
   .halt,
   .moveRight .input,
   .branch .input 267 222 226,
   .halt,
   .moveRight .input,
   .branch .input 267 230 234,
   .halt,
   .moveRight .input,
   .branch .input 267 238 242,
   .halt,
   .moveRight .input,
   .branch .input 267 246 250,
   .halt,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 10,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 138,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 202,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 202,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 202,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 202,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 74,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 202,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .erase .output,
   .halt,
   .moveLeft .input,
   .branch .input 275 271 271,
   .moveLeft .input,
   .moveLeft .input,
   .moveLeft .output,
   .jump 269,
   .moveLeft .output,
   .moveRight .input,
   .moveRight .output,
   .jump 280,
   .halt,
   .branch .input 408 281 284,
   .moveRight .input,
   .branch .input 267 288 291,
   .halt,
   .moveRight .input,
   .branch .input 267 294 297,
   .halt,
   .halt,
   .moveRight .input,
   .jump 300,
   .halt,
   .moveRight .input,
   .jump 304,
   .halt,
   .moveRight .input,
   .jump 308,
   .halt,
   .moveRight .input,
   .jump 312,
   .halt,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 280,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 280,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 280,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 344,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .branch .input 408 345 348,
   .moveRight .input,
   .branch .input 267 352 355,
   .halt,
   .moveRight .input,
   .branch .input 267 358 361,
   .halt,
   .halt,
   .moveRight .input,
   .jump 364,
   .halt,
   .moveRight .input,
   .jump 368,
   .halt,
   .moveRight .input,
   .jump 372,
   .halt,
   .moveRight .input,
   .jump 376,
   .halt,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 280,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 344,
   .write .output false,
   .moveRight .input,
   .moveRight .output,
   .jump 344,
   .write .output true,
   .moveRight .input,
   .moveRight .output,
   .jump 344,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt,
   .halt]

@[simp] private theorem lookup_280 : program[280]? = some (.branch .input 408 281 284) := rfl
@[simp] private theorem lookup_281 : program[281]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_282 : program[282]? = some (.branch .input 267 288 291) := rfl
@[simp] private theorem lookup_284 : program[284]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_285 : program[285]? = some (.branch .input 267 294 297) := rfl
@[simp] private theorem lookup_288 : program[288]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_289 : program[289]? = some (.jump 300) := rfl
@[simp] private theorem lookup_291 : program[291]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_292 : program[292]? = some (.jump 304) := rfl
@[simp] private theorem lookup_294 : program[294]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_295 : program[295]? = some (.jump 308) := rfl
@[simp] private theorem lookup_297 : program[297]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_298 : program[298]? = some (.jump 312) := rfl
@[simp] private theorem lookup_300 : program[300]? = some (.write .output false) := rfl
@[simp] private theorem lookup_301 : program[301]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_302 : program[302]? = some (.moveRight .output) := rfl
@[simp] private theorem lookup_303 : program[303]? = some (.jump 280) := rfl
@[simp] private theorem lookup_304 : program[304]? = some (.write .output true) := rfl
@[simp] private theorem lookup_305 : program[305]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_306 : program[306]? = some (.moveRight .output) := rfl
@[simp] private theorem lookup_307 : program[307]? = some (.jump 280) := rfl
@[simp] private theorem lookup_308 : program[308]? = some (.write .output true) := rfl
@[simp] private theorem lookup_309 : program[309]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_310 : program[310]? = some (.moveRight .output) := rfl
@[simp] private theorem lookup_311 : program[311]? = some (.jump 280) := rfl
@[simp] private theorem lookup_312 : program[312]? = some (.write .output false) := rfl
@[simp] private theorem lookup_313 : program[313]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_314 : program[314]? = some (.moveRight .output) := rfl
@[simp] private theorem lookup_315 : program[315]? = some (.jump 344) := rfl
@[simp] private theorem lookup_344 : program[344]? = some (.branch .input 408 345 348) := rfl
@[simp] private theorem lookup_345 : program[345]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_346 : program[346]? = some (.branch .input 267 352 355) := rfl
@[simp] private theorem lookup_348 : program[348]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_349 : program[349]? = some (.branch .input 267 358 361) := rfl
@[simp] private theorem lookup_352 : program[352]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_353 : program[353]? = some (.jump 364) := rfl
@[simp] private theorem lookup_355 : program[355]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_356 : program[356]? = some (.jump 368) := rfl
@[simp] private theorem lookup_358 : program[358]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_359 : program[359]? = some (.jump 372) := rfl
@[simp] private theorem lookup_361 : program[361]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_362 : program[362]? = some (.jump 376) := rfl
@[simp] private theorem lookup_364 : program[364]? = some (.write .output true) := rfl
@[simp] private theorem lookup_365 : program[365]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_366 : program[366]? = some (.moveRight .output) := rfl
@[simp] private theorem lookup_367 : program[367]? = some (.jump 280) := rfl
@[simp] private theorem lookup_368 : program[368]? = some (.write .output false) := rfl
@[simp] private theorem lookup_369 : program[369]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_370 : program[370]? = some (.moveRight .output) := rfl
@[simp] private theorem lookup_371 : program[371]? = some (.jump 344) := rfl
@[simp] private theorem lookup_372 : program[372]? = some (.write .output false) := rfl
@[simp] private theorem lookup_373 : program[373]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_374 : program[374]? = some (.moveRight .output) := rfl
@[simp] private theorem lookup_375 : program[375]? = some (.jump 344) := rfl
@[simp] private theorem lookup_376 : program[376]? = some (.write .output true) := rfl
@[simp] private theorem lookup_377 : program[377]? = some (.moveRight .input) := rfl
@[simp] private theorem lookup_378 : program[378]? = some (.moveRight .output) := rfl
@[simp] private theorem lookup_379 : program[379]? = some (.jump 344) := rfl
@[simp] private theorem lookup_408 : program[408]? = some (.halt) := rfl

/-- Three adjacent input cells form one little-endian column: the first
operand, the second operand, and the modulus. -/
abbrev Column := (Bool × Bool) × Bool

def interleave : List Column → List Bool
  | [] => []
  | ((first, second), modulus) :: rest =>
      first :: second :: modulus :: interleave rest

def operands (columns : List Column) : List (Bool × Bool) := columns.map Prod.fst
def moduli (columns : List Column) : List Bool := columns.map Prod.snd

def sumPairs : Bool → List Column → List (Bool × Bool)
  | _, [] => []
  | carry, ((first, second), modulus) :: rest =>
      (BinaryAddition.digit carry first second, modulus) ::
        sumPairs (BinaryAddition.nextCarry carry first second) rest

private def address (carry borrow : Bool) : Nat :=
  10 + 64 * (carry.toNat + 2 * borrow.toNat)

private def state (carry borrow : Bool) (before : List (Option Bool))
    (bits : List Bool) (written : List (Option Bool)) : Configuration :=
  { pc := address carry borrow,
    inputTape := { Tape.ofBits bits with left := before },
    outputTape := { left := written } }

set_option maxHeartbeats 1600000 in
private theorem eval_column (carry borrow first second modulus : Bool)
    (before written : List (Option Bool)) (rest : List Bool) :
    evalConfigWithin program (state carry borrow before (first :: second :: modulus :: rest) written) 9 =
      PMF.pure (state (BinaryAddition.nextCarry carry first second)
        (BinarySubtraction.nextBorrow borrow (BinaryAddition.digit carry first second) modulus)
        (some modulus :: some second :: some first :: before) rest
        (some (BinarySubtraction.digit borrow (BinaryAddition.digit carry first second) modulus) :: written)) := by
  cases carry <;> cases borrow <;> cases first <;> cases second <;> cases modulus <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address,
      BinaryAddition.digit, BinaryAddition.nextCarry,
      BinarySubtraction.digit, BinarySubtraction.nextBorrow,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_columns_context (columns : List Column) (carry borrow : Bool)
    (before written : List (Option Bool)) (following : List Bool) :
    evalConfigWithin program (state carry borrow before
      (interleave columns ++ following) written) (9 * columns.length) =
      PMF.pure (state (BinaryAddition.carryOut carry (operands columns))
        (BinarySubtraction.borrowOut borrow (sumPairs carry columns))
        ((interleave columns).reverse.map some ++ before) following
        ((BinarySubtraction.differenceBits borrow (sumPairs carry columns)).reverse.map some ++ written)) := by
  induction columns generalizing carry borrow before written with
  | nil => simp [evalConfigWithin, BinaryAddition.carryOut, operands, sumPairs,
      BinarySubtraction.borrowOut, BinarySubtraction.differenceBits,
      BinarySubtraction.lowerBits, interleave]
  | cons column rest ih =>
      rcases column with ⟨⟨first, second⟩, modulus⟩
      have hBudget : 9 * (((first, second), modulus) :: rest).length = 9 + 9 * rest.length := by
        simp; omega
      rw [hBudget, evalConfigWithin_add]
      simp only [interleave, List.cons_append, eval_column, PMF.pure_bind, ih,
        sumPairs, operands, List.map_cons, BinaryAddition.carryOut,
        BinarySubtraction.borrowOut, BinarySubtraction.differenceBits,
        BinarySubtraction.lowerBits]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

private def copyAddress (carry : Bool) : Nat := 280 + 64 * carry.toNat

private def rewindState (remaining : List (Column × Bool))
    (currentInput currentOutput : Option Bool) (afterInput afterOutput : List (Option Bool)) :
    Configuration :=
  { pc := 269,
    inputTape := {
      left := remaining.flatMap (fun column =>
        [some column.1.2, some column.1.1.2, some column.1.1.1]),
      current := currentInput, right := afterInput },
    outputTape := {
      left := remaining.map (fun column => some column.2),
      current := currentOutput, right := afterOutput } }

private def rewindFinish (remaining : List (Column × Bool))
    (currentInput currentOutput : Option Bool) (afterInput afterOutput : List (Option Bool)) :
    Configuration :=
  { pc := copyAddress false,
    inputTape := ({ right := remaining.reverse.flatMap (fun column =>
      [some column.1.1.1, some column.1.1.2, some column.1.2]) ++
        currentInput :: afterInput } : Tape).moveRight,
    outputTape := ({ right := remaining.reverse.map (fun column => some column.2) ++
      currentOutput :: afterOutput } : Tape).moveRight }

private theorem eval_rewind_column (first second modulus output : Bool)
    (remaining : List (Column × Bool)) (currentInput currentOutput : Option Bool)
    (afterInput afterOutput : List (Option Bool)) :
    evalConfigWithin program
      (rewindState ((((first, second), modulus), output) :: remaining)
        currentInput currentOutput afterInput afterOutput) 6 =
      PMF.pure (rewindState remaining (some first) (some output)
        (some second :: some modulus :: currentInput :: afterInput) (currentOutput :: afterOutput)) := by
  cases modulus <;>
    simp [evalConfigWithin, stepPMF, next, program, rewindState,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.moveLeft, PMF.pure_bind]

private theorem eval_rewind_end (currentInput currentOutput : Option Bool)
    (afterInput afterOutput : List (Option Bool)) :
    evalConfigWithin program (rewindState [] currentInput currentOutput afterInput afterOutput) 6 =
      PMF.pure (rewindFinish [] currentInput currentOutput afterInput afterOutput) := by
  simp [evalConfigWithin, stepPMF, next, program, rewindState, rewindFinish, copyAddress,
    Instruction.next, Configuration.advance, Configuration.tape,
    Configuration.updateTape, Tape.moveLeft, Tape.moveRight, PMF.pure_bind]

private theorem eval_rewind (remaining : List (Column × Bool))
    (currentInput currentOutput : Option Bool) (afterInput afterOutput : List (Option Bool)) :
    evalConfigWithin program (rewindState remaining currentInput currentOutput afterInput afterOutput)
      (6 * remaining.length + 6) =
      PMF.pure (rewindFinish remaining currentInput currentOutput afterInput afterOutput) := by
  induction remaining generalizing currentInput currentOutput afterInput afterOutput with
  | nil => simpa using eval_rewind_end currentInput currentOutput afterInput afterOutput
  | cons column rest ih =>
      rcases column with ⟨⟨⟨first, second⟩, modulus⟩, output⟩
      have hBudget : 6 * (((((first, second), modulus), output)) :: rest).length + 6 =
          6 + (6 * rest.length + 6) := by simp; omega
      rw [hBudget, evalConfigWithin_add, eval_rewind_column, PMF.pure_bind, ih]
      simp [rewindFinish, List.reverse_cons, List.flatMap_append, List.map_append,
        List.append_assoc]

private def copyState (carry : Bool) (before : List (Option Bool)) (bits : List Bool)
    (written : List (Option Bool)) (old : List Bool) : Configuration :=
  { pc := copyAddress carry,
    inputTape := { Tape.ofBits bits with left := before },
    outputTape := { Tape.ofBits old with left := written } }

private def copyFinish (before written : List (Option Bool)) (old : List Bool) : Configuration :=
  { pc := 408, inputTape := { left := before },
    outputTape := { Tape.ofBits old with left := written }, halted := true }

set_option maxHeartbeats 1600000 in
private theorem eval_copy_column (carry first second modulus : Bool) (before written : List (Option Bool))
    (rest old : List Bool) :
    evalConfigWithin program (copyState carry before (first :: second :: modulus :: rest) written old) 9 =
      PMF.pure (copyState (BinaryAddition.nextCarry carry first second)
        (some modulus :: some second :: some first :: before) rest
        (some (BinaryAddition.digit carry first second) :: written) old.tail) := by
  cases old with
  | nil =>
      cases carry <;> cases first <;> cases second <;> cases rest <;>
      simp [evalConfigWithin, stepPMF, next, copyState, copyAddress,
        BinaryAddition.digit, BinaryAddition.nextCarry,
        Instruction.next, Configuration.advance, Configuration.tape,
        Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]
  | cons oldBit oldRest =>
      cases oldRest <;> cases carry <;> cases first <;> cases second <;> cases rest <;>
      simp [evalConfigWithin, stepPMF, next, copyState, copyAddress,
        BinaryAddition.digit, BinaryAddition.nextCarry,
        Instruction.next, Configuration.advance, Configuration.tape,
        Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_copy_end (carry : Bool) (before written : List (Option Bool))
    (old : List Bool) :
    evalConfigWithin program (copyState carry before [] written old) 2 =
      PMF.pure (copyFinish before written old) := by
  cases carry <;>
    simp [evalConfigWithin, stepPMF, next, copyState, copyAddress, copyFinish,
      Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

private theorem eval_copy_columns (carry : Bool) (columns : List Column)
    (before written : List (Option Bool)) (old : List Bool) :
    evalConfigWithin program (copyState carry before (interleave columns) written old)
      (9 * columns.length + 2) =
      PMF.pure (copyFinish ((interleave columns).reverse.map some ++ before)
        ((BinaryAddition.lowerBits carry (operands columns)).reverse.map some ++ written)
        (old.drop columns.length)) := by
  induction columns generalizing carry before written old with
  | nil => simpa [interleave, operands, BinaryAddition.lowerBits] using eval_copy_end carry before written old
  | cons column rest ih =>
      rcases column with ⟨⟨first, second⟩, modulus⟩
      have hBudget : 9 * (((first, second), modulus) :: rest).length + 2 = 9 + (9 * rest.length + 2) := by
        simp; omega
      rw [hBudget, evalConfigWithin_add]
      simp only [interleave, eval_copy_column, PMF.pure_bind, ih,
        operands, List.map_cons, BinaryAddition.lowerBits, List.length_cons]
      simp [List.reverse_cons, List.map_append, List.append_assoc, List.drop_tail]

private theorem sumPairs_length (carry : Bool) (columns : List Column) :
    (sumPairs carry columns).length = columns.length := by
  induction columns generalizing carry with
  | nil => rfl
  | cons column rest ih => simp [sumPairs, ih]

private theorem sumPairs_snd (carry : Bool) (columns : List Column) :
    (sumPairs carry columns).map Prod.snd = moduli columns := by
  induction columns generalizing carry with
  | nil => rfl
  | cons column rest ih => simp [sumPairs, moduli, ih]

private theorem sumPairs_fst (carry : Bool) (columns : List Column) :
    (sumPairs carry columns).map Prod.fst = BinaryAddition.lowerBits carry (operands columns) := by
  induction columns generalizing carry with
  | nil => rfl
  | cons column rest ih => simp [sumPairs, operands, BinaryAddition.lowerBits, ih]

private theorem lowerBits_length (carry : Bool) (pairs : List (Bool × Bool)) :
    (BinaryAddition.lowerBits carry pairs).length = pairs.length := by
  induction pairs generalizing carry with
  | nil => rfl
  | cons pair rest ih => simp [BinaryAddition.lowerBits, ih]

private theorem lowerBits_value (carry : Bool) (pairs : List (Bool × Bool)) :
    Binary.value (BinaryAddition.lowerBits carry pairs) +
      2 ^ pairs.length * (BinaryAddition.carryOut carry pairs).toNat =
      Binary.value (pairs.map Prod.fst) + Binary.value (pairs.map Prod.snd) + carry.toNat := by
  induction pairs generalizing carry with
  | nil => simp [BinaryAddition.lowerBits, BinaryAddition.carryOut, Binary.value]
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      have h := congrArg (fun x : Nat => 2 * x)
        (ih (BinaryAddition.nextCarry carry first second))
      simp only [BinaryAddition.lowerBits, BinaryAddition.carryOut, Binary.value,
        List.map_cons, List.length_cons, pow_succ]
      have hDigit : (BinaryAddition.digit carry first second).toNat +
          2 * (BinaryAddition.nextCarry carry first second).toNat =
          first.toNat + second.toNat + carry.toNat := by
        cases carry <;> cases first <;> cases second <;> decide
      ring_nf at h ⊢
      omega

private theorem sumPairs_value (carry : Bool) (columns : List Column) :
    Binary.value ((sumPairs carry columns).map Prod.fst) +
      2 ^ columns.length * (BinaryAddition.carryOut carry (operands columns)).toNat =
      Binary.value ((operands columns).map Prod.fst) +
        Binary.value ((operands columns).map Prod.snd) + carry.toNat := by
  simpa [sumPairs_fst, operands] using lowerBits_value carry (operands columns)

private theorem interleave_flatMap (columns : List Column) :
    interleave columns = columns.flatMap (fun column => [column.1.1, column.1.2, column.2]) := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp [interleave, ih]

private theorem zip_input_cells (columns : List Column) (old : List Bool)
    (hLength : old.length = columns.length) :
    (columns.zip old).flatMap (fun column =>
      [some column.1.1.1, some column.1.1.2, some column.1.2]) =
      (interleave columns).map some := by
  have hFirst := List.map_fst_zip (l₁ := columns) (l₂ := old) (by omega)
  have h := congrArg (fun xs : List Column =>
    xs.flatMap (fun column => [some column.1.1, some column.1.2, some column.2])) hFirst
  simpa only [List.flatMap_map, interleave_flatMap, List.map_flatMap, List.map_cons,
    List.map_nil] using h

private theorem zip_output_cells (columns : List Column) (old : List Bool)
    (hLength : old.length = columns.length) :
    (columns.zip old).map (fun column => some column.2) = old.map some := by
  have h := congrArg (List.map some)
    (List.map_snd_zip (l₁ := columns) (l₂ := old) (by omega))
  simpa only [List.map_map, Function.comp_def] using h

private theorem rewindState_eq (columns : List Column) (old : List Bool)
    (hLength : old.length = columns.length) :
    rewindState (columns.zip old).reverse none none [] [] =
      { pc := 269,
        inputTape := { left := (interleave columns).reverse.map some },
        outputTape := { left := old.reverse.map some } } := by
  have hInput : (columns.zip old).reverse.flatMap (fun column =>
      [some column.1.2, some column.1.1.2, some column.1.1.1]) =
      (interleave columns).reverse.map some := by
    rw [List.flatMap_reverse]
    simpa [Function.comp_def, ← List.map_reverse] using
      congrArg List.reverse (zip_input_cells columns old hLength)
  simp [rewindState, hInput, List.map_reverse, zip_output_cells columns old hLength]

private theorem rewindFinish_equivalent (columns : List Column)
    (old : List Bool) (hLength : old.length = columns.length) :
    (rewindFinish (columns.zip old).reverse none none [] []).Equivalent
      (copyState false [] (interleave columns) [] old) := by
  have hInput := zip_input_cells columns old hLength
  have hOutput := zip_output_cells columns old hLength
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have h := rewindBitstringFinish_input_equivalent (interleave columns) {}
    cases hBits : interleave columns <;>
      simpa [rewindFinish, rewindBitstringFinish, copyState, hInput, Tape.ofBits,
        Tape.moveRight, hBits] using h
  · have h := rewindBitstringFinish_input_equivalent old {}
    cases old <;> simpa [rewindFinish, rewindBitstringFinish, copyState, hOutput, Tape.ofBits] using h

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private theorem eval_copy_output (columns : List Column) (old : List Bool)
    (hLength : old.length = columns.length) :
    (evalConfigWithin program (copyState false [] (interleave columns) [] old)
      (9 * columns.length + 2)).map
      (fun c => if c.halted then some c.outputBits else none) =
        PMF.pure (some (BinaryAddition.lowerBits false (operands columns))) := by
  rw [eval_copy_columns, PMF.pure_map]
  have hDrop : old.drop columns.length = [] := List.drop_eq_nil_iff.mpr (by omega)
  simp [copyFinish, hDrop, Configuration.outputBits, Tape.bits, Tape.ofBits]

private def acceptedFinish (columns : List Column) (old : List Bool) : Configuration :=
  { pc := 266,
    inputTape := { left := (interleave columns).reverse.map some },
    outputTape := { left := old.reverse.map some }, halted := true }

private theorem eval_accept (carry : Bool) (columns : List Column) (old : List Bool) :
    evalConfigWithin program (state carry false
      ((interleave columns).reverse.map some) [] (old.reverse.map some)) 2 =
      PMF.pure (acceptedFinish columns old) := by
  cases carry <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address, acceptedFinish,
      Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

private theorem eval_select_rewind (carry : Bool) (columns : List Column)
    (old : List Bool) (hLength : old.length = columns.length) :
    evalConfigWithin program (state carry true
      ((interleave columns).reverse.map some) [] (old.reverse.map some)) 1 =
      PMF.pure (rewindState (columns.zip old).reverse none none [] []) := by
  rw [rewindState_eq columns old hLength]
  cases carry <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address,
      Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

private theorem eval_tail (carry borrow : Bool) (columns : List Column)
    (old : List Bool) (hLength : old.length = columns.length) :
    (evalConfigWithin program (state carry borrow
      ((interleave columns).reverse.map some) [] (old.reverse.map some))
      (15 * columns.length + 9)).map
      (fun c => if c.halted then some c.outputBits else none) =
      PMF.pure (some (if borrow then BinaryAddition.lowerBits false (operands columns) else old)) := by
  cases borrow with
  | false =>
      have hBudget : 15 * columns.length + 9 = 2 + (15 * columns.length + 7) := by omega
      rw [hBudget, evalConfigWithin_add, eval_accept, PMF.pure_bind,
        eval_halted _ _ rfl, PMF.pure_map]
      simp [acceptedFinish, Configuration.outputBits, Tape.bits]
  | true =>
      have hBudget : 15 * columns.length + 9 =
          1 + ((6 * columns.length + 6) + (9 * columns.length + 2)) := by omega
      rw [hBudget, evalConfigWithin_add, eval_select_rewind carry columns old hLength,
        PMF.pure_bind, evalConfigWithin_add]
      have hRewind := eval_rewind (columns.zip old).reverse none none [] []
      have hCount : (columns.zip old).reverse.length = columns.length := by
        simp [List.length_zip, hLength]
      rw [hCount] at hRewind
      rw [hRewind, PMF.pure_bind]
      exact ((rewindFinish_equivalent columns old hLength).evalOutput program
        (9 * columns.length + 2)).trans (eval_copy_output columns old hLength)

private def reducedBits (columns : List Column) : List Bool :=
  if BinarySubtraction.borrowOut false (sumPairs false columns) then
    BinaryAddition.lowerBits false (operands columns)
  else BinarySubtraction.differenceBits false (sumPairs false columns)

private theorem eval_start (input : List Bool) :
    evalConfigWithin program (Configuration.initial input) 1 =
      PMF.pure (state false false [] input []) := by
  cases input <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address,
      Configuration.initial, Instruction.next, Tape.ofBits]

private theorem eval_interleave (columns : List Column) :
    evalWithin program (interleave columns) (24 * columns.length + 10) =
      PMF.pure (some (reducedBits columns)) := by
  have hBudget : 24 * columns.length + 10 = 1 + (9 * columns.length + (15 * columns.length + 9)) := by omega
  unfold evalWithin
  rw [hBudget, evalConfigWithin_add, eval_start, PMF.pure_bind,
    evalConfigWithin_add, ← List.append_nil (interleave columns), eval_columns_context, PMF.pure_bind]
  simp only [List.append_nil]
  exact eval_tail (BinaryAddition.carryOut false (operands columns))
    (BinarySubtraction.borrowOut false (sumPairs false columns)) columns
    (BinarySubtraction.differenceBits false (sumPairs false columns))
    (by simp [sumPairs_length])

private theorem reducedBits_length (columns : List Column) :
    (reducedBits columns).length = columns.length := by
  unfold reducedBits
  split <;> simp [lowerBits_length, operands, sumPairs_length]

/-- Complete bit columns always produce a result of the same width, even
when the numeric preconditions of modular correctness do not hold. This
structural property supports native caller termination on malformed data. -/
theorem complete_output (columns : List Column) :
    ∃ output : List Bool, output.length = columns.length ∧
    evalWithin program (interleave columns) (24 * columns.length + 10) =
      PMF.pure (some output) :=
  ⟨reducedBits columns, reducedBits_length columns, eval_interleave columns⟩

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private theorem reducedBits_value (columns : List Column)
    (hFirst : Binary.value ((operands columns).map Prod.fst) < Binary.value (moduli columns))
    (hSecond : Binary.value ((operands columns).map Prod.snd) < Binary.value (moduli columns))
    (hWidth : Binary.value ((operands columns).map Prod.fst) +
      Binary.value ((operands columns).map Prod.snd) < 2 ^ columns.length) :
    Binary.value (reducedBits columns) =
      (Binary.value ((operands columns).map Prod.fst) +
        Binary.value ((operands columns).map Prod.snd)) % Binary.value (moduli columns) := by
  have hSum := sumPairs_value false columns
  have hCarry : BinaryAddition.carryOut false (operands columns) = false := by
    cases h : BinaryAddition.carryOut false (operands columns) with
    | false => rfl
    | true =>
        simp only [h, Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.add_zero] at hSum
        omega
  rw [hCarry] at hSum
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hSum
  have hInvariant := BinarySubtraction.differenceBits_invariant false (sumPairs false columns)
  simp only [sumPairs_snd, sumPairs_length, Bool.toNat_false, Nat.add_zero] at hInvariant
  have hDifference := Binary.value_lt (BinarySubtraction.differenceBits false (sumPairs false columns))
  simp only [BinarySubtraction.differenceBits_length, sumPairs_length] at hDifference
  unfold reducedBits
  cases hBorrow : BinarySubtraction.borrowOut false (sumPairs false columns) with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [hBorrow, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hInvariant
      have hGe : Binary.value (moduli columns) ≤
          Binary.value ((operands columns).map Prod.fst) +
            Binary.value ((operands columns).map Prod.snd) := by omega
      rw [Nat.mod_eq_sub_mod hGe, Nat.mod_eq_of_lt (by omega)]
      omega
  | true =>
      simp only [↓reduceIte]
      simp only [hBorrow, Bool.toNat_true, Nat.mul_one] at hInvariant
      rw [Nat.mod_eq_of_lt (by omega)]
      simpa [sumPairs_fst] using hSum

/-- The actual finite program returns the canonical fixed-width code of the
modular sum. The width must accommodate the sum before conditional reduction. -/
theorem eval_add_mod_encoded (columns : List Column)
    (hFirst : Binary.value ((operands columns).map Prod.fst) < Binary.value (moduli columns))
    (hSecond : Binary.value ((operands columns).map Prod.snd) < Binary.value (moduli columns))
    (hWidth : Binary.value ((operands columns).map Prod.fst) +
      Binary.value ((operands columns).map Prod.snd) < 2 ^ columns.length) :
    evalWithin program (interleave columns) (24 * columns.length + 10) =
      PMF.pure (some (Binary.encode columns.length
        ((Binary.value ((operands columns).map Prod.fst) +
          Binary.value ((operands columns).map Prod.snd)) % Binary.value (moduli columns)))) := by
  rw [eval_interleave]
  have h := Binary.encode_value (reducedBits columns)
  rw [reducedBits_length, reducedBits_value columns hFirst hSecond hWidth] at h
  rw [h]

private def invalid (before written : List (Option Bool)) : Configuration :=
  { pc := 268, inputTape := { left := before }, outputTape := { left := written }, halted := true }

private theorem eval_short_one (carry borrow first : Bool)
    (before written : List (Option Bool)) :
    evalConfigWithin program (state carry borrow before [first] written) 5 =
      PMF.pure (invalid (some first :: before) written) := by
  cases carry <;> cases borrow <;> cases first <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address, invalid,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

set_option maxHeartbeats 600000 in
private theorem eval_short_two (carry borrow first second : Bool)
    (before written : List (Option Bool)) :
    evalConfigWithin program (state carry borrow before [first, second] written) 7 =
      PMF.pure (invalid (some second :: some first :: before) written) := by
  cases carry <;> cases borrow <;> cases first <;> cases second <;>
    simp [evalConfigWithin, stepPMF, next, program, state, address, invalid,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem decompose_input (input : List Bool) :
    ∃ columns : List Column, ∃ trailing : List Bool,
      input = interleave columns ++ trailing ∧ trailing.length < 3 := by
  match input with
  | [] => exact ⟨[], [], rfl, by decide⟩
  | [first] => exact ⟨[], [first], rfl, by simp⟩
  | [first, second] => exact ⟨[], [first, second], rfl, by simp⟩
  | first :: second :: modulus :: rest =>
      obtain ⟨columns, trailing, h, hLength⟩ := decompose_input rest
      exact ⟨((first, second), modulus) :: columns, trailing, by simp [interleave, h], hLength⟩
termination_by input.length

private theorem interleave_length (columns : List Column) :
    (interleave columns).length = 3 * columns.length := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp [interleave, ih]; omega

/-- Every finite raw input halts, including incomplete three-bit columns.
The bound charges both scans and all rewinding on the underflow path. -/
theorem haltsWithin (input : List Bool) : HaltsWithin program input (24 * (input.length + 1)) := by
  obtain ⟨columns, trailing, hInput, hLength⟩ := decompose_input input
  subst input
  cases trailing with
  | nil =>
      simp only [List.append_nil]
      apply (haltsWithin_of_no_timeout_support program (interleave columns)
        (24 * columns.length + 10) (by rw [eval_interleave]; simp)).mono
      simp [interleave_length]; omega
  | cons first rest =>
      cases rest with
      | nil =>
          have hEval : evalWithin program (interleave columns ++ [first]) (9 * columns.length + 6) =
              PMF.pure (some (invalid
                (some first :: (interleave columns).reverse.map some)
                ((BinarySubtraction.differenceBits false (sumPairs false columns)).reverse.map some)).outputBits) := by
            have hBudget : 9 * columns.length + 6 = 1 + (9 * columns.length + 5) := by omega
            unfold evalWithin
            rw [hBudget, evalConfigWithin_add, eval_start, PMF.pure_bind,
              evalConfigWithin_add, eval_columns_context, PMF.pure_bind, eval_short_one, PMF.pure_map]
            simp [invalid]
          apply (haltsWithin_of_no_timeout_support program _ (9 * columns.length + 6)
            (by rw [hEval]; simp)).mono
          simp [interleave_length]; omega
      | cons second rest =>
          have hRest : rest = [] := by
            cases rest with
            | nil => rfl
            | cons bit remaining => simp only [List.length_cons] at hLength; omega
          subst rest
          have hEval : evalWithin program (interleave columns ++ [first, second]) (9 * columns.length + 8) =
              PMF.pure (some (invalid
                (some second :: some first :: (interleave columns).reverse.map some)
                ((BinarySubtraction.differenceBits false (sumPairs false columns)).reverse.map some)).outputBits) := by
            have hBudget : 9 * columns.length + 8 = 1 + (9 * columns.length + 7) := by omega
            unfold evalWithin
            rw [hBudget, evalConfigWithin_add, eval_start, PMF.pure_bind,
              evalConfigWithin_add, eval_columns_context, PMF.pure_bind, eval_short_two, PMF.pure_map]
            simp [invalid]
          apply (haltsWithin_of_no_timeout_support program _ (9 * columns.length + 8)
            (by rw [hEval]; simp)).mono
          simp [interleave_length]; omega

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 24 * (length + 1),
    (PolynomiallyBounded.const 24).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

end Machine.BinaryModularAddition
