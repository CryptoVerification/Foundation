import Foundation.Constructions.Hash.NativeSimulatorPredecessorLookup
import Foundation.Crypto.Semantics.Oracle.BackwardFieldCopy
import Foundation.Crypto.Semantics.Machine.ListEncoding
import Foundation.Crypto.Semantics.Oracle.CodePrefixExecution

/-! Extract the selected data key by actual input reads and movements. The
payload's escaped field is prepended to the recovered message encoding; the
previous digest is decoded into the next raw target. Obsolete target cells are
scratch space. The original private table is never overwritten. -/
namespace Foundation.Hash.Native.SimulatorPredecessorExtract
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def prePayload (previous : Bits n) : List Bool :=
  true :: SimulatorPredecessorFilter.escaped previous.toList ++ [true, false]

def payload (block : Bits κ) : List Bool := FiniteBitEncoding.delimit block.toList

theorem entry_layout (previous target : Bits n) (block : Bits κ) :
    SimulatorLookup.entryBits ((previous, (false, block)), target) =
      prePayload previous ++ payload block ++ target.toList := by
  simp [SimulatorLookup.entryBits, compressionPacket, prePayload, payload,
    SimulatorPredecessorFilter.delimit_append, FiniteBitEncoding.delimit, List.append_assoc]

theorem escaped_source (bits : List Bool) :
    BackwardFieldCopy.sourceCells true bits.reverse =
      (SimulatorPredecessorFilter.escaped bits).reverse.map some := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      rw [List.reverse_cons, BackwardFieldCopy.sourceCells_append, ih]
      simp [SimulatorPredecessorFilter.escaped, BackwardFieldCopy.sourceCells,
        BackwardFieldCopy.chunk, List.map_append]

theorem escaped_source_reverse (bits : List Bool) :
    (BackwardFieldCopy.sourceCells true bits.reverse).reverse =
      (SimulatorPredecessorFilter.escaped bits).map some := by
  rw [escaped_source, ← List.map_reverse, List.reverse_reverse]

def prelude (n : Nat) : Code := StraightLine.code (List.replicate (n + 1) (.left .input))
def payloadCode (κ : Nat) : Code := BackwardFieldCopy.code false 0 (2 * κ + 1) 0

def betweenActions : List StraightLine.Action :=
  [.left .input, .left .input, .write .output (some true), .left .output,
   .write .output none, .left .output]

def betweenCode : Code := StraightLine.code betweenActions
def previousCode (n : Nat) : Code := BackwardFieldCopy.code true 0 n 0
def finalCode : Code := [.native (.moveRight .output)]

def code (n κ : Nat) (tail : Code) : Code :=
  CodeRelocation.host (prelude n) (CodeRelocation.host (payloadCode κ)
    (CodeRelocation.host betweenCode (CodeRelocation.host (previousCode n)
      (CodeRelocation.host finalCode tail))))

theorem payload_length (block : Bits κ) : (payload block).length = 2 * κ + 1 := by
  simp [payload, FiniteBitEncoding.delimit_length]

theorem code_length (n κ : Nat) (tail : Code) : (code n κ tail).length = 9 * n + 14 * κ + 15 + tail.length := by
  simp only [code, CodeRelocation.code_length, prelude, payloadCode, previousCode, betweenCode,
    StraightLine.code, List.length_map, List.length_replicate, BackwardFieldCopy.code_length,
    BackwardFieldCopy.cellWidth, BackwardFieldCopy.stride, Bool.false_eq_true, ↓reduceIte,
    betweenActions, finalCode, List.length_cons, List.length_nil]
  omega

theorem code_native (n κ : Nat) (tail : Code)
    (ht : ∀ op ∈ tail, ∃ native, op = .native native) :
    ∀ op ∈ code n κ tail, ∃ native, op = .native native := by
  have straight (actions : List StraightLine.Action) :
      ∀ op ∈ StraightLine.code actions, ∃ native, op = .native native := by
    intro op hm
    obtain ⟨action, _, rfl⟩ := List.mem_map.mp hm
    exact ⟨_, rfl⟩
  apply CodeRelocation.host_native
  · exact straight _
  apply CodeRelocation.host_native
  · exact BackwardFieldCopy.code_native _ _ _ _
  apply CodeRelocation.host_native
  · exact straight _
  apply CodeRelocation.host_native
  · exact BackwardFieldCopy.code_native _ _ _ _
  apply CodeRelocation.host_native
  · intro op hm; simp only [finalCode, List.mem_singleton] at hm; exact ⟨_, hm⟩
  · exact ht

def sourceAfter (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest : List (Option Bool)) : Tape :=
  FixedWidthCopy.backwardFrontier (target.toList.map some ++ next :: rest)
    ((payload block).reverse.map some ++ (prePayload previous).reverse.map some ++ beforeInput)

def scratch (target : Bits n) (suffix : List (Option Bool)) : Tape :=
  { left := target.toList.reverse.map some ++ [none], current := some true, right := suffix }

/-- From the found response cursor, move left to the payload field's final false
delimiter. The response and next record are pushed back without any writes. -/
theorem prelude_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (prelude n) tail) oracle) (n + 1)
      (⟨state, .running { inputTape := { left := (SimulatorLookup.entryBits ((previous, (false, block)), target)).reverse.map some ++ beforeInput, current := next, right := rest }, outputTape := scratch target suffix }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (prelude n).length
        (⟨state, .running { inputTape := sourceAfter previous target block beforeInput next rest, outputTape := scratch target suffix }, trace⟩ : Configuration State)) := by
  let cells := next :: target.toList.reverse.map some
  let left := (payload block).reverse.map some ++ (prePayload previous).reverse.map some ++ beforeInput
  have hl : cells.length = n + 1 := by simp [cells]
  have hs : ({ left := (SimulatorLookup.entryBits ((previous, (false, block)), target)).reverse.map some ++ beforeInput, current := next, right := rest } : Tape) =
      FixedWidthCopy.backwardFrontier rest (cells ++ left) := by
    simp [cells, left, entry_layout, List.reverse_append, List.map_append, List.append_assoc,
      FixedWidthCopy.backwardFrontier]
  have h := StraightLine.public_run oracle state trace []
    (tail.map (CodeRelocation.instruction (prelude n).length)) (List.replicate (n + 1) (.left .input))
    { inputTape := { left := (SimulatorLookup.entryBits ((previous, (false, block)), target)).reverse.map some ++ beforeInput, current := next, right := rest }, outputTape := scratch target suffix }
    rfl rfl
  simp only [List.nil_append, List.length_replicate] at h
  rw [hs] at h
  have hm := BackwardFieldCopy.advance_input cells rest left
    ({ outputTape := scratch target suffix } : Machine.Configuration)
  rw [hl] at hm
  rw [hm] at h
  have hr : cells.reverse ++ rest = target.toList.map some ++ next :: rest := by
    simp [cells, List.reverse_cons, ← List.map_reverse, List.append_assoc]
  rw [hr] at h
  rw [← hs] at h
  simpa only [prelude, CodeRelocation.host, CodeRelocation.frame, CodeRelocation.control,
    Machine.Configuration.rebasePc, NativeCode.frame, StraightLine.code, List.length_map,
    List.length_replicate, sourceAfter, left, Nat.zero_add, Nat.add_zero] using h

/-- Sequential fall-through preserves all physical state; relocation only changes pc. -/
theorem seq_run (oracle : BitOracle State) (first second : Code) (t₁ t₂ : Nat)
    (source middle finish : Configuration State)
    (h₁ : TimedExecution.eval (Reification.timedStep (CodeRelocation.host first second) oracle) t₁ source =
      PMF.pure (CodeRelocation.frame first.length middle))
    (h₂ : TimedExecution.eval (Reification.timedStep second oracle) t₂ middle = PMF.pure finish) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host first second) oracle) (t₁ + t₂) source =
      PMF.pure (CodeRelocation.frame first.length finish) := by
  rw [TimedExecution.eval_add, h₁, PMF.pure_bind, CodeRelocation.eval, h₂, PMF.pure_map]

def afterPayload (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.backwardFrontier
      ((payload block).map some ++ target.toList.map some ++ next :: rest)
      ((prePayload previous).reverse.map some ++ beforeInput),
    outputTape := BackwardFieldCopy.writeLeft ((payload block).reverse.map some) (scratch target suffix) }

theorem payload_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (payloadCode κ) tail) oracle) (5 * (2 * κ + 1))
      (⟨state, .running { inputTape := sourceAfter previous target block beforeInput next rest, outputTape := scratch target suffix }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (payloadCode κ).length
        (NativeCode.frame state trace (afterPayload previous target block beforeInput next rest suffix))) := by
  have h := BackwardFieldCopy.run_host oracle state trace tail false
    (target.toList.map some ++ next :: rest) ((prePayload previous).reverse.map some ++ beforeInput)
    (scratch target suffix) (payload block).reverse
  simpa only [BackwardFieldCopy.raw_sourceCells, BackwardFieldCopy.cellSteps,
    BackwardFieldCopy.stride, Bool.false_eq_true, ↓reduceIte, List.length_reverse, payload_length,
    ← List.map_reverse, List.reverse_reverse, sourceAfter, payloadCode, afterPayload,
    NativeCode.frame, List.append_assoc] using h

def afterBetween (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.backwardFrontier
      ([some true, some false] ++ (payload block).map some ++ target.toList.map some ++ next :: rest)
      ((SimulatorPredecessorFilter.escaped previous.toList).reverse.map some ++ some true :: beforeInput),
    outputTape := BackwardFieldCopy.writeLeft [some true, none]
      (afterPayload previous target block beforeInput next rest suffix).outputTape }

theorem between_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host betweenCode tail) oracle) 6
      (NativeCode.frame state trace (afterPayload previous target block beforeInput next rest suffix)) =
      PMF.pure (CodeRelocation.frame betweenCode.length
        (NativeCode.frame state trace (afterBetween previous target block beforeInput next rest suffix))) := by
  have h := StraightLine.public_run oracle state trace []
    (tail.map (CodeRelocation.instruction betweenCode.length)) betweenActions
    (afterPayload previous target block beforeInput next rest suffix) rfl rfl
  simpa [CodeRelocation.host, CodeRelocation.frame, CodeRelocation.control,
    Machine.Configuration.rebasePc, NativeCode.frame, betweenCode, betweenActions,
    StraightLine.code, StraightLine.execute, StraightLine.apply, Machine.Configuration.updateTape,
    Machine.Configuration.advance, afterPayload, afterBetween, prePayload,
    List.reverse_append, List.map_append, List.append_assoc,
    BackwardFieldCopy.backward_move, BackwardFieldCopy.writeLeft] using h

def afterPrevious (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.backwardFrontier
      ((SimulatorPredecessorFilter.escaped previous.toList).map some ++
        [some true, some false] ++ (payload block).map some ++ target.toList.map some ++ next :: rest)
      (some true :: beforeInput),
    outputTape := BackwardFieldCopy.writeLeft (previous.toList.reverse.map some)
      (afterBetween previous target block beforeInput next rest suffix).outputTape }

theorem previous_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (previousCode n) tail) oracle) (6 * n)
      (NativeCode.frame state trace (afterBetween previous target block beforeInput next rest suffix)) =
      PMF.pure (CodeRelocation.frame (previousCode n).length
        (NativeCode.frame state trace (afterPrevious previous target block beforeInput next rest suffix))) := by
  have h := BackwardFieldCopy.run_host oracle state trace tail true
    ([some true, some false] ++ (payload block).map some ++ target.toList.map some ++ next :: rest)
    (some true :: beforeInput) (afterBetween previous target block beforeInput next rest suffix).outputTape
    previous.toList.reverse
  simpa [escaped_source, BackwardFieldCopy.cellSteps,
    BackwardFieldCopy.stride, ↓reduceIte, List.length_reverse, Bits.length_toList,
    List.reverse_reverse,
    previousCode, afterBetween, afterPrevious, NativeCode.frame, List.append_assoc] using h

def finish (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) : Machine.Configuration :=
  { inputTape := (afterPrevious previous target block beforeInput next rest suffix).inputTape,
    outputTape := (afterPrevious previous target block beforeInput next rest suffix).outputTape.moveRight }

/-- The cursor returns to the selected record marker; every encoded input cell
is retained in its original order. -/
theorem finish_input (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) :
    (finish previous target block beforeInput next rest suffix).inputTape =
      { left := beforeInput, current := some true,
        right := (SimulatorPredecessorFilter.escaped previous.toList).map some ++
          [some true, some false] ++ (payload block).map some ++ target.toList.map some ++ next :: rest } := rfl

theorem final_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (machine : Machine.Configuration) (hp : machine.pc = 0)
    (hh : machine.halted = false) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host finalCode tail) oracle) 1
      (NativeCode.frame state trace machine) =
      PMF.pure (CodeRelocation.frame finalCode.length
        (NativeCode.frame state trace { machine with pc := 0, outputTape := machine.outputTape.moveRight })) := by
  have h := StraightLine.public_run oracle state trace []
    (tail.map (CodeRelocation.instruction finalCode.length)) [.right .output] machine hp hh
  simpa [finalCode, CodeRelocation.host, CodeRelocation.frame, CodeRelocation.control,
    Machine.Configuration.rebasePc, NativeCode.frame, StraightLine.code, StraightLine.execute,
    StraightLine.instruction, StraightLine.apply, Machine.Configuration.advance, Machine.Configuration.updateTape, hp, hh] using h

/-- Exact fall-through into the supplied continuation, with the original table,
external oracle state, and complete old trace retained. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) (tail : Code) :
    TimedExecution.eval (Reification.timedStep (code n κ tail) oracle) (7 * n + 10 * κ + 13)
      (⟨state, .running { inputTape := { left := (SimulatorLookup.entryBits ((previous, (false, block)), target)).reverse.map some ++ beforeInput, current := next, right := rest }, outputTape := scratch target suffix }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (code n κ []).length
        (NativeCode.frame state trace (finish previous target block beforeInput next rest suffix))) := by
  have hf := final_run oracle state trace
    (afterPrevious previous target block beforeInput next rest suffix) rfl rfl tail
  have hp := seq_run oracle (previousCode n) (CodeRelocation.host finalCode tail) _ _ _ _ _
    (previous_run oracle state trace previous target block beforeInput next rest suffix _) hf
  have hb := seq_run oracle betweenCode
    (CodeRelocation.host (previousCode n) (CodeRelocation.host finalCode tail)) _ _ _ _ _
    (between_run oracle state trace previous target block beforeInput next rest suffix _) hp
  have hpl := seq_run oracle (payloadCode κ)
    (CodeRelocation.host betweenCode (CodeRelocation.host (previousCode n) (CodeRelocation.host finalCode tail))) _ _ _ _ _
    (payload_run oracle state trace previous target block beforeInput next rest suffix _) hb
  have h := seq_run oracle (prelude n) _ _ _ _ _ _
    (prelude_run oracle state trace previous target block beforeInput next rest suffix _) hpl
  have ht : n + 1 + (5 * (2 * κ + 1) + (6 + (6 * n + 1))) = 7 * n + 10 * κ + 13 := by omega
  simpa only [ht, code, finish, afterPrevious, CodeRelocation.frame, CodeRelocation.control,
    Machine.Configuration.rebasePc, NativeCode.frame, CodeRelocation.code_length,
    List.length_nil, Nat.add_zero, Nat.add_assoc] using h

/-- Obsolete raw target cells are all overwritten by real writes. No assumed
fresh allocation is needed, even when either fixed field has width zero. -/
theorem finish_output (previous target : Bits n) (block : Bits κ)
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest suffix : List (Option Bool)) :
    (finish previous target block beforeInput next rest suffix).outputTape =
      FixedWidthCopy.frontier [none]
        (previous.toList.map some ++ none :: some true :: (payload block).map some ++ suffix) := by
  let cells := (payload block).reverse.map some ++ [some true, none] ++ previous.toList.reverse.map some
  have hl : (target.toList.reverse.map some ++ [none]).length < cells.length := by
    simp [cells, payload_length]
    omega
  have hw := BackwardFieldCopy.writeLeft_finish cells
    (target.toList.reverse.map some ++ [none]) suffix (some true) hl
  simp only [finish, afterPrevious, afterBetween, afterPayload, scratch,
    ← BackwardFieldCopy.writeLeft_append]
  rw [hw]
  cases he : previous.toList <;>
    simp [cells, he, List.reverse_append, ← List.map_reverse, List.append_assoc,
      Tape.moveRight, FixedWidthCopy.frontier, ResponseLoading.fromCells]

end Foundation.Hash.Native.SimulatorPredecessorExtract
