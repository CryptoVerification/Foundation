import Foundation.Crypto.Semantics.Machine.NativeFixedComponent
import Foundation.Crypto.Semantics.Machine.Encoding

/-! Fixed native transfer of a delimited bitstring, erasing every consumed
source cell. The static flag selects preservation of the delimiter encoding
or decoding to raw bits. Both variants have the same 12n+6 time bound and
retain arbitrary saved destination bits and an arbitrary source suffix. -/
namespace Machine.NativeDelimitedTransfer
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

structure Input where
  consumed : Nat := 0
  prefixBits : List Bool := []
  data : List Bool
  suffix : List Bool := []

def source (consumed : Nat) (remaining : List Bool) : Tape :=
  {Tape.ofBits remaining with left := List.replicate consumed none}

def destination (bits : List Bool) : Tape := {left := bits.reverse.map some}

def emit (keepFlags : Bool) (data : List Bool) : List Bool :=
  if keepFlags then FiniteBitEncoding.delimit data else data

def code (keepFlags : Bool) : Program :=
  [.branch .input 20 16 1,
   (if keepFlags then .write .output true else .jump 2),
   (if keepFlags then .moveRight .output else .jump 3),
   .erase .input, .moveRight .input, .branch .input 20 6 9,
   .write .output false, .jump 12, .halt,
   .write .output true, .jump 12, .halt,
   .moveRight .output, .erase .input, .moveRight .input, .jump 0,
   (if keepFlags then .write .output false else .jump 17),
   (if keepFlags then .moveRight .output else .jump 18),
   .erase .input, .moveRight .input, .halt]

def initial (input : Input) : Configuration :=
  {inputTape := source input.consumed (FiniteBitEncoding.delimit input.data ++ input.suffix),
   outputTape := destination input.prefixBits}

def finish (keepFlags : Bool) (input : Input) : Configuration :=
  {pc := 20,
   inputTape := source (input.consumed + 2 * input.data.length + 1) input.suffix,
   outputTape := destination (input.prefixBits ++ emit keepFlags input.data), halted := true}

def nextInput (keepFlags : Bool) (input : Input) (bit : Bool) (rest : List Bool) : Input :=
  {consumed := input.consumed + 2,
   prefixBits := input.prefixBits ++ (if keepFlags then [true, bit] else [bit]), data := rest, suffix := input.suffix}

theorem iteration (keepFlags : Bool) (input : Input) (bit : Bool) (rest : List Bool) :
    evalConfigWithin (code keepFlags) (initial {input with data := bit :: rest}) 12 =
      PMF.pure (initial (nextInput keepFlags input bit rest)) := by
  cases keepFlags <;> cases bit <;> cases rest <;>
    simp [code, initial, nextInput, source, destination, FiniteBitEncoding.delimit, evalConfigWithin,
      stepPMF, next, Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.ofBits, Tape.write, Tape.moveRight, List.reverse_append, List.replicate_succ, Nat.add_assoc]

theorem run (keepFlags : Bool) (input : Input) :
    evalConfigWithin (code keepFlags) (initial input) (12 * input.data.length + 6) =
      PMF.pure (finish keepFlags input) := by
  obtain ⟨consumed, prefixBits, data, suffix⟩ := input
  induction data generalizing consumed prefixBits with
  | nil =>
      cases keepFlags <;> cases suffix <;>
        simp [code, initial, finish, source, destination, emit, FiniteBitEncoding.delimit,
          evalConfigWithin, stepPMF, next, Instruction.next, Configuration.tape,
          Configuration.updateTape, Configuration.advance, Tape.ofBits, Tape.write,
          Tape.moveRight, List.reverse_append, List.replicate_succ]
  | cons bit rest ih =>
      rw [show 12 * ({consumed := consumed, prefixBits := prefixBits, data := bit :: rest, suffix := suffix} : Input).data.length + 6 =
        12 + (12 * rest.length + 6) by simp; omega,
        evalConfigWithin_add, iteration keepFlags ⟨consumed, prefixBits, rest, suffix⟩ bit rest, PMF.pure_bind]
      change evalConfigWithin (code keepFlags) (initial (nextInput keepFlags ⟨consumed, prefixBits, rest, suffix⟩ bit rest))
        (12 * rest.length + 6) = _
      rw [show nextInput keepFlags ⟨consumed, prefixBits, rest, suffix⟩ bit rest =
        ⟨consumed + 2, prefixBits ++ (if keepFlags then [true, bit] else [bit]), rest, suffix⟩ from rfl, ih]
      congr 1
      cases keepFlags <;> simp [finish, emit, FiniteBitEncoding.delimit, List.append_assoc]
      all_goals congr 1 <;> omega

noncomputable def component (keepFlags : Bool) : NativeComponent Input Configuration :=
  NativeComponent.ofFixed (code keepFlags) initial (fun _ output => output)
    (fun input => PMF.pure (finish keepFlags input)) (fun input => 12 * input.data.length + 6)
    (fun input => by simpa only [PMF.pure_map] using run keepFlags input)
    (by cases keepFlags <;> decide) (fun _ => by change 0 < 21; decide) (fun _ => rfl)
    (by intro input output h; rw [PMF.mem_support_pure_iff] at h; subst output; rfl)

end Machine.NativeDelimitedTransfer
