import Foundation.Constructions.Symmetric.EncryptThenMAC.TableMAC
import Foundation.Constructions.Symmetric.EncryptThenMAC.OneBitEncryption
import Foundation.Crypto.Semantics.Machine.SubroutineProbability

/-! Native response authentication for the privacy reduction. An input packet
contains an optional ciphertext followed by the private interleaved table key.
Failure bypasses signing. Success copies the ciphertext and invokes the actual
finite signing code, retaining both physical tapes and charging the return. -/
namespace Foundation.Symmetric.EncryptThenMAC.AuthenticateResponse
open Foundation.Probability Machine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

-- Only addresses in this preamble are absolute caller addresses.
def preamble : Program :=
  [.branch .input 12 12 1,
   .write .output true, .moveRight .output, .moveRight .input,
   .branch .input 12 5 7,
   .write .output false, .jump 9, .write .output true, .jump 9,
   .moveRight .output, .jump 14, .halt,
   .write .output false, .halt]

def code : Program :=
  Program.withSubroutine preamble TableMAC.Native.signCode [.halt]
    (preamble.length + TableMAC.Native.signCode.length + 1)

abbrev beforeSign (ciphertext : Bool) (rows : List Bool) : Configuration :=
  Machine.OneTimePad.state [true] [true, ciphertext] (ciphertext :: rows)

theorem success_prefix (ciphertext : Bool) (rows : List Bool) :
    evalConfigWithin code (Configuration.initial (true :: ciphertext :: rows)) 9 =
      PMF.pure ((beforeSign ciphertext rows).rebasePc preamble.length) := by
  cases ciphertext <;> cases rows <;>
    simp [evalConfigWithin, stepPMF, next, code, preamble, Program.withSubroutine,
      beforeSign, Machine.OneTimePad.state, Configuration.initial, Configuration.rebasePc,
      Tape.ofBits, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write, Tape.moveRight]

/-- The signer returns with the complete authenticated packet already on the
output tape; no whole-string append is hidden in a single machine step. -/
theorem success_run {width : Nat} (key : TableMAC.Key width) (ciphertext : Bool) :
    evalWithin code
      (true :: ciphertext :: Machine.OneTimePad.pairInput key.1.toList key.2.toList)
      (8 * width + 14) =
      PMF.pure (some ([true, ciphertext] ++ (TableMAC.sign key ciphertext).toList)) := by
  let start := beforeSign ciphertext (Machine.OneTimePad.pairInput key.1.toList key.2.toList)
  have hRun := TableMAC.Native.sign_from_run key ciphertext [true] [true, ciphertext]
  have hHalts : ∀ finish, PaddedRunsFor TableMAC.Native.signCode start finish (8 * width + 4) →
      finish.halted = true := by
    intro finish h
    have hm := (mem_support_evalConfigWithin_iff _ _ _ _).mpr h
    rw [hRun, PMF.mem_support_pure_iff] at hm
    subst finish
    rfl
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt preamble TableMAC.Native.signCode
    start (by simp [start, beforeSign, Machine.OneTimePad.state, TableMAC.Native.signCode])
    rfl (8 * width + 4) hHalts
  rw [evalWithin, show 8 * width + 14 = 9 + ((8 * width + 4) + 1) by omega,
    evalConfigWithin_add, success_prefix, PMF.pure_bind]
  change (evalConfigWithin code (start.rebasePc preamble.length) ((8 * width + 4) + 1)).map _ = _
  unfold code
  dsimp only at hCall
  rw [hCall, hRun, PMF.map_comp, PMF.pure_map]
  simp [TableMAC.Native.finish, Machine.OneTimePad.finish, Machine.OneTimePad.state,
    Configuration.outputBits, Tape.bits]

private theorem halted_padding (p : Program) (c : Configuration) (h : c.halted = true) (fuel : Nat) :
    evalConfigWithin p c fuel = PMF.pure c := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [evalConfigWithin, ih, stepPMF, next, h]

/-- A failed encryption never enters the signer or reads its private rows. -/
theorem failure_run (rows : List Bool) (extra : Nat) :
    evalWithin code (false :: rows) (3 + extra) = PMF.pure (some [false]) := by
  have hPrefix : evalConfigWithin code (Configuration.initial (false :: rows)) 3 =
      PMF.pure { (Configuration.initial (false :: rows)) with
        pc := 13, halted := true, outputTape := { current := some false } } := by
    simp [evalConfigWithin, stepPMF, next, code, preamble, Program.withSubroutine,
      Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write]
  rw [evalWithin, evalConfigWithin_add, hPrefix, PMF.pure_bind, halted_padding _ _ rfl, PMF.pure_map]
  rfl

def input {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) : List Bool :=
  (match ciphertext with | none => [false] | some bit => [true, bit]) ++
    Machine.OneTimePad.pairInput key.1.toList key.2.toList

def encode {width : Nat} : Option (Bool × Bits width) → List Bool
  | none => [false]
  | some (ciphertext, tag) => [true, ciphertext] ++ tag.toList

/-- The general call law also covers incomplete key rows. Complete
configurations ensure the call preserves the caller's retained cells. -/
theorem all_success_run (ciphertext : Bool) (rows : List Bool) :
    evalWithin code (true :: ciphertext :: rows) (4 * rows.length + 16) =
      PMF.pure (some ([true, ciphertext] ++ TableMAC.Native.selectedPairs ciphertext rows)) := by
  let start := beforeSign ciphertext rows
  have hRun := TableMAC.Native.all_from_run ciphertext [true] [true, ciphertext] rows
  have hHalts : ∀ finish, PaddedRunsFor TableMAC.Native.signCode start finish (4 * rows.length + 6) →
      finish.halted = true := by
    intro finish h
    have hm := (mem_support_evalConfigWithin_iff _ _ _ _).mpr h
    rw [hRun, PMF.mem_support_pure_iff] at hm
    subst finish
    rfl
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt preamble TableMAC.Native.signCode
    start (by simp [start, beforeSign, Machine.OneTimePad.state, TableMAC.Native.signCode])
    rfl (4 * rows.length + 6) hHalts
  rw [evalWithin, show 4 * rows.length + 16 = 9 + ((4 * rows.length + 6) + 1) by omega,
    evalConfigWithin_add, success_prefix, PMF.pure_bind]
  change (evalConfigWithin code (start.rebasePc preamble.length) ((4 * rows.length + 6) + 1)).map _ = _
  unfold code
  dsimp only at hCall
  rw [hCall, hRun, PMF.map_comp, PMF.pure_map]
  simp [TableMAC.Native.finish, Machine.OneTimePad.finish, Machine.OneTimePad.state,
    Configuration.outputBits, Tape.bits]

/-- The finite handler has an all-input, all-branch CPU bound. Semantic
correctness is claimed separately for well-formed ciphertext/key packets. -/
theorem all_halts (raw : List Bool) : HaltsWithin code raw (4 * raw.length + 8) := by
  apply haltsWithin_of_no_timeout_support
  cases raw with
  | nil =>
      simp [evalWithin, evalConfigWithin, stepPMF, next, code, preamble, Program.withSubroutine,
        Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape,
        Configuration.updateTape, Configuration.advance, Tape.write, PMF.pure_map,
        Configuration.outputBits, Tape.bits]
  | cons flag rest =>
      cases flag with
      | false =>
          have h := failure_run rest (4 * rest.length + 9)
          rw [show 3 + (4 * rest.length + 9) = 4 * (false :: rest).length + 8 by simp; omega] at h
          rw [h]
          simp
      | true =>
          cases rest with
          | nil =>
              simp [evalWithin, evalConfigWithin, stepPMF, next, code, preamble, Program.withSubroutine,
                Configuration.initial, Tape.ofBits, Instruction.next, Configuration.tape,
                Configuration.updateTape, Configuration.advance, Tape.write, Tape.moveRight,
                PMF.pure_map, Configuration.outputBits, Tape.bits]
          | cons ciphertext rows =>
              rw [show 4 * (true :: ciphertext :: rows).length + 8 = 4 * rows.length + 16 by simp; omega,
                all_success_run]
              simp

def boundedProgram : CryptoLogic.BoundedProgram where
  program := code
  budget := fun m => 4 * m + 8
  polynomial := ((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 8)
  halts := all_halts

/-- The response code implements the authenticate function in the semantic
privacy reduction, for the exact concrete authentication scheme. -/
theorem realizes_authenticate (width : Nat → Nat) (n : Nat)
    (key : TableMAC.Key (width n)) (ciphertext : Option Bool) :
    evalWithin code (input key ciphertext) (8 * width n + 14) =
      PMF.pure (some (encode (ciphertext.map (fun c => (c, (TableMAC.scheme width).sign n key c))))) := by
  cases ciphertext with
  | none =>
      have h := failure_run (Machine.OneTimePad.pairInput key.1.toList key.2.toList) (8 * width n + 11)
      rw [show 3 + (8 * width n + 11) = 8 * width n + 14 by omega] at h
      simpa [input, encode] using h
  | some bit => simpa [input, encode, TableMAC.scheme] using success_run key bit

theorem halts_typed {width : Nat} (key : TableMAC.Key width) (ciphertext : Option Bool) :
    HaltsWithin code (input key ciphertext) (8 * width + 14) := by
  apply haltsWithin_of_no_timeout_support
  have h := realizes_authenticate (fun _ => width) 0 key ciphertext
  rw [h]
  simp

/-- This is the exact semantic response adapter used by the privacy
reduction for the concrete one-bit encryption and table authentication. -/
theorem realizes_privacy_response (width : Nat → Nat) (n : Nat)
    (key : TableMAC.Key (width n)) (ciphertext : Option Bool) :
    evalWithin code (input key ciphertext) (8 * width n + 14) =
      PMF.pure (some (encode (authenticate OneBitEncryption.scheme (TableMAC.scheme width)
        n key ciphertext))) := realizes_authenticate width n key ciphertext

theorem profile_polynomial {width : Nat → Nat} (h : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => 8 * width n + 14) :=
  ((PolynomiallyBounded.const 8).mul h).add (PolynomiallyBounded.const 14)

end Foundation.Symmetric.EncryptThenMAC.AuthenticateResponse
