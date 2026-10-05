import Foundation.Crypto.Semantics.Machine.ContextualInput
import Foundation.Crypto.Semantics.Machine.OutputFrameCounter
import Foundation.Crypto.Semantics.Machine.AdvanceInputByOutput
import Foundation.Crypto.Semantics.Machine.NativeSequence

namespace Machine.SelectRetainedScalar

private def atCells (before rest : List (Option Bool)) : Tape :=
  {({right := rest} : Tape).moveRight with left := before}

def program : Program := ((skipUnary.followedBy skipUnary).followedBy
  OutputFrameCounter.program).followedBy AdvanceInputByOutput.program

def requestPrefix (n : Nat) (modulus scalar generator : List Bool) : List Bool :=
  encodeSecurityParameter n ++ encodeSecurityParameter (modulus++scalar++generator).length ++ modulus

/-- Locate the scalar in the actual request retained by exponentiation.
The public key's physical payload counts the modulus field's width. -/
theorem runs (n : Nat) (modulus scalar generator publicKey : List Bool)
    (retained : List (Option Bool)) (hWidth : modulus.length = publicKey.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus++scalar++generator)
    ∃ target used, used ≤ 3*n+3*(modulus++scalar++generator).length+11*publicKey.length+21 ∧
      RunsFor program
        ({inputTape := atCells [none] (raw.map some ++ none::retained), outputTape := {left := (frame publicKey).reverse.map some}} : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape.Equivalent
        (atCells ((requestPrefix n modulus scalar generator).reverse.map some ++ [none])
          ((scalar++generator).map some ++ none::retained)) ∧
      target.outputTape.Equivalent {left := (frame publicKey).reverse.map some} := by
  dsimp only
  let instanceBits := modulus++scalar++generator
  let out : Tape := {left := (frame publicKey).reverse.map some}
  let instancePrefix := (encodeSecurityParameter n).reverse.map some ++ [none]
  let payloadPrefix := (encodeSecurityParameter instanceBits.length).reverse.map some ++ instancePrefix
  let payloadInput := atCells payloadPrefix (instanceBits.map some ++ none::retained)
  have first := skipUnaryCells_runs [none] n ((frame instanceBits).map some ++ none::retained) out
  have second := skipUnaryCells_runs instancePrefix instanceBits.length (instanceBits.map some ++ none::retained) out
  have boundary : (skipUnaryCellsStart instancePrefix instanceBits.length (instanceBits.map some ++ none::retained) out).Equivalent
      ((skipUnaryCellsFinish [none] n ((frame instanceBits).map some ++ none::retained) out).resumeAt 0) := by
    have same : (skipUnaryCellsStart instancePrefix instanceBits.length (instanceBits.map some ++ none::retained) out).inputTape =
        (skipUnaryCellsFinish [none] n ((frame instanceBits).map some ++ none::retained) out).inputTape := by
      rw [skipUnaryCellsStart_layout]
      cases h : instanceBits.length with
      | zero =>
        have empty : instanceBits = [] := List.length_eq_zero_iff.mp h
        simp only [empty, List.map_nil, List.nil_append, frame, List.length_nil, List.replicate_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append]
        rw [skipUnaryCellsFinish_layout]
        simp [instancePrefix, encodeSecurityParameter, List.map_replicate, List.reverse_replicate, List.append_assoc, Tape.moveRight]
      | succ count =>
        simp only [frame, h, List.replicate_succ, List.map_append, List.map_cons, List.map_replicate, List.cons_append]
        rw [skipUnaryCellsFinish_layout]
        simp [instancePrefix, encodeSecurityParameter, List.map_replicate, List.reverse_replicate, List.append_assoc, Tape.moveRight]
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    rw [same]
    exact Tape.Equivalent.refl _
  obtain ⟨a, u, hu, readRun, readHalt, ai, ao⟩ := first.followedBy_equivalent second boundary
    (Nat.zero_le _) rfl rfl rfl
  have payloadLayout : payloadInput.Equivalent
      (skipUnaryCellsFinish instancePrefix instanceBits.length (instanceBits.map some ++ none::retained) out).inputTape := by
    cases hInstance : instanceBits with
    | nil =>
      simp only [List.map_nil, List.nil_append]
      rw [skipUnaryCellsFinish_layout]
      simp [payloadInput, atCells, payloadPrefix, hInstance, encodeSecurityParameter, Tape.moveRight, List.map_replicate]
      exact Tape.Equivalent.refl _
    | cons bit rest =>
      simp only [List.map_cons, List.cons_append]
      rw [skipUnaryCellsFinish_layout]
      simp [payloadInput, atCells, payloadPrefix, hInstance, encodeSecurityParameter, Tape.moveRight, List.map_replicate]
      exact Tape.Equivalent.refl _
  obtain ⟨b, v, hv, counterRun, counterHalt, bi, bo⟩ := OutputFrameCounter.runs payloadInput publicKey
  have counterEntry : ({inputTape := payloadInput, outputTape := out} : Configuration).Equivalent (a.resumeAt 0) :=
    ⟨rfl, rfl, payloadLayout.trans ai, ao⟩
  obtain ⟨c, uc, hc, rc, cHalt, ci, co⟩ := readRun.followedBy_equivalent counterRun counterEntry
    (Nat.zero_le _) rfl readHalt counterHalt
  have advance := AdvanceInputByOutput.runs_cells payloadPrefix
    ((encodeSecurityParameter publicKey.length).reverse.map some)
    ((scalar++generator).map some ++ none::retained) modulus publicKey hWidth
  have advanceEntry : ({inputTape := payloadInput, outputTape := {Tape.ofBits publicKey with left := (encodeSecurityParameter publicKey.length).reverse.map some}} : Configuration).Equivalent (c.resumeAt 0) :=
    ⟨rfl, rfl, bi.symm.trans ci, bo.symm.trans co⟩
  simp only [List.map_append, List.append_assoc] at advance
  have advanceEntryActual := advanceEntry
  simp only [payloadInput, atCells, instanceBits, List.map_append, List.append_assoc] at advanceEntryActual
  obtain ⟨target, used, bound, run, halt, ti, tout⟩ := rc.followedBy_equivalent advance advanceEntryActual
    (Nat.zero_le _) rfl cHalt rfl
  have startEq : skipUnaryCellsStart [none] n ((frame instanceBits).map some ++ none::retained) out =
      ({inputTape := atCells [none] ((encodeSecurityParameter n ++ frame instanceBits).map some ++ none::retained), outputTape := out} : Configuration) := by
    rw [skipUnaryCellsStart_layout]
    simp [atCells, encodeSecurityParameter, List.map_append, List.map_replicate, List.append_assoc]
  rw [startEq] at run
  refine ⟨target, used, ?_, run, halt, ?_, ?_⟩
  · change used ≤ 3*n+3*instanceBits.length+11*publicKey.length+21
    omega
  · have same : (modulus.reverse.map some ++ payloadPrefix) = (requestPrefix n modulus scalar generator).reverse.map some ++ [none] := by
      simp [requestPrefix, payloadPrefix, instancePrefix, instanceBits, List.reverse_append, List.map_append, List.append_assoc]
    rw [same] at ti
    simpa only [atCells, List.map_append, List.append_assoc] using ti.symm
  · have same : publicKey.reverse.map some ++ (encodeSecurityParameter publicKey.length).reverse.map some = (frame publicKey).reverse.map some := by
      simp [frame, encodeSecurityParameter, List.reverse_append, List.map_append, List.map_replicate]
    rw [same] at tout
    exact tout.symm

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · exact Program.followedBy_no_randomBit _ _
      (Program.followedBy_no_randomBit _ _ skipUnary_no_randomBit skipUnary_no_randomBit)
      OutputFrameCounter.no_randomBit
  · exact AdvanceInputByOutput.no_randomBit

end Machine.SelectRetainedScalar
