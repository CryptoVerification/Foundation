import Foundation.Constructions.Hash.NativeSimulatorTerminalCheck

/-! Terminal comparison with the private table retained on the input tape. -/
namespace Foundation.Hash.Native.SimulatorTerminalCheck
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Agreement preserves an arbitrary input tape, including the simulator's table. -/
theorem compare_run_framed (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (faultAfter : Nat) (input : Tape) :
    ∀ (bits : List Bool) (tail : Code) (before' right : List (Option Bool)),
      TimedExecution.eval (Reification.timedStep (compareCode faultAfter tail bits) oracle)
        (2 * bits.length)
        (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier right (bits.map some ++ before') }, trace⟩ : Configuration State) =
        PMF.pure ⟨state, .running { pc := 2 * bits.length, inputTape := input, outputTape := seekFrontier (bits.reverse.map some ++ right) before' }, trace⟩ := by
  intro bits
  induction bits with
  | nil => intro tail before' right; simp [compareCode, TimedExecution.eval]
  | cons b rest ih =>
      intro tail before' right
      have hcell : TimedExecution.eval (Reification.timedStep (compareCode faultAfter tail (b :: rest)) oracle)
            2
            (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier right (some b :: (rest.map some ++ before')) }, trace⟩ : Configuration State) =
          PMF.pure (CodeRelocation.frame (cellRel (faultAfter + 2 * rest.length + 2) b).length
            (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier (some b :: right) (rest.map some ++ before') }, trace⟩ : Configuration State)) := by
        have hc := TerminalCopy.cellLeft_run oracle state trace []
          ((compareCode faultAfter tail rest).map (CodeRelocation.instruction (cellRel (faultAfter + 2 * rest.length + 2) b).length))
          (faultAfter + 2 * rest.length + 2) b
          { pc := 0, inputTape := input, outputTape := seekFrontier right (some b :: (rest.map some ++ before')) }
          rfl rfl rfl
        rw [show ([] : Code) ++ TerminalCopy.cellLeft (([] : Code).length) (faultAfter + 2 * rest.length + 2) b ++
            (compareCode faultAfter tail rest).map (CodeRelocation.instruction (cellRel (faultAfter + 2 * rest.length + 2) b).length) =
            CodeRelocation.host (cellRel (faultAfter + 2 * rest.length + 2) b) (compareCode faultAfter tail rest) from rfl] at hc
        simp only [List.length_nil, seekFrontier_move] at hc
        exact hc
      rw [show 2 * (b :: rest).length = 2 + 2 * rest.length from by simp; omega,
        TimedExecution.eval_add]
      simp only [List.map_cons, List.cons_append]
      rw [hcell, PMF.pure_bind,
        show (compareCode faultAfter tail (b :: rest)) = CodeRelocation.host (cellRel (faultAfter + 2 * rest.length + 2) b)
          (compareCode faultAfter tail rest) from rfl,
        CodeRelocation.eval (cellRel (faultAfter + 2 * rest.length + 2) b) (compareCode faultAfter tail rest)
          oracle (2 * rest.length), ih, PMF.pure_map]
      simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
        List.reverse_cons, List.map_append, List.append_assoc]
      rfl

/-- The flag's value is retained and the table tape is preserved. -/
theorem checkCode_run_framed (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (bits : List Bool)
    (successCode mismatchCode : Code) (input : Tape) (flag : Option Bool)
    (before' right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (checkCode bits successCode mismatchCode) oracle)
      (1 + 2 * bits.length)
      (⟨state, .running { pc := 0, inputTape := input, outputTape := { left := bits.map some ++ before', current := flag, right := right } }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 1 + 2 * bits.length, inputTape := input, outputTape := seekFrontier (bits.reverse.map some ++ flag :: right) before' }, trace⟩ := by
  have hmove : ({ left := bits.map some ++ before', current := flag, right := right } : Tape).moveLeft =
      seekFrontier (flag :: right) (bits.map some ++ before') := by
    generalize bits.map some ++ before' = cells
    cases cells <;> rfl
  have hstep : TimedExecution.eval (Reification.timedStep (checkCode bits successCode mismatchCode) oracle) 1
      (⟨state, .running { pc := 0, inputTape := input, outputTape := { left := bits.map some ++ before', current := flag, right := right } }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame 1
        (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier (flag :: right) (bits.map some ++ before') }, trace⟩ : Configuration State)) := by
    simp [checkCode, CodeRelocation.host, TimedExecution.eval, Reification.timedStep,
      Reification.terminal, Reification.perform, Reification.action, transition,
      Machine.Instruction.next, Machine.Configuration.advance, Machine.Configuration.updateTape,
      hmove, CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]
  rw [TimedExecution.eval_add, hstep, PMF.pure_bind, checkCode]
  have placed := CodeRelocation.eval [Instruction.native (Instruction.moveLeft .output)]
    (compareCode successCode.length (successCode ++ mismatchCode) bits) oracle (2 * bits.length)
    (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier (flag :: right) (bits.map some ++ before') }, trace⟩ : Configuration State)
  simp only [List.length_cons, List.length_nil] at placed
  rw [placed, compare_run_framed oracle state trace successCode.length input bits (successCode ++ mismatchCode)
    before' (flag :: right), PMF.pure_map]
  rfl

/-- Rewind the table, return to the flag, then move onto the key and compare.
The additional key movement is charged separately from the existing flag movement.
This agreement statement concerns the query's own marked packet, not reconstruction
of a predecessor chain. -/
theorem check_after_rewind (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (query : CompressionInput (Foundation.Symmetric.Bits κ) (Foundation.Symmetric.Bits n))
    (table : CompressionTable (Foundation.Symmetric.Bits κ) (Foundation.Symmetric.Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none)
    (hMarker : query.2.1 = true) (successCode mismatchCode : Code) :
    TimedExecution.eval (Reification.timedStep
      (SimulatorFreshAfterLookup.codeWithBody (checkInput query successCode mismatchCode)) oracle)
      (SimulatorFreshAfterLookup.rewindSteps table + 1 + (1 + 2 * (κ + 1 + n)))
      (NativeCode.frame state trace (SimulatorFreshAfterLookup.start query table beforeOutput)) =
      PMF.pure (CodeRelocation.frame 5 (CodeRelocation.frame 1
        (NativeCode.frame state trace
          { pc := 1 + 2 * (κ + 1 + n),
            inputTape := { Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] },
            outputTape := seekFrontier ((compressionPacket query).map some ++ [some false, none]) beforeOutput }))) := by
  have hkey : (compressionPacket query).reverse = checkBits query.1 query.2.2 := by
    simpa only [compressionPacket, recordBits] using reverse_record_eq_checkBitsOf query hMarker
  have hlen : (checkBits query.1 query.2.2).length = κ + 1 + n := by
    simpa only [checkBitsOf] using checkBitsOf_length query.1 query.2.2
  have hbody := checkCode_run_framed oracle state trace (checkBits query.1 query.2.2)
    successCode mismatchCode
    ({ Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] } : Tape)
    (some false) beforeOutput [none]
  have hpacket : (checkBits query.1 query.2.2).reverse = compressionPacket query := by
    rw [← hkey, List.reverse_reverse]
  rw [hlen, hpacket] at hbody
  have hwhole := SimulatorFreshAfterLookup.withBody_run (checkInput query successCode mismatchCode)
    oracle state trace query table beforeOutput fresh (1 + 2 * (κ + 1 + n))
  have hentry : NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput) =
      (⟨state, .running { pc := 0, inputTape := { Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] }, outputTape := { left := (checkBits query.1 query.2.2).map some ++ beforeOutput, current := some false, right := [none] } }, trace⟩ : Configuration State) := by
    simp only [NativeCode.frame, SimulatorFresh.startAtFlag, SimulatorFresh.start, hkey]
  rw [hentry] at hwhole
  simpa only [checkInput, hbody, PMF.pure_map, NativeCode.frame] using hwhole

/-- A disagreeing cell branches without changing the table or either tape. -/
theorem compare_head_differ_framed (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (input : Tape)
    (fault : Nat) (b : Bool) (rest : Code) (cur : Option Bool)
    (left right : List (Option Bool)) (hDiff : cur ≠ some b) :
    TimedExecution.eval (Reification.timedStep
      (CodeRelocation.host (cellRel fault b) rest) oracle) 1
      (⟨state, .running { pc := 0, inputTape := input, outputTape := { left := left, current := cur, right := right } }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := fault, inputTape := input, outputTape := { left := left, current := cur, right := right } }, trace⟩ := by
  have hOne : Reification.timedStep (CodeRelocation.host (cellRel fault b) rest) oracle
      (⟨state, .running { pc := 0, inputTape := input, outputTape := { left := left, current := cur, right := right } }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := fault, inputTape := input, outputTape := { left := left, current := cur, right := right } }, trace⟩ := by
    cases cur with
    | none =>
        simp only [CodeRelocation.host, cellRel, TerminalCopy.cellLeft, Reification.timedStep,
          Reification.terminal, Reification.perform, Reification.action, transition,
          Machine.Instruction.next, Machine.Configuration.tape, List.getElem?_append]
        rfl
    | some actual =>
        cases actual <;> cases b <;>
          simp only [CodeRelocation.host, cellRel, TerminalCopy.cellLeft, Reification.timedStep,
            Reification.terminal, Reification.perform, Reification.action, transition,
            Machine.Instruction.next, Machine.Configuration.tape, List.getElem?_append] <;>
          first | rfl | exact absurd rfl hDiff
  rw [show (1 : Nat) = 0 + 1 from rfl, TimedExecution.eval, hOne, PMF.pure_bind]
  rfl

/-- One agreeing block, with the table retained. -/
theorem compare_cell_agree_framed (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (input : Tape)
    (fault : Nat) (b : Bool) (rest : Code) (left right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (cellRel fault b) rest) oracle) 2
      (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier right (some b :: left) }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame 2
        (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier (some b :: right) left }, trace⟩ : Configuration State)) := by
  have hc := TerminalCopy.cellLeft_run oracle state trace []
    (rest.map (CodeRelocation.instruction 2)) fault b
    { pc := 0, inputTape := input, outputTape := seekFrontier right (some b :: left) } rfl rfl rfl
  rw [seekFrontier_move] at hc
  exact hc

/-- The first mismatch at any position leaves with the exact table tape intact. -/
theorem compare_run_mismatch_framed (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (faultAfter : Nat) (input : Tape) :
    ∀ (k : Nat) (bits : List Bool) (tail : Code) (before' right : List (Option Bool))
      (actual : List (Option Bool)),
      k < bits.length → k < actual.length →
      (∀ j, j < k → actual[j]? = (bits[j]?).map some) →
      actual[k]? ≠ (bits[k]?).map some →
      TimedExecution.eval (Reification.timedStep (compareCode faultAfter tail bits) oracle) (2 * k + 1)
        (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier right (actual ++ before') }, trace⟩ : Configuration State) =
        PMF.pure (⟨state, .running { pc := 2 * bits.length + faultAfter, inputTape := input, outputTape := seekFrontier ((actual.take k).reverse ++ right) (actual.drop k ++ before') }, trace⟩ : Configuration State) := by
  intro k
  induction k with
  | zero =>
      intro bits tail before' right actual hkB hkA hAgree hDiff
      rcases bits with _ | ⟨b, rest⟩
      · simp at hkB
      rcases actual with _ | ⟨a, actual'⟩
      · simp at hkA
      have hne : a ≠ some b := by
        have hd := hDiff
        simp only [List.getElem?_cons_zero, Option.map_some] at hd
        intro h
        exact hd (congrArg Option.some h)
      have hd := compare_head_differ_framed oracle state trace input
        (faultAfter + 2 * rest.length + 2) b (compareCode faultAfter tail rest)
        a (actual' ++ before') right hne
      change TimedExecution.eval _ 1
        (⟨state, .running { pc := 0, inputTape := input, outputTape := { left := actual' ++ before', current := a, right := right } }, trace⟩ : Configuration State) = _
      rw [compareCode, hd]
      have hpc : faultAfter + 2 * rest.length + 2 = 2 * (b :: rest).length + faultAfter := by
        simp only [List.length_cons]; omega
      rw [hpc]
      rfl
  | succ k ih =>
      intro bits tail before' right actual hkB hkA hAgree hDiff
      rcases bits with _ | ⟨b, rest⟩
      · simp at hkB
      rcases actual with _ | ⟨a, actual'⟩
      · simp at hkA
      have hHead : a = some b := by
        simpa only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] using hAgree 0 (by omega)
      subst a
      have hkB' : k < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hkB
      have hkA' : k < actual'.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hkA
      have hAgree' : ∀ j, j < k → actual'[j]? = (rest[j]?).map some := by
        intro j hj
        simpa only [List.getElem?_cons_succ] using hAgree (j + 1) (by omega)
      have hDiff' : actual'[k]? ≠ (rest[k]?).map some := by
        simpa only [List.getElem?_cons_succ] using hDiff
      rw [show 2 * Nat.succ k + 1 = 2 + (2 * k + 1) from by omega, TimedExecution.eval_add]
      simp only [List.cons_append]
      rw [compareCode, compare_cell_agree_framed, PMF.pure_bind]
      have placed := CodeRelocation.eval (cellRel (faultAfter + 2 * rest.length + 2) b)
        (compareCode faultAfter tail rest) oracle (2 * k + 1)
        (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier (some b :: right) (actual' ++ before') }, trace⟩ : Configuration State)
      rw [show (cellRel (faultAfter + 2 * rest.length + 2) b).length = 2 from rfl] at placed
      rw [placed, ih rest tail before' (some b :: right) actual' hkB' hkA' hAgree' hDiff', PMF.pure_map]
      simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
        List.take_succ_cons, List.drop_succ_cons, List.reverse_cons, List.append_assoc]
      have hpc : 2 + (2 * rest.length + faultAfter) = 2 * (b :: rest).length + faultAfter := by
        simp only [List.length_cons]; omega
      rw [hpc]
      rfl

end Foundation.Hash.Native.SimulatorTerminalCheck
