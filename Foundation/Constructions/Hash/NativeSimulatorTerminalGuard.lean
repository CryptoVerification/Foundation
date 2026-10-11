import Foundation.Constructions.Hash.NativeSimulatorTerminalCheckFramed
import Foundation.Crypto.Semantics.Oracle.OutputSeekFlag

/-! The terminal-marker guard is fixed by the construction's terminal payload.
It does not compare the runtime chaining value with the IV: predecessor search
performs that test separately. Continuations are linked with relocation. -/
namespace Foundation.Hash.Native.SimulatorTerminalGuard
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric SimulatorTerminalCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def expected (terminal : Bits κ) : List Bool := terminal.toList.reverse ++ [true]

def actual (query : CompressionInput (Bits κ) (Bits n)) : List Bool :=
  query.2.2.toList.reverse ++ [query.2.1]

theorem expected_length (terminal : Bits κ) : (expected terminal).length = κ + 1 := by
  simp [expected]

theorem actual_length (query : CompressionInput (Bits κ) (Bits n)) :
    (actual query).length = κ + 1 := by
  simp [actual]

/-- The guard recognizes exactly the marker/payload predicate of `terminalMessage`. -/
theorem actual_eq_expected_iff (query : CompressionInput (Bits κ) (Bits n))
    (terminal : Bits κ) :
    actual query = expected terminal ↔ query.2.1 = true ∧ query.2.2 = terminal := by
  constructor
  · intro h
    have hr := congrArg List.reverse h
    simp only [actual, expected, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.reverse_reverse, List.nil_append] at hr
    have hm : query.2.1 = true := by simpa using congrArg List.head? hr
    have hp : query.2.2.toList = terminal.toList := by simpa using congrArg List.tail hr
    exact ⟨hm, List.ofFn_injective hp⟩
  · rintro ⟨hm, hp⟩
    simp only [actual, expected, hm, hp]

theorem packet_reverse (query : CompressionInput (Bits κ) (Bits n)) :
    (compressionPacket query).reverse = actual query ++ query.1.toList.reverse := by
  simp [compressionPacket, actual, List.reverse_append, List.reverse_cons, List.append_assoc]

/-- All branch targets, including the rejected continuation's internal targets,
are relative to their own closed component before linking. -/
def code (terminal : Bits κ) (accepted rejected : Code) : Code :=
  CodeRelocation.host [.native (.moveLeft .output)]
    (compareCode accepted.length (CodeRelocation.host accepted rejected) (expected terminal))

theorem code_length (terminal : Bits κ) (accepted rejected : Code) :
    (code terminal accepted rejected).length = 1 + 2 * (κ + 1) + accepted.length + rejected.length := by
  simp only [code, CodeRelocation.code_length, compareCode_length, expected_length, List.length_cons,
    List.length_nil]
  omega

theorem code_native (terminal : Bits κ) (accepted rejected : Code)
    (ha : ∀ i ∈ accepted, ∃ op, i = .native op)
    (hr : ∀ i ∈ rejected, ∃ op, i = .native op) :
    ∀ i ∈ code terminal accepted rejected, ∃ op, i = .native op := by
  apply CodeRelocation.host_native
  · intro i hi
    exact ⟨.moveLeft .output, by simpa using hi⟩
  · exact compareCode_native _ _ _ (CodeRelocation.host_native _ _ ha hr)

/-- Linking a continuation into all nested placements adds the same final offset. -/
theorem compareCode_link (fault : Nat) (tail : Code) (bits : List Bool) :
    compareCode fault tail bits = CodeRelocation.host (compareCode fault [] bits) tail := by
  induction bits with
  | nil => simp [compareCode]
  | cons b rest ih =>
      rw [compareCode, ih, ← CodeRelocation.host_assoc]
      rfl

def rejectedPrefix (terminal : Bits κ) (accepted : Code) : Code :=
  CodeRelocation.host
    (CodeRelocation.host [.native (.moveLeft .output)]
      (compareCode accepted.length [] (expected terminal))) accepted

theorem rejectedPrefix_length (terminal : Bits κ) (accepted : Code) :
    (rejectedPrefix terminal accepted).length = 1 + 2 * (κ + 1) + accepted.length := by
  simp only [rejectedPrefix, CodeRelocation.code_length, compareCode_length, expected_length,
    List.length_cons, List.length_nil]
  omega

theorem code_rejected_host (terminal : Bits κ) (accepted rejected : Code) :
    code terminal accepted rejected = CodeRelocation.host (rejectedPrefix terminal accepted) rejected := by
  rw [code, compareCode_link, ← CodeRelocation.host_assoc, ← CodeRelocation.host_assoc]
  rfl

/-- Move off the response flag while preserving the complete table tape. -/
theorem prepare_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (terminal : Bits κ) (accepted rejected : Code)
    (input : Tape) (flag : Option Bool) (cells before' right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code terminal accepted rejected) oracle) 1
      (⟨state, .running { pc := 0, inputTape := input, outputTape := { left := cells ++ before', current := flag, right := right } }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame 1
        (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier (flag :: right) (cells ++ before') }, trace⟩ : Configuration State)) := by
  have hm : ({ left := cells ++ before', current := flag, right := right } : Tape).moveLeft =
      seekFrontier (flag :: right) (cells ++ before') := by
    generalize cells ++ before' = remaining
    cases remaining <;> rfl
  simp [code, CodeRelocation.host, TimedExecution.eval, Reification.timedStep,
    Reification.terminal, Reification.perform, Reification.action, transition,
    Machine.Instruction.next, Machine.Configuration.advance, Machine.Configuration.updateTape,
    hm, CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]

/-- A valid terminal marker/payload enters the accepted continuation with the
runtime chaining value still on the output tape and the private table intact. -/
theorem accepted_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (terminal : Bits κ) (accepted rejected : Code)
    (input : Tape) (flag : Option Bool) (query : CompressionInput (Bits κ) (Bits n))
    (before' right : List (Option Bool))
    (h : query.2.1 = true ∧ query.2.2 = terminal) :
    TimedExecution.eval (Reification.timedStep (code terminal accepted rejected) oracle)
      (1 + 2 * (κ + 1))
      (⟨state, .running { pc := 0, inputTape := input, outputTape := { left := (compressionPacket query).reverse.map some ++ before', current := flag, right := right } }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 1 + 2 * (κ + 1), inputTape := input, outputTape := seekFrontier ((expected terminal).reverse.map some ++ flag :: right) (query.1.toList.reverse.map some ++ before') }, trace⟩ := by
  have heq := (actual_eq_expected_iff query terminal).mpr h
  rw [packet_reverse, List.map_append, heq, List.append_assoc]
  have hl := expected_length terminal
  rw [← hl, TimedExecution.eval_add, prepare_run, PMF.pure_bind, code]
  have placed := CodeRelocation.eval [.native (.moveLeft .output)]
    (compareCode accepted.length (CodeRelocation.host accepted rejected) (expected terminal)) oracle
    (2 * (expected terminal).length)
    (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier (flag :: right) ((expected terminal).map some ++ (query.1.toList.reverse.map some ++ before')) }, trace⟩ : Configuration State)
  simp only [List.length_cons, List.length_nil] at placed
  rw [placed, compare_run_framed, PMF.pure_map]
  rfl

/-- Equal-width unequal strings have a first disagreeing position. -/
theorem first_mismatch (x y : List Bool) (hl : x.length = y.length) (hne : x ≠ y) :
    ∃ k, k < x.length ∧ (∀ j, j < k → x[j]? = y[j]?) ∧ x[k]? ≠ y[k]? := by
  induction x generalizing y with
  | nil =>
      cases y <;> simp_all
  | cons b rest ih =>
      cases y with
      | nil => simp at hl
      | cons c other =>
          by_cases hbc : b = c
          · subst c
            have ht : rest ≠ other := by intro h; exact hne (by rw [h])
            have hlt : rest.length = other.length := by simpa using hl
            obtain ⟨k, hk, hp, hd⟩ := ih other hlt ht
            refine ⟨k + 1, by simp; omega, ?_, ?_⟩
            · intro j hj
              cases j with
              | zero => rfl
              | succ j => simpa only [List.getElem?_cons_succ] using hp j (by omega)
            · simpa only [List.getElem?_cons_succ] using hd
          · refine ⟨0, by simp, by intro j hj; omega, ?_⟩
            simp only [List.getElem?_cons_zero]
            intro heq
            exact hbc (Option.some.inj heq)

private theorem map_some_injective : Function.Injective (fun x : Option Bool => x.map some) := by
  intro x y h
  cases x <;> cases y <;> simp_all

/-- A false marker or wrong terminal payload enters the rejected continuation at
its correctly relocated address. The exact first-mismatch time is retained. -/
theorem rejected_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (terminal : Bits κ) (accepted rejected : Code)
    (input : Tape) (flag : Option Bool) (query : CompressionInput (Bits κ) (Bits n))
    (before' right : List (Option Bool))
    (h : ¬ (query.2.1 = true ∧ query.2.2 = terminal)) :
    ∃ k, k < κ + 1 ∧
      TimedExecution.eval (Reification.timedStep (code terminal accepted rejected) oracle) (1 + (2 * k + 1))
        (⟨state, .running { pc := 0, inputTape := input, outputTape := { left := (compressionPacket query).reverse.map some ++ before', current := flag, right := right } }, trace⟩ : Configuration State) =
        PMF.pure ⟨state, .running { pc := 1 + (2 * (κ + 1) + accepted.length), inputTape := input, outputTape := seekFrontier ((((actual query).map some).take k).reverse ++ flag :: right) (((actual query).map some).drop k ++ (query.1.toList.reverse.map some ++ before')) }, trace⟩ := by
  have hne : actual query ≠ expected terminal := by
    intro heq
    exact h ((actual_eq_expected_iff query terminal).mp heq)
  obtain ⟨k, hk, hp, hd⟩ := first_mismatch (actual query) (expected terminal)
    (by rw [actual_length, expected_length]) hne
  have hk' : k < κ + 1 := by simpa only [actual_length] using hk
  have hb : k < (expected terminal).length := by simpa only [expected_length] using hk'
  have hc : k < ((actual query).map some).length := by simpa only [List.length_map] using hk
  have hprefix : ∀ j, j < k → ((actual query).map some)[j]? = ((expected terminal)[j]?).map some := by
    intro j hj
    simp only [List.getElem?_map, hp j hj]
  have hdifferent : ((actual query).map some)[k]? ≠ ((expected terminal)[k]?).map some := by
    rw [List.getElem?_map]
    intro heq
    exact hd (map_some_injective heq)
  refine ⟨k, hk', ?_⟩
  rw [packet_reverse, List.map_append, List.append_assoc, TimedExecution.eval_add, prepare_run, PMF.pure_bind, code]
  have placed := CodeRelocation.eval [.native (.moveLeft .output)]
    (compareCode accepted.length (CodeRelocation.host accepted rejected) (expected terminal)) oracle
    (2 * k + 1)
    (⟨state, .running { pc := 0, inputTape := input, outputTape := seekFrontier (flag :: right) ((actual query).map some ++ (query.1.toList.reverse.map some ++ before')) }, trace⟩ : Configuration State)
  simp only [List.length_cons, List.length_nil] at placed
  rw [placed, compare_run_mismatch_framed oracle state trace accepted.length input k
    (expected terminal) (CodeRelocation.host accepted rejected)
    (query.1.toList.reverse.map some ++ before') (flag :: right) ((actual query).map some)
    hb hc hprefix hdifferent, PMF.pure_map]
  simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc, expected_length]

/-- A rejected query is restored to exactly its original response-flag entry.
The next continuation can therefore reuse the existing fresh-response code.
Both the private table and every query cell survive the recovery. -/
theorem rejected_recovered (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (terminal : Bits κ) (accepted fresh : Code)
    (input : Tape) (flag : Bool) (query : CompressionInput (Bits κ) (Bits n))
    (before' : List (Option Bool))
    (h : ¬ (query.2.1 = true ∧ query.2.2 = terminal)) :
    ∃ k, k < κ + 1 ∧
      TimedExecution.eval (Reification.timedStep (code terminal accepted (OutputSeekFlag.code fresh)) oracle)
        ((1 + (2 * k + 1)) + (3 * (k + 2) + 2))
        (⟨state, .running { pc := 0, inputTape := input, outputTape := { left := (compressionPacket query).reverse.map some ++ before', current := some flag, right := [none] } }, trace⟩ : Configuration State) =
        PMF.pure (CodeRelocation.frame (rejectedPrefix terminal accepted).length
          (⟨state, .running { pc := 4, inputTape := input, outputTape := { left := (compressionPacket query).reverse.map some ++ before', current := some flag, right := [none] } }, trace⟩ : Configuration State)) := by
  obtain ⟨k, hk, hd⟩ := rejected_run oracle state trace terminal accepted (OutputSeekFlag.code fresh)
    input (some flag) query before' [none] h
  have hka : k < (actual query).length := by simpa only [actual_length] using hk
  cases hr : (actual query).drop k with
  | nil =>
      have hl := congrArg List.length hr
      simp only [List.length_drop, List.length_nil] at hl
      omega
  | cons c rest =>
      have hdecomp : (actual query).take k ++ c :: rest = actual query := by
        rw [← hr, List.take_append_drop]
      have hpast : ((actual query).take k).length = k := by
        simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hka)]
      have htape : seekFrontier ((((actual query).map some).take k).reverse ++ [some flag, none])
          (((actual query).map some).drop k ++ (query.1.toList.reverse.map some ++ before')) =
          FixedWidthCopy.backwardFrontier (((actual query).take k).reverse.map some ++ [some flag, none])
            ((c :: rest).map some ++ (query.1.toList.reverse.map some ++ before')) := by
        simp only [← List.map_take, ← List.map_drop, hr, List.map_reverse, seekFrontier,
          FixedWidthCopy.backwardFrontier]
      have hrecovery := OutputSeekFlag.recover oracle state trace input fresh
        ((actual query).take k) rest c flag (query.1.toList.reverse.map some ++ before')
      rw [hpast, hdecomp] at hrecovery
      have hpacket : (actual query).map some ++ (query.1.toList.reverse.map some ++ before') =
          (compressionPacket query).reverse.map some ++ before' := by
        rw [packet_reverse, List.map_append, List.append_assoc]
      rw [hpacket] at hrecovery
      refine ⟨k, hk, ?_⟩
      rw [TimedExecution.eval_add, hd, PMF.pure_bind]
      rw [code_rejected_host]
      have hframe : (⟨state, .running { pc := 1 + (2 * (κ + 1) + accepted.length), inputTape := input, outputTape := seekFrontier ((((actual query).map some).take k).reverse ++ [some flag, none]) (((actual query).map some).drop k ++ (query.1.toList.reverse.map some ++ before')) }, trace⟩ : Configuration State) =
          CodeRelocation.frame (rejectedPrefix terminal accepted).length
            (⟨state, .running { pc := 0, inputTape := input, outputTape := FixedWidthCopy.backwardFrontier (((actual query).take k).reverse.map some ++ [some flag, none]) ((c :: rest).map some ++ (query.1.toList.reverse.map some ++ before')) }, trace⟩ : Configuration State) := by
        simp only [CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
          rejectedPrefix_length, Nat.add_zero, htape]
        rw [Nat.add_assoc]
      rw [hframe, CodeRelocation.eval, hrecovery, PMF.pure_map]

end Foundation.Hash.Native.SimulatorTerminalGuard
