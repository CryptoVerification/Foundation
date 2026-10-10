import Foundation.Constructions.Hash.NativeSimulatorLookupStages
import Foundation.Crypto.Semantics.BoundaryExactTime

/-! Sequential lookup of the simulator's compression table by actual finite
native code. Duplicate keys are permitted: the first matching entry is
returned, as in the existing List.lookup semantics. -/
namespace Foundation.Hash.Native.SimulatorLookup
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

/-- A proof-side exact transition count. It is not a runtime lookup opcode. -/
def lookupSteps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n)) :
    CompressionTable (Bits κ) (Bits n) → Nat
  | [] => n + κ + 5
  | entry :: rest =>
      if entry.1 = query then 7 * (n + κ + 1) + 5 * n + 12
      else 8 * (n + κ + 1) + n + 10 + lookupSteps query rest

/-- Full physical postcondition, retaining all tape cells and the first
matching value. This mathematical definition is never executed by the code. -/
def lookupFinish {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n)) :
    CompressionTable (Bits κ) (Bits n) → List (Option Bool) → List (Option Bool) → Machine.Configuration
  | [], beforeInput, beforeOutput => missingFinish query beforeInput beforeOutput
  | entry :: rest, beforeInput, beforeOutput =>
      if entry.1 = query then foundFinish entry rest query beforeInput beforeOutput
      else lookupFinish query rest ((entryBits entry).reverse.map some ++ beforeInput) beforeOutput

/-- Actual execution, with no precondition of unique keys or a host-side
search result. Oracle state and prior transcript are preserved jointly. -/
theorem lookup_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) (lookupSteps query table)
      (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace (lookupFinish query table beforeInput beforeOutput)) := by
  induction table generalizing beforeInput with
  | nil => exact lookup_missing_run oracle state trace query beforeInput beforeOutput
  | cons entry rest ih =>
      by_cases equalKey : entry.1 = query
      · simp only [lookupSteps, lookupFinish, equalKey, ↓reduceIte]
        exact lookup_found_run oracle state trace entry rest query beforeInput beforeOutput equalKey
      · simp only [lookupSteps, lookupFinish, equalKey, ↓reduceIte]
        rw [TimedExecution.eval_add, lookup_skip_run oracle state trace entry rest query
          beforeInput beforeOutput equalKey, PMF.pure_bind, ih]

/-- Physical response format: false for absent, true followed by the digest
for present. The original query precedes this packet on the output tape. -/
def lookupResponse {n : Nat} : Option (Bits n) → List Bool
  | none => [false]
  | some value => true :: value.toList

/-- The physical response is exactly the existing table lookup, including
its first-match behavior in the presence of duplicate keys. -/
theorem lookupFinish_output {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    (lookupFinish query table beforeInput beforeOutput).outputTape =
      { left := (lookupResponse (table.lookup query)).reverse.map some ++
          (compressionPacket query).reverse.map some ++ beforeOutput } := by
  induction table generalizing beforeInput with
  | nil => simp [lookupFinish, missingFinish, lookupResponse]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases equalKey : key = query
      · simp [lookupFinish, equalKey, foundFinish, lookupResponse,
          List.reverse_cons, List.map_append, List.append_assoc]
      · have reverseUnequal : query ≠ key := Ne.symm equalKey
        simp [lookupFinish, equalKey, List.lookup_cons, beq_eq_false_iff_ne.mpr reverseUnequal, ih]

theorem lookupFinish_halted {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    (lookupFinish query table beforeInput beforeOutput).halted = true := by
  induction table generalizing beforeInput with
  | nil => rfl
  | cons entry rest ih =>
      simp only [lookupFinish]
      split_ifs
      · rfl
      · exact ih _

/-- A width- and table-length bound on actual transitions. It includes all
key comparisons, delimiter restoration, value traversal, query rewind,
response copying and the final halt. It is not wall-clock time. -/
def lookupBudget (n κ entries : Nat) : Nat :=
  entries * (8 * (n + κ + 1) + n + 10) +
    max (7 * (n + κ + 1) + 5 * n + 12) (n + κ + 5)

theorem lookupBudget_eq (n κ entries : Nat) :
    lookupBudget n κ entries = entries * (9 * n + 8 * κ + 18) + 12 * n + 7 * κ + 19 := by
  unfold lookupBudget
  rw [max_eq_left (by omega)]
  ring

theorem lookupSteps_le {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    lookupSteps query table ≤ lookupBudget n κ table.length := by
  induction table with
  | nil => simp [lookupSteps, lookupBudget]
  | cons entry rest ih =>
      simp only [lookupSteps, lookupBudget, List.length_cons, Nat.add_mul, Nat.one_mul] at ⊢
      unfold lookupBudget at ih
      split_ifs <;> omega

theorem lookupSteps_positive {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    0 < lookupSteps query table := by
  cases table with
  | nil => simp [lookupSteps]
  | cons entry rest => simp only [lookupSteps]; split_ifs <;> omega

/-- Adjacent horizons share one physical execution: immediately before
and immediately after the final native halt instruction. -/
theorem lookup_stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle)
      (lookupSteps query table - 1 + halt.toNat)
      (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace
        { lookupFinish query table beforeInput beforeOutput with halted := halt }) := by
  induction table generalizing beforeInput with
  | nil =>
      simp only [lookupSteps, lookupFinish]
      rw [show n + κ + 5 - 1 = n + κ + 4 by omega]
      exact lookup_missing_stage oracle state trace query beforeInput beforeOutput halt
  | cons entry rest ih =>
      by_cases equalKey : entry.1 = query
      · simp only [lookupSteps, lookupFinish, equalKey, ↓reduceIte]
        rw [show 7 * (n + κ + 1) + 5 * n + 12 - 1 =
          7 * (n + κ + 1) + 5 * n + 11 by omega]
        exact lookup_found_stage oracle state trace entry rest query beforeInput beforeOutput equalKey halt
      · simp only [lookupSteps, lookupFinish, equalKey, ↓reduceIte]
        have positive := lookupSteps_positive query rest
        rw [show 8 * (n + κ + 1) + n + 10 + lookupSteps query rest - 1 + halt.toNat =
          (8 * (n + κ + 1) + n + 10) + (lookupSteps query rest - 1 + halt.toNat) by omega,
          TimedExecution.eval_add, lookup_skip_run oracle state trace entry rest query
            beforeInput beforeOutput equalKey, PMF.pure_bind, ih]

/-- Actual first halt, with its physical result and exact transition count
in one joint distribution. The count is derived from the executed stages. -/
theorem lookup_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    runToBoundary (Reification.timedStep (lookupCode n κ) oracle)
      (fun frame => Reification.terminal frame.control) (lookupSteps query table)
      (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace (lookupFinish query table beforeInput beforeOutput),
        lookupSteps query table) := by
  have positive := lookupSteps_positive query table
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (lookupCode n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput))
    (lookupSteps query table - 1)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (by intro frame support
        have law := lookup_stage_run oracle state trace query table beforeInput beforeOutput false
        simp only [Bool.toNat_false, Nat.add_zero] at law
        rw [law, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
    (by intro frame support
        rw [show lookupSteps query table - 1 + 1 = lookupSteps query table by omega,
          lookup_run, PMF.mem_support_pure_iff] at support
        subst frame
        exact lookupFinish_halted query table beforeInput beforeOutput)
  simpa only [show lookupSteps query table - 1 + 1 = lookupSteps query table by omega,
    lookup_run, PMF.pure_map] using h

/-- The same actual execution realizes the existing table lookup after
observing the output tape, preserving external state and prior history. -/
theorem lookup_output_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    (TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle) (lookupSteps query table)
      (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput))).map
      (fun frame => (frame.state, frame.reverseTrace,
        match frame.control with | .running machine => some machine.outputTape | _ => none)) =
      PMF.pure (state, trace, some
        ({ left := (lookupResponse (table.lookup query)).reverse.map some ++
          (compressionPacket query).reverse.map some ++ beforeOutput } : Tape)) := by
  rw [lookup_run, PMF.pure_map]
  simp only [NativeCode.frame, lookupFinish_output]

/-- Physical entry data. Preparing these tapes is a caller obligation; the
lookup budget starts with the encoded table/query already on their tapes. -/
structure LookupInput (State : Type*) (n κ : Nat) where
  state : State
  trace : List (List Bool × List Bool)
  query : CompressionInput (Bits κ) (Bits n)
  table : CompressionTable (Bits κ) (Bits n)
  beforeInput : List (Option Bool)
  beforeOutput : List (Option Bool)

/-- Register the actual full-frame run with Foundation's existing composable
procedure contract. The exit is the returned physical frame itself. -/
noncomputable def lookupProcedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (Reification.timedStep (lookupCode n κ) oracle) (LookupInput State n κ) (Configuration State) :=
  Procedure.ofFixed _
    (fun input => NativeCode.frame input.state input.trace
      (scanStart input.table input.query input.beforeInput input.beforeOutput))
    (fun _ output => output)
    (fun input => PMF.pure (NativeCode.frame input.state input.trace
      (lookupFinish input.query input.table input.beforeInput input.beforeOutput)))
    (fun input => lookupSteps input.query input.table)
    (fun input => by rw [lookup_run, PMF.pure_map])

theorem lookupProcedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (lookupProcedure n κ oracle) := by
  apply Procedure.operational_ofFixed

/-- The procedure's cost is its actual first halt, rather than only a
fixed-horizon simulation certificate. -/
theorem lookupProcedure_first_joint {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : LookupInput State n κ) :
    runToBoundary (Reification.timedStep (lookupCode n κ) oracle)
      (fun frame => Reification.terminal frame.control)
      ((lookupProcedure n κ oracle).budget input) ((lookupProcedure n κ oracle).entry input) =
      (lookupProcedure n κ oracle).costed input := by
  change runToBoundary _ _ (lookupSteps input.query input.table)
    (NativeCode.frame input.state input.trace
      (scanStart input.table input.query input.beforeInput input.beforeOutput)) = _
  rw [lookup_first_joint]
  simp only [lookupProcedure, TimedExecution.Procedure.ofFixed, PMF.pure_map]

end Foundation.Hash.Native.SimulatorLookup
