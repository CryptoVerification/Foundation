import Foundation.Constructions.Hash.PolygraphLookup
import Foundation.Constructions.Hash.NativeSimulatorQueryPacket
import Foundation.Crypto.Semantics.BoundaryStability
import Foundation.Crypto.Semantics.Asymptotic.PolynomiallyBounded

/-! Native cache-hit and fresh-sample rounds with a common transition cap.
The physical interpreter takes no logical table: the table is only a proof
parameter certifying its retained input tape. Admission, lookup, random-bit
generation, insertion, restoration and physical packet export are included.
The resulting costed oracle accounts for server transitions, not client CPU
time or one uniform bit program for all width parameters. -/
namespace Foundation.Hash.Native.PolygraphOracle

open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

abbrev Key (n κ : Nat) := CompressionInput (Bits κ) (Bits n)
abbrev Table (n κ : Nat) := CompressionTable (Bits κ) (Bits n)

def slope (n κ : Nat) := 15 * n + 12 * κ + 26
def overhead (n κ : Nat) := 21 * n + 12 * κ + 40
def budget (n κ entries : Nat) := entries * slope n κ + overhead n κ

variable {n κ : Nat} {State Result : Type}

theorem steps_budget (query : Key n κ) (table : Table n κ) (positive : 0 < n)
    {entries : Nat} (size : table.length ≤ entries) :
    SimulatorQueryPacket.steps query table ≤ budget n κ entries := by
  apply (SimulatorQueryPacket.steps_le query table positive).trans
  have h := Nat.mul_le_mul_right (15 * n + 12 * κ + 26) size
  dsimp [budget, slope, overhead]
  omega

/-- No table, host lookup, or preselected cache branch is supplied here. -/
noncomputable def physicalRound (oracle : BitOracle State) (entries : Nat)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : Key n κ) : PMF (SimulatorQueryPacket.Control State × Nat) :=
  runToBoundary (SimulatorQueryPacket.step n κ oracle) SimulatorQueryPacket.readyBoundary
    (budget n κ entries) (.admitting state machine trace (compressionPacket query ++ [false]))

def encodeAnswer (state : State) (trace : List (List Bool × List Bool))
    (answer : Table n κ × Bits n) :=
  some (state, trace, some (SimulatorLookup.tableBits answer.1, answer.2.toList))

theorem packet_law (oracle : BitOracle State) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (query : Key n κ) (table : Table n κ)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    (TimedExecution.eval (SimulatorQueryPacket.step n κ oracle) (SimulatorQueryPacket.steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).map
        SimulatorQueryPacket.observation =
      (RandomOracle.oracle table query).map (encodeAnswer state trace) := by
  have middle := SimulatorDispatchQueryLoading.native_run oracle state machine trace query table layout
    positive SimulatorDispatchQueryLoading.view SimulatorDispatchQueryLoading.view_equivalent
  rw [show (fun frame : Configuration State => some (SimulatorDispatchQueryLoading.view frame)) =
    some ∘ SimulatorDispatchQueryLoading.view by rfl, ← PMF.map_comp,
    SimulatorDispatchQueryLoading.result_view] at middle
  rw [SimulatorQueryPacket.run oracle state machine trace query table layout positive, PMF.map_comp]
  calc
    _ = (TimedExecution.eval (SimulatorDispatchQueryLoading.step n κ oracle)
        (SimulatorDispatchQueryLoading.steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map
          (SimulatorQueryLoading.observe SimulatorDispatchQueryLoading.view) := by
      unfold PMF.map
      apply bind_congr_of_support
      intro target ht
      obtain ⟨_, _, actual, rfl, _, _, _, _, _⟩ :=
        SimulatorDispatchQueryLoading.native_layout oracle state machine trace query table layout
          positive target ht
      rfl
    _ = _ := by
      rw [middle]
      have dictionaries : (instBEqProd : BEq (Bits n × (Bool × Bits κ))) =
          (@instBEqOfDecidableEq (Key n κ) inferInstance) := lawful_beq_subsingleton _ _
      rw [dictionaries]
      cases h : @List.lookup (Key n κ) (Bits n) instBEqOfDecidableEq query table <;>
        simp [RandomOracle.oracle, h, PMF.pure_map, PMF.map_comp, encodeAnswer, Function.comp_def]

theorem round_complete (oracle : BitOracle State) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (query : Key n κ) (table : Table n κ)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    ∀ result ∈ (runToBoundary (SimulatorQueryPacket.step n κ oracle) SimulatorQueryPacket.readyBoundary
      (SimulatorQueryPacket.steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).support,
      SimulatorQueryPacket.readyBoundary result.1 = true := by
  apply runToBoundary_completes
  intro target ht
  obtain ⟨value, actual, rfl, _⟩ := SimulatorQueryPacket.returned_layout
    oracle state machine trace query table layout positive target ht
  rfl

theorem physicalRound_eq (oracle : BitOracle State) (entries : Nat)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : Key n κ) (table : Table n κ)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (size : table.length ≤ entries) :
    physicalRound oracle entries state machine trace query =
      runToBoundary (SimulatorQueryPacket.step n κ oracle) SimulatorQueryPacket.readyBoundary
        (SimulatorQueryPacket.steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false])) := by
  apply runToBoundary_fuel_stable
  · exact steps_budget query table positive size
  · exact round_complete oracle state machine trace query table layout positive

/-- The new value in the physical table and the response come from the same
native random-bit instructions. Both branches have their actual arrival time. -/
theorem physicalRound_law (oracle : BitOracle State) (entries : Nat)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : Key n κ) (table : Table n κ)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (size : table.length ≤ entries) :
    (physicalRound oracle entries state machine trace query).map
      (fun result => (SimulatorQueryPacket.observation result.1, result.2)) =
    (RandomOracle.oracle table query).map
      (fun answer => (encodeAnswer state trace answer, SimulatorQueryPacket.steps query table)) := by
  rw [physicalRound_eq oracle entries state machine trace query table layout positive size,
    SimulatorQueryPacket.first_joint oracle state machine trace query table layout positive,
    PMF.map_comp]
  have law := congrArg (PMF.map (fun observation => (observation, SimulatorQueryPacket.steps query table)))
    (packet_law oracle state machine trace query table layout positive)
  rw [PMF.map_comp, PMF.map_comp] at law
  rw [SimulatorQueryPacket.run oracle state machine trace query table layout positive, PMF.map_comp] at law
  exact law

/-- The actual frame is retained, with the updated table still on its tape.
It is a legal physical input to the next native round. -/
theorem physicalRound_retained (oracle : BitOracle State) (entries : Nat)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : Key n κ) (table : Table n κ)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (size : table.length ≤ entries)
    (result : SimulatorQueryPacket.Control State × Nat)
    (hr : result ∈ (physicalRound oracle entries state machine trace query).support) :
    ∃ (value : Bits n) (actual : Machine.Configuration),
      SimulatorQueryPacket.ready result.1 = some (NativeCode.frame state trace actual, value.toList) ∧
      actual.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits
        (if (table.lookup query).isSome then table else (query, value) :: table))) ∧
      result.2 = SimulatorQueryPacket.steps query table := by
  rw [physicalRound_eq oracle entries state machine trace query table layout positive size,
    SimulatorQueryPacket.first_joint oracle state machine trace query table layout positive,
    PMF.mem_support_map_iff] at hr
  obtain ⟨target, ht, rfl⟩ := hr
  have full : SimulatorQueryPacket.exported true target ∈
      (TimedExecution.eval (SimulatorQueryPacket.step n κ oracle) (SimulatorQueryPacket.steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).support := by
    rw [SimulatorQueryPacket.run oracle state machine trace query table layout positive,
      PMF.mem_support_map_iff]
    exact ⟨target, ht, rfl⟩
  obtain ⟨value, actual, same, htable⟩ := SimulatorQueryPacket.returned_layout
    oracle state machine trace query table layout positive _ full
  exact ⟨value, actual, by rw [same]; rfl, htable, rfl⟩

/-- Proof-side accounting whose per-step charge is certified above by the
joint law of the physical sampler, insertion and response. -/
noncomputable def costedOracle : Oracle (Key n κ) (Bits n) (Table n κ × Nat) :=
  fun state query => (RandomOracle.oracle state.1 query).map fun answer =>
    ((answer.1, state.2 + SimulatorQueryPacket.steps query state.1), answer.2)

/-- The costed step is the projection of the same physical first-return
distribution, including the pre-existing elapsed server cost. -/
theorem physicalRound_costed (oracle : BitOracle State) (entries : Nat)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : Key n κ) (table : Table n κ) (elapsed : Nat)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (size : table.length ≤ entries) :
    (physicalRound oracle entries state machine trace query).map
      (fun result => (SimulatorQueryPacket.observation result.1, elapsed + result.2)) =
    (costedOracle (table, elapsed) query).map
      (fun answer => (encodeAnswer state trace (answer.1.1, answer.2), answer.1.2)) := by
  have law := congrArg (PMF.map (fun result => (result.1, elapsed + result.2)))
    (physicalRound_law oracle entries state machine trace query table layout positive size)
  simpa only [PMF.map_comp, Function.comp_def, costedOracle] using law

theorem erase_cost (program : CryptoOracle.Program (Key n κ) (Bits n) Result)
    (table : Table n κ) (elapsed : Nat) :
    (program.run costedOracle (table, elapsed)).map (Program.mapState Prod.fst) =
      program.run RandomOracle.oracle table := by
  apply Program.run_state_map
  intro state query
  simp only [costedOracle, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

def updateTable (table : Table n κ) (query : Key n κ) (value : Bits n) : Table n κ :=
  match @List.lookup (Key n κ) (Bits n) instBEqOfDecidableEq query table with
  | some _ => table
  | none => (query, value) :: table

theorem oracle_update (table : Table n κ) (query : Key n κ) (reply : Table n κ × Bits n)
    (hr : reply ∈ (RandomOracle.oracle table query).support) :
    reply.1 = updateTable table query reply.2 := by
  cases h : @List.lookup (Key n κ) (Bits n) instBEqOfDecidableEq query table with
  | some value =>
    simp only [RandomOracle.oracle, h, PMF.mem_support_pure_iff] at hr
    subst reply
    simp [updateTable, h]
  | none =>
    simp only [RandomOracle.oracle, h, PMF.mem_support_map_iff] at hr
    obtain ⟨value, _, rfl⟩ := hr
    simp [updateTable, h]

def advance (state : Table n κ × Nat) (query : Key n κ) (value : Bits n) : Table n κ × Nat :=
  (updateTable state.1 query value, state.2 + SimulatorQueryPacket.steps query state.1)

theorem costed_step (state : Table n κ × Nat) (query : Key n κ)
    (answer : (Table n κ × Nat) × Bits n)
    (ha : answer ∈ (costedOracle state query).support) :
    answer.1 = advance state query answer.2 := by
  rw [costedOracle, PMF.mem_support_map_iff] at ha
  obtain ⟨reply, hr, rfl⟩ := ha
  exact Prod.ext (oracle_update state.1 query reply hr) rfl

/-- The charge is determined by the same transcript and stored answers as
the cache, rather than an independently sampled or independently chosen cost. -/
theorem state_from_trace (program : CryptoOracle.Program (Key n κ) (Bits n) Result)
    (table : Table n κ) (elapsed : Nat)
    (out : Outcome (Key n κ) (Bits n) Result (Table n κ × Nat))
    (ho : out ∈ (program.run costedOracle (table, elapsed)).support) :
    out.state = out.trace.foldl (fun state entry => advance state entry.1 entry.2) (table, elapsed) :=
  Program.run_observe_trace costedOracle id advance costed_step program (table, elapsed) out ho

def enrich (table : Table n κ) (elapsed : Nat)
    (out : Outcome (Key n κ) (Bits n) Result (Table n κ)) :
    Outcome (Key n κ) (Bits n) Result (Table n κ × Nat) :=
  ⟨out.result, out.trace.foldl (fun state entry => advance state entry.1 entry.2) (table, elapsed), out.trace⟩

theorem enrich_erase (program : CryptoOracle.Program (Key n κ) (Bits n) Result)
    (table : Table n κ) (elapsed : Nat)
    (out : Outcome (Key n κ) (Bits n) Result (Table n κ × Nat))
    (ho : out ∈ (program.run costedOracle (table, elapsed)).support) :
    enrich table elapsed (Program.mapState Prod.fst out) = out := by
  have hs := state_from_trace program table elapsed out ho
  cases out
  simp only [enrich, Program.mapState]
  congr 1
  exact hs.symm

theorem reconstruct_cost (program : CryptoOracle.Program (Key n κ) (Bits n) Result)
    (table : Table n κ) (elapsed : Nat) :
    (program.run RandomOracle.oracle table).map (enrich table elapsed) =
      program.run costedOracle (table, elapsed) := by
  rw [← erase_cost program table elapsed, PMF.map_comp]
  calc
    _ = (program.run costedOracle (table, elapsed)).map id := by
      unfold PMF.map
      apply bind_congr_of_support
      intro out ho
      exact congrArg PMF.pure (enrich_erase program table elapsed out ho)
    _ = _ := PMF.map_id _

theorem enrich_table (program : CryptoOracle.Program (Key n κ) (Bits n) Result)
    (table : Table n κ) (elapsed : Nat)
    (out : Outcome (Key n κ) (Bits n) Result (Table n κ))
    (ho : out ∈ (program.run RandomOracle.oracle table).support) :
    (enrich table elapsed out).state.1 = out.state := by
  rw [← erase_cost program table elapsed, PMF.mem_support_map_iff] at ho
  obtain ⟨full, hf, rfl⟩ := ho
  rw [enrich_erase program table elapsed full hf]
  rfl

/-- The old shared realization is extended with the actual per-round costs;
the selected random function and the adaptive execution remain coupled. -/
noncomputable def coupledCost (program : CryptoOracle.Program (Key n κ) (Bits n) Result) :=
  (RandomOracle.Cube.coupled program).map (fun pair => (enrich [] 0 pair.1, pair.2))

theorem coupledCost_execution (program : CryptoOracle.Program (Key n κ) (Bits n) Result) :
    (coupledCost program).map Prod.fst = program.run costedOracle ([], 0) := by
  rw [coupledCost, PMF.map_comp]
  calc
    _ = ((RandomOracle.Cube.coupled program).map Prod.fst).map (enrich [] 0) :=
      (PMF.map_comp Prod.fst (RandomOracle.Cube.coupled program) (enrich [] 0)).symm
    _ = _ := by rw [RandomOracle.Cube.coupled_lazy, reconstruct_cost]

theorem coupledCost_cube (program : CryptoOracle.Program (Key n κ) (Bits n) Result) :
    (coupledCost program).map Prod.snd =
      (RandomOracle.Cube.model (Input := Key n κ) (Output := Bits n)).joint := by
  rw [coupledCost, PMF.map_comp]
  exact RandomOracle.Cube.coupled_cube program

theorem coupledCost_cache (program : CryptoOracle.Program (Key n κ) (Bits n) Result)
    (pair : Outcome (Key n κ) (Bits n) Result (Table n κ × Nat) ×
      (Finset (Key n κ) → (RandomOracle.Cube.cube (Key n κ) (Bits n)).State))
    (hp : pair ∈ (coupledCost program).support) :
    ∀ query, RandomOracle.Cube.view (pair.2 (RandomOracle.Cube.seen pair.1.state.1)) query =
      @List.lookup (Key n κ) (Bits n) instBEqOfDecidableEq query pair.1.state.1 := by
  obtain ⟨original, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  have hlazy : original.1 ∈ (program.run RandomOracle.oracle []).support := by
    rw [← RandomOracle.Cube.coupled_lazy program]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨original, ho, rfl⟩
  intro query
  change RandomOracle.Cube.view
    (original.2 (RandomOracle.Cube.seen (enrich [] 0 original.1).state.1)) query = _
  rw [enrich_table program [] 0 original.1 hlazy]
  exact RandomOracle.Cube.coupled_cache program original ho query

/-- A global capacity leaves enough space for every future adaptive query.
This bound is for native server rounds; source continuation costs are separate. -/
theorem cumulative_bound {program : CryptoOracle.Program (Key n κ) (Bits n) Result} {q : Nat}
    (hq : program.BoundedQueries q) (positive : 0 < n) (capacity : Nat)
    (table : Table n κ) (elapsed : Nat) (room : table.length + q ≤ capacity)
    (out : Outcome (Key n κ) (Bits n) Result (Table n κ × Nat))
    (ho : out ∈ (program.run costedOracle (table, elapsed)).support) :
    out.state.1.length ≤ table.length + q ∧ out.state.2 ≤ elapsed + q * budget n κ capacity := by
  induction hq generalizing table elapsed out with
  | done result q =>
    simp only [Program.run, PMF.mem_support_pure_iff] at ho
    subst out
    simp
  | coin next q h ih =>
    rw [Program.run, PMF.mem_support_bind_iff] at ho
    obtain ⟨bit, _, ho⟩ := ho
    exact ih bit table elapsed room out ho
  | query query next q h ih =>
    rw [Program.run, PMF.mem_support_bind_iff] at ho
    obtain ⟨answer, ha, ho⟩ := ho
    rw [costedOracle, PMF.mem_support_map_iff] at ha
    obtain ⟨reply, hr, rfl⟩ := ha
    rw [PMF.mem_support_map_iff] at ho
    obtain ⟨tail, ht, rfl⟩ := ho
    have growth := (RandomOracle.step table query reply hr).2.2
    have nextRoom : reply.1.length + q ≤ capacity := by omega
    have bound := ih reply.2 reply.1 (elapsed + SimulatorQueryPacket.steps query table) nextRoom tail ht
    have charge : SimulatorQueryPacket.steps query table ≤ budget n κ capacity :=
      steps_budget query table positive (by omega)
    constructor
    · exact bound.1.trans (by omega)
    · change tail.state.2 ≤ _
      calc
        _ ≤ (elapsed + SimulatorQueryPacket.steps query table) + q * budget n κ capacity := bound.2
        _ ≤ (elapsed + budget n κ capacity) + q * budget n κ capacity :=
          Nat.add_le_add_right (Nat.add_le_add_left charge _) _
        _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega

theorem empty_bound {program : CryptoOracle.Program (Key n κ) (Bits n) Result} {q : Nat}
    (hq : program.BoundedQueries q) (positive : 0 < n)
    (out : Outcome (Key n κ) (Bits n) Result (Table n κ × Nat))
    (ho : out ∈ (program.run costedOracle ([], 0)).support) :
    out.state.2 ≤ q * (q * (15 * n + 12 * κ + 26) + 21 * n + 12 * κ + 40) := by
  simpa [budget, slope, overhead, Nat.add_assoc] using
    (cumulative_bound hq positive q [] 0 (by simp) out ho).2

def totalBudget (n κ q : Nat) := q * budget n κ q

theorem coupledCost_bound {program : CryptoOracle.Program (Key n κ) (Bits n) Result} {q : Nat}
    (hq : program.BoundedQueries q) (positive : 0 < n)
    (pair : Outcome (Key n κ) (Bits n) Result (Table n κ × Nat) ×
      (Finset (Key n κ) → (RandomOracle.Cube.cube (Key n κ) (Bits n)).State))
    (hp : pair ∈ (coupledCost program).support) : pair.1.state.2 ≤ totalBudget n κ q := by
  have hcost : pair.1 ∈ (program.run costedOracle ([], 0)).support := by
    rw [← coupledCost_execution program]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨pair, hp, rfl⟩
  simpa [totalBudget, budget, slope, overhead, Nat.add_assoc] using empty_bound hq positive pair.1 hcost

theorem totalBudget_polynomial (width payload queries : Nat → Nat)
    (hw : PolynomiallyBounded width) (hp : PolynomiallyBounded payload)
    (hq : PolynomiallyBounded queries) :
    PolynomiallyBounded (fun size => totalBudget (width size) (payload size) (queries size)) :=
  hq.mul ((hq.mul ((((PolynomiallyBounded.const 15).mul hw).add
    ((PolynomiallyBounded.const 12).mul hp)).add (PolynomiallyBounded.const 26))).add
    ((((PolynomiallyBounded.const 21).mul hw).add
      ((PolynomiallyBounded.const 12).mul hp)).add (PolynomiallyBounded.const 40)))

end Foundation.Hash.Native.PolygraphOracle
