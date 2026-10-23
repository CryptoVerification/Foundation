import Foundation.Examples.NativeOracleExecution

/-! Discharge the concrete caller's obligations and instantiate the continuing
execution theorem. The invariant is actual physical reachability, not an
assumption that the desired caller or service result has already occurred. -/
namespace Foundation.Hash.Native.NativeOracleExecution.Examples.Certified
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric SimulatorQueryRound
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
set_option cbv.warning false

noncomputable abbrev runtime := SimulatorQueryRound.callerStep 1 1 oracle callerCode oracle

/-- Include every intermediate physical state, across both native coin branches. -/
def visited : Nat → Physical → List Physical
  | fuel, control => control :: (if stopped control then [] else match fuel with
    | 0 => []
    | fuel + 1 => (next control).values.flatMap (visited fuel))

theorem paths_visited (fuel : Nat) (control : Physical) (result : Physical × Nat)
    (hs : result ∈ paths fuel control) : result.1 ∈ visited fuel control := by
  induction fuel generalizing control result with
  | zero =>
      simp only [paths] at hs
      split at hs <;> simp_all [visited]
  | succ fuel ih =>
      by_cases h : stopped control = true
      · simp [paths, h] at hs
        subst result
        simp [visited]
      · simp only [paths, h, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_map] at hs
        obtain ⟨middle, hm, final, hf, rfl⟩ := hs
        simp only [visited, h, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_flatMap]
        exact Or.inr ⟨middle, hm, ih middle final hf⟩

theorem eval_visited (fuel time : Nat) (control final : Physical) (ht : time ≤ fuel)
    (hs : final ∈ (eval runtime time control).support) : final ∈ visited fuel control := by
  induction time generalizing fuel control with
  | zero =>
      simp only [TimedExecution.eval, PMF.mem_support_pure_iff] at hs
      subst final
      cases fuel <;> simp [visited]
  | succ time ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          by_cases h : stopped control = true
          · rw [Block.eval_of_absorbing control (stopped_absorbing control h), PMF.mem_support_pure_iff] at hs
            subst final
            simp [visited]
          · rw [TimedExecution.eval] at hs
            simp only [runtime, ← next_law, PMF.mem_support_bind_iff] at hs
            obtain ⟨middle, hm, hf⟩ := hs
            simp only [visited, h, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_flatMap]
            exact Or.inr ⟨middle, (Choice.support _ _).mp hm, ih fuel middle (by omega) hf⟩

/-- Reachability remains closed under actual round execution of any duration. -/
def Reachable (control : Physical) : Prop := ∃ time, control ∈ (eval runtime time initial).support

theorem reachable_visited (control : Physical) (hs : Reachable control) :
    control ∈ visited 224 initial := by
  obtain ⟨time, ht⟩ := hs
  by_cases h : time ≤ 224
  · exact eval_visited 224 time initial control h ht
  · rw [whole_run time (by omega), PMF.mem_support_map_iff] at ht
    obtain ⟨result, hr, rfl⟩ := ht
    exact paths_visited 224 initial result ((paths_support _ _ _).mp hr)

/-- The caller-prefix enumerator includes only the caller's native instructions
and physical request export, stopping at the actual request or native halt. -/
def sourceChoice (frame : Configuration Unit) : Choice (Configuration Unit) :=
  if SourcePrefix.boundary frame then .pure frame else timedChoice callerCode frame

theorem sourceChoice_law (frame : Configuration Unit) :
    (sourceChoice frame).law = SourcePrefix.step callerCode oracle frame := by
  by_cases h : SourcePrefix.boundary frame = true
  · simp [sourceChoice, SourcePrefix.step, h, Choice.law]
  · simp [sourceChoice, SourcePrefix.step, h, timedChoice_law]

def sourceFrames : Nat → Configuration Unit → List (Configuration Unit)
  | 0, frame => [frame]
  | fuel + 1, frame => (sourceChoice frame).values.flatMap (sourceFrames fuel)

theorem sourceFrames_support (fuel : Nat) (frame final : Configuration Unit) :
    final ∈ (eval (SourcePrefix.step callerCode oracle) fuel frame).support ↔ final ∈ sourceFrames fuel frame := by
  induction fuel generalizing frame with
  | zero => simp [TimedExecution.eval, sourceFrames]
  | succ fuel ih =>
      simp only [TimedExecution.eval, ← sourceChoice_law, PMF.mem_support_bind_iff,
        sourceFrames, List.mem_flatMap, Choice.support, ih]

def format (frame : Configuration Unit) : Bool := match frame.control with
  | .awaiting _ raw => raw == [false, false, false, false]
  | _ => true

/-- Only properties of concrete frames are computed: completion, raw format,
trace preservation and physical table size. No logical table is executed. -/
def sourceCertificate (control : Physical) : Bool := match control with
  | .source saved frame =>
      (frame.reverseTrace.length ≤ 2) &&
      (match saved.control with
       | .running machine => machine.inputTape.bits.length ≤ 10
       | _ => false) &&
      (sourceFrames 25 frame).all (fun final => SourcePrefix.boundary final && format final &&
        (final.reverseTrace == frame.reverseTrace))
  | _ => true

theorem checked_sources : (visited 224 initial).all sourceCertificate = true := by decide_cbv

theorem source_facts (session : Session 1 1 Unit Unit) (hr : Reachable (embed session)) :
    session.val.2.reverseTrace.length ≤ 2 ∧
    (retained session).machine.inputTape.bits.length ≤ 10 ∧
    ∀ frame ∈ (eval (SourcePrefix.step callerCode oracle) 25 session.val.2).support,
      SourcePrefix.boundary frame = true ∧ format frame = true ∧
        frame.reverseTrace = session.val.2.reverseTrace := by
  have h := List.all_eq_true.mp checked_sources (embed session) (reachable_visited _ hr)
  change sourceCertificate (.source session.val.1 session.val.2) = true at h
  simp only [sourceCertificate, Bool.and_eq_true, decide_eq_true_eq] at h
  have machine := (retained session).hControl
  change session.val.1.control = .running (retained session).machine at machine
  rw [machine] at h
  refine ⟨h.1.1, of_decide_eq_true h.1.2, ?_⟩
  intro frame hf
  have hh := List.all_eq_true.mp h.2 frame ((sourceFrames_support _ _ _).mp hf)
  simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using hh

theorem table_bound (session : Session 1 1 Unit Unit) (hr : Reachable (embed session)) :
    (retained session).table.length ≤ 1 := by
  have physical := (source_facts session hr).2.1
  have same := (retained session).tableLayout.bits
  have encoded : (Tape.ofBits (SimulatorLookup.tableBits (retained session).table)).bits =
      SimulatorLookup.tableBits (retained session).table := by
    generalize SimulatorLookup.tableBits (retained session).table = bits
    cases bits <;> simp [Tape.ofBits, Tape.bits]
  rw [same, encoded, SimulatorLookup.tableBits_length] at physical
  omega

/-- The concrete caller's request format is proved for every supported
prefix outcome at every reachable physical entry. -/
theorem request_format (session : Session 1 1 Unit Unit) (hr : Reachable (embed session))
    (frame : Configuration Unit)
    (hf : frame ∈ (eval (SourcePrefix.step callerCode oracle) 25 session.val.2).support)
    (caller : Machine.Configuration) (raw : List Bool) (hc : frame.control = .awaiting caller raw) :
    raw = compressionPacket CryptoOracle.RandomOracle.PolygraphExamples.Native.first ++ [false] := by
  have h := ((source_facts session hr).2.2 frame hf).2.1
  have packet : compressionPacket CryptoOracle.RandomOracle.PolygraphExamples.Native.first ++ [false] =
      [false, false, false, false] := by decide
  rw [packet]
  simpa only [format, hc, beq_iff_eq] using h

theorem caller_complete (session : Session 1 1 Unit Unit) (hr : Reachable (embed session))
    (frame : Configuration Unit)
    (hf : frame ∈ (eval (SourcePrefix.step callerCode oracle) 25 session.val.2).support) :
    SourcePrefix.boundary frame = true := ((source_facts session hr).2.2 frame hf).1

noncomputable def selection (session : Session 1 1 Unit Unit) (hr : Reachable (embed session)) :
    Selection oracle callerCode oracle session where
  sourceInput := ⟨session.val.2, 25, fun frame hf => ((source_facts session hr).2.2 frame hf).1⟩
  start := rfl
  replyCap := 133
  valid := by
    intro frame hf caller raw hc
    have formatOK := request_format session hr frame hf caller raw hc
    refine ⟨CryptoOracle.RandomOracle.PolygraphExamples.Native.first, ?_, ?_⟩
    · exact formatOK
    · have bound := PolygraphOracle.steps_budget CryptoOracle.RandomOracle.PolygraphExamples.Native.first
        (retained session).table (Nat.zero_lt_succ 0) (table_bound session hr)
      change SimulatorQueryPacket.steps _ _ + (3 * 1 + 4) ≤ 133
      have : PolygraphOracle.budget 1 1 1 = 126 := rfl
      omega

theorem round_closed (session : Session 1 1 Unit Unit) (hr : Reachable (embed session))
    (output : Session 1 1 Unit Unit)
    (hs : output ∈ ((round oracle (Nat.zero_lt_succ 0) callerCode oracle session (selection session hr)).semantics ()).support) :
    Reachable (embed output) := by
  rw [← (round oracle (Nat.zero_lt_succ 0) callerCode oracle session (selection session hr)).correct,
    PMF.mem_support_map_iff] at hs
  obtain ⟨result, hs, rfl⟩ := hs
  obtain ⟨time, ht⟩ := hr
  refine ⟨time + result.2, ?_⟩
  rw [eval_add, PMF.mem_support_bind_iff]
  exact ⟨embed session, ht, stage_reachable oracle (Nat.zero_lt_succ 0) callerCode oracle session (selection session ⟨time, ht⟩) result hs⟩

/-- Every nonterminating round contributes one real query/response to the
caller's physical transcript. Prefix computation never fabricates a query. -/
theorem round_progress (session : Session 1 1 Unit Unit) (hr : Reachable (embed session))
    (output : Session 1 1 Unit Unit)
    (hs : output ∈ ((round oracle (Nat.zero_lt_succ 0) callerCode oracle session (selection session hr)).semantics ()).support) :
    Halted output ∨ output.val.2.reverseTrace.length = session.val.2.reverseTrace.length + 1 := by
  have hs' : output.val ∈ ((rawRound oracle (Nat.zero_lt_succ 0) callerCode oracle session (selection session hr)).semantics ()).support := by
    rw [← Procedure.certify_semantics (rawRound oracle (Nat.zero_lt_succ 0) callerCode oracle session (selection session hr))
      (fun out => Layout 1 1 out.1)
      (fun _ out ho => round_layout oracle (Nat.zero_lt_succ 0) callerCode oracle session (selection session hr) out ho) (),
      PMF.mem_support_map_iff]
    exact ⟨output, hs, rfl⟩
  rw [rawRound, simulatorSourceRound_semantics, PMF.mem_support_bind_iff] at hs'
  obtain ⟨selected, hSelected, hResponse⟩ := hs'
  have hPrefix : selected.val ∈ (eval (SourcePrefix.step callerCode oracle) 25 session.val.2).support := by
    change selected.val ∈ (eval (SourcePrefix.step callerCode oracle)
      (selection session hr).sourceInput.budget (selection session hr).sourceInput.start).support
    rw [← simulatorCertifiedPrefix_erase (oracle := oracle) callerCode oracle (retained session)
      (selection session hr).sourceInput (selection session hr).replyCap (selection session hr).valid,
      PMF.mem_support_map_iff]
    exact ⟨selected, hSelected, rfl⟩
  have facts := (source_facts session hr).2.2 selected.val hPrefix
  unfold simulatorResponse at hResponse
  split at hResponse
  · next caller raw hc =>
      rw [simulatorWaitingService_semantics, SimulatorQueryService.simulatorService,
        PacketResponseService.service_semantics, PMF.mem_support_map_iff] at hResponse
      obtain ⟨packet, _, he⟩ := hResponse
      have traceEq := congrArg (fun frames : Configuration Unit × Configuration Unit => frames.2.reverseTrace) he
      simp only [NativeCallback.resumed] at traceEq
      exact Or.inr (by rw [← traceEq, List.length_cons, facts.2.2])
  · next hNot =>
      change output.val ∈ (PMF.pure ((retained session).saved, selected.val)).support at hResponse
      rw [PMF.mem_support_pure_iff] at hResponse
      apply Or.inl
      change Reification.terminal output.val.2.control = true
      rw [hResponse]
      have boundary := facts.1
      cases hc : selected.val.control <;>
        simp_all [SourcePrefix.boundary, Reification.terminal]

noncomputable def policy : Policy (n := 1) (κ := 1) oracle (Nat.zero_lt_succ 0) callerCode oracle where
  admitted := fun session => Reachable (embed session)
  select := fun session => selection session.val session.property
  closed := fun session output hs => round_closed session.val session.property output hs
  cap := 159
  bounded := fun _ => by change 25 + (1 + 133) ≤ 159; decide

noncomputable def initialSession : Session 1 1 Unit Unit :=
  ⟨(⟨(), .running {inputTape := Tape.ofBits (SimulatorLookup.tableBits ([] : PolygraphOracle.Table 1 1))}, []⟩,
     Configuration.initial () []),
    ⟨[], _, rfl, Tape.Equivalent.refl _⟩⟩

noncomputable def start : Valid oracle (Nat.zero_lt_succ 0) callerCode oracle policy :=
  ⟨initialSession, 0, by simp [initialSession, embed, initial, TimedExecution.eval]⟩

noncomputable abbrev run (count : Nat) := execution oracle (Nat.zero_lt_succ 0) callerCode oracle policy count start

/-- Unpack the certified stage without changing the physical outcome. -/
theorem checked_progress (session : Valid oracle (Nat.zero_lt_succ 0) callerCode oracle policy)
    (result : Valid oracle (Nat.zero_lt_succ 0) callerCode oracle policy × Nat)
    (hs : result ∈ (checkedStage oracle (Nat.zero_lt_succ 0) callerCode oracle policy session).outcome.support) :
    Halted result.1.val ∨
      result.1.val.val.2.reverseTrace.length = session.val.val.2.reverseTrace.length + 1 := by
  have original : (result.1.val, result.2) ∈
      ((round oracle (Nat.zero_lt_succ 0) callerCode oracle session.val (selection session.val session.property)).costed ()).support := by
    rw [← Procedure.certify_costed
      (round oracle (Nat.zero_lt_succ 0) callerCode oracle session.val (selection session.val session.property))
      policy.admitted (fun _ output ho => policy.closed session output ho) (), PMF.mem_support_map_iff]
    exact ⟨result, hs, rfl⟩
  exact round_progress session.val session.property result.1.val
    ((round oracle (Nat.zero_lt_succ 0) callerCode oracle session.val (selection session.val session.property)).result_support () _ original)

theorem halt_persists (session : Valid oracle (Nat.zero_lt_succ 0) callerCode oracle policy)
    (count : Nat) (result : Valid oracle (Nat.zero_lt_succ 0) callerCode oracle policy × Nat)
    (hs : result ∈ (execution oracle (Nat.zero_lt_succ 0) callerCode oracle policy count session).outcome.support)
    (halted : Halted session.val) : Halted result.1.val := by
  have reached := execution_reachable oracle (Nat.zero_lt_succ 0) callerCode oracle policy count session result hs
  change embed result.1.val ∈ (eval runtime result.2 (embed session.val)).support at reached
  rw [Block.eval_of_absorbing _ (halted_absorbing oracle callerCode oracle session.val halted),
    PMF.mem_support_pure_iff] at reached
  have same := congrArg stopped reached
  change Reification.terminal result.1.val.val.2.control = true
  change Reification.terminal result.1.val.val.2.control =
    Reification.terminal session.val.val.2.control at same
  exact same.trans halted

/-- If execution has not halted, every completed round must have made an
additional query. This is a progress argument about the physical transcript. -/
theorem trace_progress (count : Nat) (session : Valid oracle (Nat.zero_lt_succ 0) callerCode oracle policy)
    (result : Valid oracle (Nat.zero_lt_succ 0) callerCode oracle policy × Nat)
    (hs : result ∈ (execution oracle (Nat.zero_lt_succ 0) callerCode oracle policy count session).outcome.support)
    (active : ¬Halted result.1.val) :
    session.val.val.2.reverseTrace.length + count ≤ result.1.val.val.2.reverseTrace.length := by
  induction count generalizing session result with
  | zero =>
      change result ∈ (PMF.pure (session, 0)).support at hs
      rw [PMF.mem_support_pure_iff] at hs
      subst result
      dsimp only
      omega
  | succ count ih =>
      rw [execution_succ, PMF.mem_support_bind_iff] at hs
      obtain ⟨middle, hm, hs⟩ := hs
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨final, hf, rfl⟩ := hs
      have middleActive : ¬Halted middle.1.val := fun h =>
        active (halt_persists middle.1 count final hf h)
      have first := (checked_progress session middle hm).resolve_left middleActive
      have rest := ih middle.1 final hf active
      dsimp only at *
      omega

/-- The initial caller can make only two queries; its third round is the
post-response computation and genuine native halt. No stopping premise remains. -/
theorem three_rounds_stop (result : Valid oracle (Nat.zero_lt_succ 0) callerCode oracle policy × Nat)
    (hs : result ∈ (run 3).outcome.support) : Halted result.1.val := by
  by_contra h
  have progress := trace_progress 3 start result hs h
  have bounded := (source_facts result.1.val result.1.property).1
  omega

/-- Application of the general execution theorem with all caller-specific
obligations proved above. The certified bound is 3 * 159 = 477 transitions;
actual elapsed time is retained in the execution distribution. -/
theorem certified_execution (horizon : Nat) (enough : 477 ≤ horizon) :
    eval runtime horizon initial = (run 3).outcome.map
      (fun result => physical oracle (Nat.zero_lt_succ 0) callerCode oracle policy result.1) := by
  exact execution_final oracle (Nat.zero_lt_succ 0) callerCode oracle policy 3 start three_rounds_stop horizon enough

theorem certified_correct (final : Physical)
    (hs : final ∈ ((run 3).outcome.map
      (fun result => physical oracle (Nat.zero_lt_succ 0) callerCode oracle policy result.1)).support) :
    stopped final = true ∧ correctResult final = true := by
  rw [← certified_execution 477 (Nat.le_refl _)] at hs
  exact whole_run_correct 477 (by decide) final hs

/-- All four caller obligations have been discharged. Every certified
three-round result halts, has the correct physical tapes and costs at most
477 transitions, with no remaining caller-specific hypothesis. -/
theorem certified_result (result : Valid oracle (Nat.zero_lt_succ 0) callerCode oracle policy × Nat)
    (hs : result ∈ (run 3).outcome.support) :
    Halted result.1.val ∧
      correctResult (physical oracle (Nat.zero_lt_succ 0) callerCode oracle policy result.1) = true ∧
      result.2 ≤ 477 := by
  refine ⟨three_rounds_stop result hs, ?_, ?_⟩
  · apply (certified_correct _ ?_).2
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hs, rfl⟩
  · exact execution_cost_bound oracle (Nat.zero_lt_succ 0) callerCode oracle policy 3 start result hs

end Foundation.Hash.Native.NativeOracleExecution.Examples.Certified
