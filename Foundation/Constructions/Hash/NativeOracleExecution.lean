import Foundation.Constructions.Hash.NativeSimulatorQueryRound
import Foundation.Constructions.Hash.PolygraphOracle

/-! A single continuing caller/component execution. Layout certificates are
proof coordinates: every stage enters with the exact physical frames returned
by the previous stage. The caller code and both oracle transition functions
remain fixed throughout selection, service, response loading and termination. -/
namespace Foundation.Hash.Native.NativeOracleExecution
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric SimulatorQueryRound
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {n κ : Nat} {State Source : Type}

/-- Ordinary lazy-random-oracle semantics of the physical service, jointly
with the entire resumed caller frame. No terminal-recognition side condition
from the hash construction is needed for the lazy sampling branch. -/
theorem service_lazy (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (query : PolygraphOracle.Key n κ) (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool)) (request : List Bool) :
    ((SimulatorQueryService.simulatorService oracle ret.table ret.saved.state ret.machine ret.saved.reverseTrace
      query ret.tableLayout positive code callerOracle caller callerState callerTrace request).semantics ()).map
        (fun output => (SimulatorDispatchQueryLoading.view output.1, output.2)) =
      (RandomOracle.oracle ret.table query).map (fun answer =>
        ((ret.saved.state, ret.saved.reverseTrace, some (SimulatorLookup.tableBits answer.1, answer.2.toList)),
          NativeCallback.resumed caller callerState callerTrace request answer.2.toList)) := by
  have obs := PolygraphOracle.packet_law oracle ret.saved.state ret.machine ret.saved.reverseTrace
    query ret.table ret.tableLayout positive
  rw [SimulatorQueryPacket.run oracle ret.saved.state ret.machine ret.saved.reverseTrace
    query ret.table ret.tableLayout positive, PMF.map_comp] at obs
  rw [SimulatorQueryService.simulatorService, PacketResponseService.service_semantics, PMF.map_comp]
  have rhs := congrArg (PMF.map (SimulatorQueryService.observationPair caller callerState callerTrace request ret.saved)) obs
  rw [PMF.map_comp, PMF.map_comp] at rhs
  change _ = _ at rhs
  calc
    _ = _ := ?_
    _ = _ := rhs
  rw [SimulatorQueryService.simulatorPacketHandler]
  unfold SimulatorQueryService.simulatorPacketProcedure
  simp only [TimedExecution.Procedure.ofFixed, PMF.map_comp]
  unfold PMF.map
  apply bind_congr_of_support
  intro target ht
  obtain ⟨value, before, actual, rfl, halted, input, blank, outputEq, bits⟩ :=
    SimulatorDispatchQueryLoading.native_layout oracle ret.saved.state ret.machine ret.saved.reverseTrace
      query ret.table ret.tableLayout positive target ht
  rfl

/-- The same correspondence retains actual service time, including the
physical response transfer, correlated with table and resumed caller. -/
theorem service_lazy_costed (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (query : PolygraphOracle.Key n κ) (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool)) (request : List Bool) :
    ((SimulatorQueryService.simulatorService oracle ret.table ret.saved.state ret.machine ret.saved.reverseTrace
      query ret.tableLayout positive code callerOracle caller callerState callerTrace request).costed ()).map
        (fun result => ((SimulatorDispatchQueryLoading.view result.1.1, result.1.2), result.2)) =
      (RandomOracle.oracle ret.table query).map (fun answer =>
        (((ret.saved.state, ret.saved.reverseTrace, some (SimulatorLookup.tableBits answer.1, answer.2.toList)),
          NativeCallback.resumed caller callerState callerTrace request answer.2.toList),
          SimulatorQueryPacket.steps query ret.table + (3 * n + 4))) := by
  have law := congrArg (PMF.map (fun output => (output, SimulatorQueryPacket.steps query ret.table + (3 * n + 4))))
    (service_lazy oracle positive code callerOracle ret query caller callerState callerTrace request)
  rw [PMF.map_comp, PMF.map_comp] at law
  calc
    _ = _ := ?_
    _ = _ := law
  rw [SimulatorQueryService.simulatorService_costed, PMF.map_comp,
    SimulatorQueryService.simulatorService, PacketResponseService.service_semantics, PMF.map_comp]
  unfold SimulatorQueryService.simulatorPacketHandler SimulatorQueryService.simulatorPacketProcedure
  simp only [TimedExecution.Procedure.ofFixed, PMF.map_comp]
  unfold PMF.map
  apply bind_congr_of_support
  intro target ht
  obtain ⟨value, before, actual, rfl, halted, input, blank, outputEq, bits⟩ :=
    SimulatorDispatchQueryLoading.native_layout oracle ret.saved.state ret.machine ret.saved.reverseTrace
      query ret.table ret.tableLayout positive target ht
  simp only [Function.comp_def, SimulatorQueryService.exitRead, NativeCode.frame, bits, Bits.length_toList]

/-- A retained physical frame contains a well-formed private table. -/
def Layout (n κ : Nat) (saved : Configuration State) : Prop :=
  ∃ (table : CompressionTable (Bits κ) (Bits n)) (machine : Machine.Configuration),
    saved.control = .running machine ∧
      machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table))

/-- Both complete physical frames, with only a proof of private layout added. -/
abbrev Session (n κ : Nat) (State Source : Type) :=
  {frames : Configuration State × Configuration Source // Layout n κ frames.1}

def embed (session : Session n κ State Source) :
    PacketResponseSource.Control (SimulatorQueryPacket.Control State) Source (Configuration State) :=
  .source session.val.1 session.val.2

noncomputable def retained (session : Session n κ State Source) : Retained n κ State where
  table := session.property.choose
  saved := session.val.1
  machine := session.property.choose_spec.choose
  hControl := session.property.choose_spec.choose_spec.1
  tableLayout := session.property.choose_spec.choose_spec.2

/-- The existing physical service really returns a reusable table. This is
proved from its native tape invariant, rather than assumed at the handoff. -/
theorem response_layout (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (cap : Nat) (selected : {frame // SimulatorAdmissible ret.table cap frame})
    (output : Configuration State × Configuration Source)
    (hs : output ∈ ((simulatorResponse oracle positive code callerOracle ret cap selected).semantics ()).support) :
    Layout n κ output.1 := by
  unfold simulatorResponse at hs
  split at hs
  · next caller raw hc =>
      rw [simulatorWaitingService_semantics] at hs
      exact SimulatorQueryService.simulatorService_frame oracle ret.table ret.saved.state ret.machine
        ret.saved.reverseTrace _ ret.tableLayout positive code callerOracle caller selected.val.state
        selected.val.reverseTrace _ output hs
  · change output ∈ (PMF.pure (ret.saved, selected.val)).support at hs
    rw [PMF.mem_support_pure_iff] at hs
    subst output
    exact ⟨ret.table, ret.machine, ret.hControl, ret.tableLayout⟩

/-- The proof obligations concern actual caller code, not an abstract query
chosen by the proof: run to its next request or halt, check packet format and
bound the physical response. The start must be the unchanged caller frame. -/
structure Selection (oracle : BitOracle State) (code : Code) (callerOracle : BitOracle Source)
    (session : Session n κ State Source) where
  sourceInput : SourcePrefix.Input code callerOracle
  start : sourceInput.start = session.val.2
  replyCap : Nat
  valid : ∀ frame ∈ (eval (SourcePrefix.step code callerOracle) sourceInput.budget sourceInput.start).support,
    SimulatorAdmissible (retained session).table replyCap frame

noncomputable def rawRound (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) (session : Session n κ State Source)
    (selection : Selection oracle code callerOracle session) :=
  simulatorSourceRound oracle positive code callerOracle (retained session)
    selection.sourceInput selection.replyCap selection.valid

theorem round_layout (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) (session : Session n κ State Source)
    (selection : Selection oracle code callerOracle session)
    (output : Configuration State × Configuration Source)
    (hs : output ∈ ((rawRound oracle positive code callerOracle session selection).semantics ()).support) :
    Layout n κ output.1 := by
  rw [rawRound, simulatorSourceRound_semantics, PMF.mem_support_bind_iff] at hs
  obtain ⟨selected, _, hs⟩ := hs
  exact response_layout oracle positive code callerOracle (retained session) selection.replyCap selected output hs

/-- Certification preserves the joint distribution of full frames and time. -/
noncomputable def round (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) (session : Session n κ State Source)
    (selection : Selection oracle code callerOracle session) :
    Procedure (callerStep n κ oracle code callerOracle) Unit (Session n κ State Source) :=
  (rawRound oracle positive code callerOracle session selection).certify
    (fun output => Layout n κ output.1)
    (fun _ output hs => round_layout oracle positive code callerOracle session selection output hs)

theorem round_costed (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) (session : Session n κ State Source)
    (selection : Selection oracle code callerOracle session) :
    ((round oracle positive code callerOracle session selection).costed ()).map
      (fun result => (result.1.val, result.2)) =
        (rawRound oracle positive code callerOracle session selection).costed () :=
  Procedure.certify_costed _ _ _ ()

theorem round_operational (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) (session : Session n κ State Source)
    (selection : Selection oracle code callerOracle session) :
    Procedure.Operational (round oracle positive code callerOracle session selection) := by
  apply Procedure.operational_certify
  exact simulatorSourceRound_operational oracle positive code callerOracle (retained session)
    selection.sourceInput selection.replyCap selection.valid

noncomputable def stage (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) (session : Session n κ State Source)
    (selection : Selection oracle code callerOracle session) :
    Stage (callerStep n κ oracle code callerOracle) embed session where
  budget := selection.sourceInput.budget + (1 + selection.replyCap)
  outcome := (round oracle positive code callerOracle session selection).costed ()
  bounded := (round oracle positive code callerOracle session selection).bounded ()
  law := by
    intro horizon enough
    have h := (round oracle positive code callerOracle session selection).law () horizon enough
    change eval (callerStep n κ oracle code callerOracle) horizon
      (PacketResponseSource.Control.source session.val.1 selection.sourceInput.start) =
      ((round oracle positive code callerOracle session selection).costed ()).bind
        (fun result => eval (callerStep n κ oracle code callerOracle) (horizon - result.2) (embed result.1)) at h
    simpa only [selection.start, embed] using h

/-- Each reported return is reachable at its reported time, in the same
fixed transition system. Residual distribution equality alone is not used
as a substitute for this operational fact. -/
theorem stage_reachable (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) (session : Session n κ State Source)
    (selection : Selection oracle code callerOracle session) (result : Session n κ State Source × Nat)
    (hs : result ∈ (stage oracle positive code callerOracle session selection).outcome.support) :
    embed result.1 ∈ (eval (callerStep n κ oracle code callerOracle) result.2 (embed session)).support := by
  have h := round_operational oracle positive code callerOracle session selection () result hs
  change embed result.1 ∈ (eval _ result.2 (.source session.val.1 selection.sourceInput.start)).support at h
  simpa only [selection.start, embed] using h

/-- A caller-specific invariant restricts certificates and uniform bounds
 to reachable, well-formed sessions. In particular no bound on all arbitrary
 physical tables or malformed caller configurations is required. -/
structure Policy (oracle : BitOracle State) (positive : 0 < n)
    (code : Code) (callerOracle : BitOracle Source) where
  admitted : Session n κ State Source → Prop
  select : ∀ session : {s // admitted s}, Selection oracle code callerOracle session.val
  closed : ∀ session output,
    output ∈ ((round oracle positive code callerOracle session.val (select session)).semantics ()).support →
      admitted output
  cap : Nat
  bounded : ∀ session, (select session).sourceInput.budget + (1 + (select session).replyCap) ≤ cap

variable (oracle : BitOracle State) (positive : 0 < n) (code : Code) (callerOracle : BitOracle Source)
    (policy : Policy (κ := κ) oracle positive code callerOracle)

abbrev Valid := {session // policy.admitted session}

def physical (session : Valid oracle positive code callerOracle policy) := embed session.val

noncomputable def checkedRound (session : Valid oracle positive code callerOracle policy) :=
  (round oracle positive code callerOracle session.val (policy.select session)).certify
    policy.admitted (fun _ output hs => policy.closed session output hs)

noncomputable def checkedStage (session : Valid oracle positive code callerOracle policy) :
    Stage (callerStep n κ oracle code callerOracle) (physical oracle positive code callerOracle policy) session where
  budget := (policy.select session).sourceInput.budget + (1 + (policy.select session).replyCap)
  outcome := (checkedRound oracle positive code callerOracle policy session).costed ()
  bounded := (checkedRound oracle positive code callerOracle policy session).bounded ()
  law := by
    intro horizon enough
    have h := (checkedRound oracle positive code callerOracle policy session).law () horizon enough
    change eval (callerStep n κ oracle code callerOracle) horizon
      (PacketResponseSource.Control.source session.val.val.1 (policy.select session).sourceInput.start) =
      ((checkedRound oracle positive code callerOracle policy session).costed ()).bind
        (fun result => eval (callerStep n κ oracle code callerOracle) (horizon - result.2)
          (physical oracle positive code callerOracle policy result.1)) at h
    simpa only [(policy.select session).start, physical, embed] using h

/-- Repeated physical rounds. A final round can consist of caller computation
and genuine halt, with no request and zero response duration. -/
noncomputable def execution (count : Nat) (session : Valid oracle positive code callerOracle policy) :=
  Stage.iterate (checkedStage oracle positive code callerOracle policy) policy.cap policy.bounded count session

theorem execution_budget (count : Nat) (session : Valid oracle positive code callerOracle policy) :
    (execution oracle positive code callerOracle policy count session).budget = count * policy.cap :=
  Stage.iterate_budget _ _ _ _ _

/-- Recursion exposes the exact sum of actual caller and service durations.
Certified upper bounds are not substituted for elapsed time. -/
theorem execution_succ (count : Nat) (session : Valid oracle positive code callerOracle policy) :
    (execution oracle positive code callerOracle policy (count + 1) session).outcome =
      (checkedStage oracle positive code callerOracle policy session).outcome.bind (fun middle =>
        (execution oracle positive code callerOracle policy count middle.1).outcome.map
          (fun final => (final.1, middle.2 + final.2))) := rfl

theorem checkedStage_reachable (session : Valid oracle positive code callerOracle policy)
    (result : Valid oracle positive code callerOracle policy × Nat)
    (hs : result ∈ (checkedStage oracle positive code callerOracle policy session).outcome.support) :
    physical oracle positive code callerOracle policy result.1 ∈
      (eval (callerStep n κ oracle code callerOracle) result.2
        (physical oracle positive code callerOracle policy session)).support := by
  have h := Procedure.operational_certify _
    (round_operational oracle positive code callerOracle session.val (policy.select session))
    policy.admitted (fun _ output hs => policy.closed session output hs) () result hs
  change embed result.1.val ∈ (eval (callerStep n κ oracle code callerOracle) result.2
    (PacketResponseSource.Control.source session.val.val.1 (policy.select session).sourceInput.start)).support at h
  simpa only [(policy.select session).start, physical, embed] using h

theorem execution_reachable (count : Nat) (session : Valid oracle positive code callerOracle policy)
    (result : Valid oracle positive code callerOracle policy × Nat)
    (hs : result ∈ (execution oracle positive code callerOracle policy count session).outcome.support) :
    physical oracle positive code callerOracle policy result.1 ∈
      (eval (callerStep n κ oracle code callerOracle) result.2
        (physical oracle positive code callerOracle policy session)).support := by
  induction count generalizing session result with
  | zero =>
      change result ∈ (PMF.pure (session, 0)).support at hs
      rw [PMF.mem_support_pure_iff] at hs
      subst result
      simp [TimedExecution.eval]
  | succ count ih =>
      rw [execution_succ, PMF.mem_support_bind_iff] at hs
      obtain ⟨middle, hm, hs⟩ := hs
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨final, hf, rfl⟩ := hs
      rw [eval_add, PMF.mem_support_bind_iff]
      exact ⟨physical oracle positive code callerOracle policy middle.1,
        checkedStage_reachable oracle positive code callerOracle policy session middle hm, ih middle.1 final hf⟩

/-- Continue the same transition function after the sum of actual times. -/
theorem execution_law (count : Nat) (session : Valid oracle positive code callerOracle policy)
    (horizon : Nat) (enough : count * policy.cap ≤ horizon) :
    eval (callerStep n κ oracle code callerOracle) horizon (physical oracle positive code callerOracle policy session) =
      (execution oracle positive code callerOracle policy count session).outcome.bind
        (fun result => eval (callerStep n κ oracle code callerOracle) (horizon - result.2)
          (physical oracle positive code callerOracle policy result.1)) :=
  (execution oracle positive code callerOracle policy count session).law horizon (by
    rw [execution_budget]; exact enough)

theorem execution_cost_bound (count : Nat) (session : Valid oracle positive code callerOracle policy)
    (result : Valid oracle positive code callerOracle policy × Nat)
    (hs : result ∈ (execution oracle positive code callerOracle policy count session).outcome.support) :
    result.2 ≤ count * policy.cap := by
  simpa only [execution_budget] using
    (execution oracle positive code callerOracle policy count session).bounded result hs

/-- An explicit whole-run stopping obligation. Awaiting another request is
not termination. Local format/response bounds do not imply this condition. -/
def Halted (session : Session n κ State Source) : Prop :=
  Reification.terminal session.val.2.control = true

theorem halted_absorbing (session : Session n κ State Source) (h : Halted session) :
    callerStep n κ oracle code callerOracle (embed session) = PMF.pure (embed session) := by
  rcases session with ⟨⟨saved, frame⟩, layout⟩
  cases hc : frame.control <;>
    simp_all [Halted, Reification.terminal, callerStep, embed, PacketResponseSource.step,
      Reification.timedStep, PMF.pure_map]

/-- The final caller computation is inside the same machine run. The
right-hand side keeps the complete final private/caller frames. -/
theorem execution_final (count : Nat) (session : Valid oracle positive code callerOracle policy)
    (stops : ∀ result ∈ (execution oracle positive code callerOracle policy count session).outcome.support,
      Halted result.1.val)
    (horizon : Nat) (enough : count * policy.cap ≤ horizon) :
    eval (callerStep n κ oracle code callerOracle) horizon (physical oracle positive code callerOracle policy session) =
      (execution oracle positive code callerOracle policy count session).outcome.map
        (fun result => physical oracle positive code callerOracle policy result.1) := by
  apply Stage.final_law
  · intro result hs
    exact halted_absorbing oracle code callerOracle result.1.val (stops result hs)
  · rw [execution_budget]
    exact enough

/-- Include caller computation, ownership transfer and physical response
loading in addition to the already established component packet bound. -/
def roundBudget (caller n κ capacity : Nat) : Nat :=
  caller + (1 + (PolygraphOracle.budget n κ capacity + (3 * n + 4)))

theorem selection_budget (session : Session n κ State Source)
    (selection : Selection oracle code callerOracle session)
    (caller capacity : Nat) (hCaller : selection.sourceInput.budget ≤ caller)
    (hReply : selection.replyCap ≤ PolygraphOracle.budget n κ capacity + (3 * n + 4)) :
    (stage oracle positive code callerOracle session selection).budget ≤ roundBudget caller n κ capacity := by
  change selection.sourceInput.budget + (1 + selection.replyCap) ≤ _
  unfold roundBudget
  omega

/-- The scalar bound is conditional on caller-specific certificates. It is
not a compiler producing uniform code or an unconditional PPT claim. -/
theorem wholeBudget_polynomial (rounds caller width payload capacity : Nat → Nat)
    (hr : PolynomiallyBounded rounds) (hc : PolynomiallyBounded caller)
    (hw : PolynomiallyBounded width) (hp : PolynomiallyBounded payload)
    (hL : PolynomiallyBounded capacity) :
    PolynomiallyBounded (fun size => rounds size * roundBudget (caller size)
      (width size) (payload size) (capacity size)) :=
  hr.mul (hc.add ((PolynomiallyBounded.const 1).add
    (((hL.mul ((((PolynomiallyBounded.const 15).mul hw).add
        ((PolynomiallyBounded.const 12).mul hp)).add (PolynomiallyBounded.const 26))).add
      ((((PolynomiallyBounded.const 21).mul hw).add
        ((PolynomiallyBounded.const 12).mul hp)).add (PolynomiallyBounded.const 40))).add
      (((PolynomiallyBounded.const 3).mul hw).add (PolynomiallyBounded.const 4)))))

end Foundation.Hash.Native.NativeOracleExecution
