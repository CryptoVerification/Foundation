import Foundation.Constructions.Hash.NativeOracleExecution
import Foundation.Examples.PolygraphOracle

/-! Exhaustive finite execution of one unchanged caller/server controller.
Only actual random instructions branch. Deterministic transitions are not
charged as oracle capabilities or evaluated by a host-side table lookup. -/
namespace Foundation.Hash.Native.NativeOracleExecution.Examples
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option cbv.warning false
set_option maxHeartbeats 3000000

inductive Choice (α : Type) where
  | pure : α → Choice α
  | coin : α → α → Choice α

def Choice.map {α β : Type} (f : α → β) : Choice α → Choice β
  | .pure a => .pure (f a)
  | .coin a b => .coin (f a) (f b)

noncomputable def Choice.law {α : Type} : Choice α → PMF α
  | .pure a => PMF.pure a
  | .coin a b => sampleBit.map (fun bit => if bit then b else a)

def Choice.values {α : Type} : Choice α → List α
  | .pure a => [a]
  | .coin a b => [a, b]

theorem Choice.map_law {α β : Type} (f : α → β) (choice : Choice α) :
    (choice.map f).law = choice.law.map f := by
  cases choice <;> simp [Choice.map, Choice.law, PMF.map_comp, Function.comp_def, PMF.pure_map]
  congr 1
  funext bit
  cases bit <;> rfl

theorem Choice.support {α : Type} (choice : Choice α) (value : α) :
    value ∈ choice.law.support ↔ value ∈ choice.values := by
  cases choice with
  | pure => simp [law, values]
  | coin a b =>
      simp only [law, PMF.mem_support_map_iff, values, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨bit, _, rfl⟩
        cases bit <;> simp
      · rintro (rfl | rfl)
        · exact ⟨false, by simp [sampleBit, uniform], rfl⟩
        · exact ⟨true, by simp [sampleBit, uniform], rfl⟩

def noOracle (_ : Unit) (_ : List Bool) : Unit × List Bool := ((), [])
noncomputable def oracle : BitOracle Unit := fun state request => PMF.pure (noOracle state request)

/-- Execute a caller/component native instruction using the existing
instruction decoder; the local coin is the sole branching operation. -/
def timedChoice (code : Code) (frame : Configuration Unit) : Choice (Configuration Unit) :=
  if Reification.terminal frame.control then .pure frame else
    match transition code frame with
    | .deterministic next => .pure next
    | .random zero one => .coin zero one
    | .oracleCall caller request =>
        let response := noOracle frame.state request
        .pure ⟨response.1, .loading caller response.2 {}, (request, response.2) :: frame.reverseTrace⟩

theorem timedChoice_law (code : Code) (frame : Configuration Unit) :
    (timedChoice code frame).law = Reification.timedStep code oracle frame := by
  by_cases ht : Reification.terminal frame.control = true
  · simp [timedChoice, Reification.timedStep, ht, Choice.law]
  · simp only [timedChoice, Reification.timedStep, ht, Bool.false_eq_true, ↓reduceIte]
    rw [← Reification.step_eq_perform]
    cases h : transition code frame <;> simp [h, Interactive.step, Choice.law, oracle, noOracle, PMF.pure_map]

/-- The actual cell-aware exporter with empty fallback native code. -/
def exportNext : ResponseExport.Control → ResponseExport.Control
  | .running machine => if machine.halted then .rewinding machine.outputTape
      else .running {machine with halted := true}
  | .rewinding tape => if (tape.left.getD 0 none).isSome then .rewinding tape.moveLeft
      else .collecting tape []
  | .collecting tape reversed => match tape.current with
      | none => .reversing reversed []
      | some bit => .collecting tape.moveRight (bit :: reversed)
  | .reversing remaining packet => match remaining with
      | [] => .returned packet
      | bit :: rest => .reversing rest (bit :: packet)
  | .returned packet => .returned packet

theorem exportNext_law (control : ResponseExport.Control) :
    PMF.pure (exportNext control) = CellResponseExport.step [] control := by
  cases control with
  | running machine => cases h : machine.halted <;> simp [exportNext, CellResponseExport.step, h, stepPMF, Machine.next, PMF.pure_map]
  | rewinding tape => simp [exportNext, CellResponseExport.step]; split <;> rfl
  | collecting tape reversed => cases h : tape.current <;> simp [exportNext, CellResponseExport.step, h]
  | reversing remaining packet => cases remaining <;> rfl
  | returned => rfl

def loadNext : NativePacketService.Control → NativePacketService.Control
  | .loading [] tape => .rewinding tape
  | .loading (bit :: rest) tape => .advancing rest (tape.write (some bit))
  | .advancing rest tape => .loading rest tape.moveRight
  | .rewinding tape => match tape.left with
      | [] => .prepared {outputTape := tape}
      | _ :: _ => .rewinding tape.moveLeft
  | .prepared machine => .executing (.running machine)
  | .executing component => .executing (exportNext component)

theorem loadNext_law (control : NativePacketService.Control) :
    PMF.pure (loadNext control) = NativePacketService.step [] control := by
  cases control with
  | loading remaining tape => cases remaining <;> rfl
  | advancing => rfl
  | rewinding tape => cases h : tape.left <;> simp [loadNext, NativePacketService.step, h]
  | prepared => rfl
  | executing component => rw [NativePacketService.step, ← exportNext_law, PMF.pure_map]; rfl

def packetChoice (control : SimulatorQueryPacket.Control Unit) : Choice (SimulatorQueryPacket.Control Unit) :=
  match control with
  | .admitting state machine trace request => .pure (.running (.computing
      (SimulatorQueryLoading.loadingFrame 1 1 state machine trace request)))
  | .running (.computing frame) =>
      if Reification.terminal frame.control then
        match frame.control with
        | .running machine => .pure (.running (.exporting frame (.running machine)))
        | _ => .pure (.running (.exporting frame (.returned [])))
      else (timedChoice (SimulatorQueryPacket.code 1 1) frame).map (fun next => .running (.computing next))
  | .running (.exporting frame exporter) => .pure (.running (.exporting frame (exportNext exporter)))

theorem packetChoice_law (control : SimulatorQueryPacket.Control Unit) :
    (packetChoice control).law = SimulatorQueryPacket.step 1 1 oracle control := by
  cases control with
  | admitting => rfl
  | running component =>
      cases component with
      | computing frame =>
          by_cases ht : Reification.terminal frame.control = true
          · simp only [packetChoice, SimulatorQueryPacket.step, NativePacketComponent.step, ht, ↓reduceIte]
            cases frame.control <;> simp only [Choice.law, PMF.pure_map]
          · simp only [packetChoice, SimulatorQueryPacket.step, NativePacketComponent.step, ht,
              Bool.false_eq_true, ↓reduceIte, Choice.map_law, timedChoice_law, PMF.map_comp,
              Function.comp_def]
      | exporting frame exporter =>
          simp only [packetChoice, Choice.law, SimulatorQueryPacket.step, NativePacketComponent.step,
            ← exportNext_law, PMF.pure_map]

/-- Build each four-bit raw request by native writes and head movements.
The extra zero is the framing bit expected by the component. -/
def writeRequest : Code :=
  [.native (.write .output false), .native (.moveRight .output),
   .native (.write .output false), .native (.moveRight .output),
   .native (.write .output false), .native (.moveRight .output),
   .native (.write .output false), .native (.moveLeft .output),
   .native (.moveLeft .output), .native (.moveLeft .output)]

/-- Save the first response, construct another request, then branch on the
second response and write its complement before the genuine native halt. -/
def callerCode : Code :=
  writeRequest ++ [.call, .native (.branch .output 13 13 12),
    .native (.write .input true), .native (.moveRight .input)] ++
  writeRequest ++ [.call, .native (.branch .output 29 26 28),
    .native (.write .output true), .native (.jump 29),
    .native (.write .output false), .native .halt]

abbrev Physical := PacketResponseSource.Control (SimulatorQueryPacket.Control Unit) Unit (Configuration Unit)

def next (control : Physical) : Choice Physical :=
  match control with
  | .source saved frame => match frame.control with
      | .awaiting caller request => .pure (.processing caller frame.state frame.reverseTrace request
          (SimulatorQueryService.beginRound saved request))
      | _ => (timedChoice callerCode frame).map (.source saved)
  | .processing caller state trace request component => match SimulatorQueryPacket.ready component with
      | some (saved, packet) => .pure (.returning saved caller state ((request, packet) :: trace) (.loading packet {}))
      | none => (packetChoice component).map (.processing caller state trace request)
  | .returning saved caller state trace (.prepared loaded) =>
      .pure (.source saved ⟨state, .running {caller with outputTape := loaded.outputTape}, trace⟩)
  | .returning saved caller state trace loader => .pure (.returning saved caller state trace (loadNext loader))

theorem next_law (control : Physical) :
    (next control).law = SimulatorQueryRound.callerStep 1 1 oracle callerCode oracle control := by
  cases control with
  | source saved frame =>
      cases hc : frame.control <;>
        simp only [next, SimulatorQueryRound.callerStep, PacketResponseSource.step, hc]
      all_goals first | rw [Choice.map_law, timedChoice_law] | rfl
  | processing caller state trace request component =>
      cases hr : SimulatorQueryPacket.ready component with
      | none => simp only [next, SimulatorQueryRound.callerStep, PacketResponseSource.step, hr,
          Choice.map_law, packetChoice_law]
      | some pair => cases pair; simp only [next, SimulatorQueryRound.callerStep, PacketResponseSource.step, hr, Choice.law]
  | returning saved caller state trace loader =>
      cases loader <;>
        simp only [next, SimulatorQueryRound.callerStep, PacketResponseSource.step,
          Choice.law, ← loadNext_law, PMF.pure_map]

def stopped : Physical → Bool
  | .source _ frame => Reification.terminal frame.control
  | _ => false

/-- Enumerate all actual random branches, retaining first-halt durations. -/
def paths : Nat → Physical → List (Physical × Nat)
  | fuel, control => if stopped control then [(control, 0)] else match fuel with
    | 0 => [(control, 0)]
    | fuel + 1 => (next control).values.flatMap fun middle =>
        (paths fuel middle).map (fun result => (result.1, result.2 + 1))

theorem paths_support (fuel : Nat) (control : Physical) (result : Physical × Nat) :
    result ∈ (runToBoundary (SimulatorQueryRound.callerStep 1 1 oracle callerCode oracle)
      stopped fuel control).support ↔ result ∈ paths fuel control := by
  induction fuel generalizing control result with
  | zero => simp [runToBoundary, paths]
  | succ fuel ih =>
      by_cases h : stopped control = true
      · simp [runToBoundary, paths, h]
      · simp only [runToBoundary, paths, h, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_bind_iff, PMF.mem_support_map_iff, List.mem_flatMap, List.mem_map]
        rw [← next_law]
        simp only [Choice.support, ih]

def initial : Physical := .source
  ⟨(), .running {inputTape := Tape.ofBits (SimulatorLookup.tableBits ([] : PolygraphOracle.Table 1 1))}, []⟩
  (Configuration.initial () [])

/-- info: [(true, 224), (true, 224)] -/
#guard_msgs in
#eval (paths 500 initial).map fun result => (stopped result.1, result.2)

/-- Inspect the actual final tapes and public trace. The first response is
saved on the caller input tape; the final output is computed after the
second response. The server stores exactly the same sampled bit. -/
def correctResult (control : Physical) : Bool :=
  match control with
  | .source saved frame => match saved.control, frame.control, frame.reverseTrace with
      | .running server, .running caller, [(second, [b]), (first, [a])] =>
          caller.halted && (caller.pc == 29) && (a == b) &&
          (first == [false, false, false, false]) && (second == first) &&
          (caller.outputTape.bits == [!b]) &&
          (caller.inputTape.left.getD 0 none == if a then some true else none) &&
          (server.inputTape.bits == SimulatorLookup.tableBits
            [(CryptoOracle.RandomOracle.PolygraphExamples.Native.first, (fun _ : Fin 1 => b))])
      | _, _, _ => false
  | _ => false

theorem checked_paths : (paths 224 initial).all (fun result =>
    stopped result.1 && (result.2 == 224) && correctResult result.1) = true := by decide_cbv

theorem checked_before : (paths 223 initial).all (fun result => !stopped result.1) = true := by decide_cbv

theorem first_halt_exact (result : Physical × Nat)
    (hs : result ∈ (runToBoundary (SimulatorQueryRound.callerStep 1 1 oracle callerCode oracle)
      stopped 224 initial).support) :
    stopped result.1 = true ∧ result.2 = 224 ∧ correctResult result.1 = true := by
  have h := List.all_eq_true.mp checked_paths result ((paths_support 224 initial result).mp hs)
  simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using h

theorem one_before_unfinished (result : Physical × Nat)
    (hs : result ∈ (runToBoundary (SimulatorQueryRound.callerStep 1 1 oracle callerCode oracle)
      stopped 223 initial).support) : stopped result.1 = false := by
  have h := List.all_eq_true.mp checked_before result ((paths_support 223 initial result).mp hs)
  cases hStop : stopped result.1 <;> simp_all

theorem stopped_absorbing (control : Physical) (hs : stopped control = true) :
    SimulatorQueryRound.callerStep 1 1 oracle callerCode oracle control = PMF.pure control := by
  cases control with
  | source saved frame =>
      cases hc : frame.control <;>
        simp_all [stopped, Reification.terminal, SimulatorQueryRound.callerStep,
          PacketResponseSource.step, Reification.timedStep, PMF.pure_map]
  | processing => simp [stopped] at hs
  | returning => simp [stopped] at hs

/-- A whole native execution, including both request constructors, physical
services, response loading, response-dependent caller branches and final halt. -/
theorem whole_run (horizon : Nat) (enough : 224 ≤ horizon) :
    eval (SimulatorQueryRound.callerStep 1 1 oracle callerCode oracle) horizon initial =
      (runToBoundary (SimulatorQueryRound.callerStep 1 1 oracle callerCode oracle)
        stopped 224 initial).map Prod.fst := by
  apply (Block.stopped _ stopped 224 initial).final_law
  · intro result hs
    exact stopped_absorbing result.1 (first_halt_exact result hs).1
  · exact enough

theorem whole_run_correct (horizon : Nat) (enough : 224 ≤ horizon) (final : Physical)
    (hs : final ∈ (eval (SimulatorQueryRound.callerStep 1 1 oracle callerCode oracle) horizon initial).support) :
    stopped final = true ∧ correctResult final = true := by
  rw [whole_run horizon enough, PMF.mem_support_map_iff] at hs
  obtain ⟨result, hr, rfl⟩ := hs
  have h := first_halt_exact result hr
  exact ⟨h.1, h.2.2⟩

end Foundation.Hash.Native.NativeOracleExecution.Examples
