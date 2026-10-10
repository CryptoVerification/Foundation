import Foundation.Constructions.Hash.NativeAdaptivePublicExecution
import Foundation.Crypto.Semantics.Oracle.PacketResponseHalt
import Foundation.Crypto.Semantics.ProcedureBoundaryReachability
import Foundation.Crypto.Semantics.ProcedurePhysical

/-! Genuine whole-caller completion for the concrete adaptive two-window
program. Actual private frames, public transcripts, and response cells remain
in the final distribution. The halt itself costs one native transition. -/
namespace Foundation.Hash.Native.AdaptivePublicCaller
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {n κ : Nat} (marker : Bool) (payload : Bits κ)

theorem final_halt_lookup : (code n marker payload)[2 + preparationCost n κ]? = some (.native .halt) := by
  have length : ([Instruction.call] ++ StraightLine.code (actions n marker payload)).length = preparationCost n κ + 1 := by
    simp [StraightLine.code, Nat.add_comm]
  unfold code
  rw [List.getElem?_append_right (by rw [length]; omega)]
  rw [length, show 2 + preparationCost n κ - (preparationCost n κ + 1) = 1 by omega]
  rfl

variable {State : Type*} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (input : Tape) (message : List (Bits κ))
    (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    (saved : Configuration (IdealTable n κ)) (table : CompressionTable (Bits κ) (Bits n))
    (cache : saved.state = encodeCompressionTable table)

theorem twoWorld_ready (output : IdealTable n κ × Configuration State)
    (hs : output ∈ (twoWorld marker payload state trace input message initial terminal table).support) :
    PacketResponseHalt.Ready (code n marker payload) output.2 := by
  rw [twoWorld, PMF.mem_support_bind_iff] at hs
  obtain ⟨first, _, hs⟩ := hs
  rw [afterFirst, PMF.mem_support_map_iff] at hs
  obtain ⟨second, _, he⟩ := hs
  subst output
  refine ⟨{ (secondMachine input first.2 marker payload).advance with outputTape := ResponseLoading.loaded second.2.toList }, rfl, rfl, ?_⟩
  change (code n marker payload)[(1 + preparationCost n κ) + 1]? = some (.native .halt)
  rw [show (1 + preparationCost n κ) + 1 = 2 + preparationCost n κ by omega]
  exact final_halt_lookup marker payload

theorem bothCalls_ready (output : Configuration (IdealTable n κ) × Configuration State)
    (hs : output ∈ ((bothCalls marker payload oracle state trace input message
      initial terminal prior saved table cache).semantics ()).support) :
    PacketResponseHalt.Ready (code n marker payload) output.2 := by
  have hm : (output.1.state, output.2) ∈
      (((bothCalls marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).map
        (fun result => (result.1.state, result.2))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨output, hs, rfl⟩
  rw [bothCalls_packet] at hm
  exact twoWorld_ready marker payload state trace input message initial terminal table _ hm

noncomputable def readyCalls :=
  (bothCalls marker payload oracle state trace input message initial terminal prior saved table cache).certify
    (fun output => PacketResponseHalt.Ready (code n marker payload) output.2)
    (fun _ output hs => bothCalls_ready marker payload oracle state trace input message initial terminal prior saved table cache output hs)

noncomputable def whole :=
  ((readyCalls marker payload oracle state trace input message initial terminal prior saved table cache).seq
    (PacketResponseHalt.procedure (nativeWorldStep initial terminal prior) nativeWorldBegin nativeWorldReady
      (code n marker payload) oracle)
    (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)).observe Prod.snd
      (fun _ output => PacketResponseSource.Control.source output.1 output.2) (fun _ _ _ => rfl)

theorem whole_semantics :
    (whole marker payload oracle state trace input message initial terminal prior saved table cache).semantics () =
      ((readyCalls marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).map
        (fun selected => (selected.val.1, PacketResponseHalt.halted selected.val.2)) := by
  simp only [whole, Procedure.observe, Procedure.seq, PacketResponseHalt.procedure,
    TimedExecution.Procedure.ofFixed, PMF.pure_map, PMF.map_bind]
  rfl

theorem whole_budget :
    (whole marker payload oracle state trace input message initial terminal prior saved table cache).budget () =
      (2 * (nativeWorldPacket (.inl message : WorldInput (Bits κ) (Bits n))).length + 3) +
        (1 + (nativeWorldBudget (.inl message : WorldInput (Bits κ) (Bits n)) + (3 * n + 4))) + secondCap n κ + 1 := rfl

/-- A concrete transition bound for the full two-query code, including
request export, both native services, response loading and genuine halt. -/
theorem whole_budget_polynomial :
    (whole marker payload oracle state trace input message initial terminal prior saved table cache).budget () =
      message.length * (7 * n + 27 * κ + 33) + 32 * n + 15 * κ + 103 := by
  rw [whole_budget]
  simp only [nativeWorldPacket, List.length_cons, typed_runtime_input_length, nativeWorldBudget,
    runtimeRawExportSteps, runtimePreparationSteps, runtimeLinkedHashSteps, runtimeTransferSteps,
    runtimeHashSteps, runtimeLoopSteps, secondCap, preparationCost, NativeCompressionCall.rawSteps]
  ring

theorem whole_operational :
    Procedure.Operational (whole marker payload oracle state trace input message initial terminal prior saved table cache) := by
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · apply Procedure.operational_certify
    exact bothCalls_operational _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact PacketResponseHalt.procedure_operational _ _ _ _ _

theorem whole_packet :
    ((whole marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).map
      (fun output => (output.1.state, output.2)) =
      (twoWorld marker payload state trace input message initial terminal table).map
        (fun output => (output.1, PacketResponseHalt.halted output.2)) := by
  rw [whole_semantics, PMF.map_comp]
  have erase := Procedure.certify_semantics
    (bothCalls marker payload oracle state trace input message initial terminal prior saved table cache)
    (fun output => PacketResponseHalt.Ready (code n marker payload) output.2)
    (fun _ output hs => bothCalls_ready marker payload oracle state trace input message initial terminal prior saved table cache output hs) ()
  have mapped := congrArg (fun distribution => distribution.map (fun output => (output.1, PacketResponseHalt.halted output.2)))
    (bothCalls_packet marker payload oracle state trace input message initial terminal prior saved table cache)
  rw [← erase, PMF.map_comp, PMF.map_comp] at mapped
  exact mapped

theorem whole_terminal (output : Configuration (IdealTable n κ) × Configuration State)
    (hs : output ∈ ((whole marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).support) :
    PacketResponseSource.terminal
      (PacketResponseSource.Control.source (Component := NativeWorldComponent n κ) output.1 output.2) = true := by
  rw [whole_semantics, PMF.mem_support_map_iff] at hs
  obtain ⟨selected, _, he⟩ := hs
  subst output
  exact PacketResponseHalt.halted_terminal _ selected.val.2 selected.property

/-- The unchanged finite code actually terminates. This is a distribution
of complete physical returns, not merely two successful component replies. -/
theorem whole_run (horizon : Nat)
    (enough : (whole marker payload oracle state trace input message initial terminal prior saved table cache).budget () ≤ horizon) :
    TimedExecution.eval (nativeWorldCallerStep initial terminal prior (code n marker payload) oracle) horizon
      (.source saved ⟨state, .running (firstMachine (n := n) input message), trace⟩) =
      ((whole marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).map
        (fun output => PacketResponseSource.Control.source output.1 output.2) := by
  apply (whole marker payload oracle state trace input message initial terminal prior saved table cache).final_run ()
  · intro output hs
    apply PacketResponseSource.terminal_absorbing
    exact whole_terminal marker payload oracle state trace input message initial terminal prior saved table cache output hs
  · exact enough

/-- Actual first caller-termination costs and full physical endpoints, obtained
from the existing boundary constructor. Private native halts are not boundaries. -/
noncomputable def firstHalt :=
  (whole marker payload oracle state trace input message initial terminal prior saved table cache).physical.liftBoundary
    PacketResponseSource.terminal
    (by
      intro _ output hs
      change output ∈ (((whole marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).map _).support at hs
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨original, ho, he⟩ := hs
      subst output
      exact whole_terminal marker payload oracle state trace input message initial terminal prior saved table cache original ho)
    (PacketResponseSource.terminal_absorbing (nativeWorldStep initial terminal prior)
      nativeWorldBegin nativeWorldReady (code n marker payload) oracle)
    (fun _ output => output) (fun _ _ => rfl)
    (nativeWorldCallerStep initial terminal prior (code n marker payload) oracle)
    PacketResponseSource.terminal id (fun _ => rfl) (fun _ _ => (PMF.map_id _).symm)

theorem firstHalt_operational :
    Procedure.Operational (firstHalt marker payload oracle state trace input message initial terminal prior saved table cache) := by
  unfold firstHalt
  apply Procedure.operational_liftBoundary

/-- The reported costs are precisely the actual first caller-halt joint law;
the bound is not used as a deterministic elapsed time. -/
theorem firstHalt_costed :
    (firstHalt marker payload oracle state trace input message initial terminal prior saved table cache).costed () =
    runToBoundary (nativeWorldCallerStep initial terminal prior (code n marker payload) oracle)
      PacketResponseSource.terminal
      (message.length * (7 * n + 27 * κ + 33) + 32 * n + 15 * κ + 103)
      (.source saved ⟨state, .running (firstMachine (n := n) input message), trace⟩) := by
  have budget := whole_budget_polynomial marker payload oracle state trace input message initial terminal prior saved table cache
  change (runToBoundary _ _ ((whole marker payload oracle state trace input message initial terminal prior saved table cache).budget ()) _).map id = _
  rw [budget, PMF.map_id]
  rfl

theorem firstHalt_semantics :
    (firstHalt marker payload oracle state trace input message initial terminal prior saved table cache).semantics () =
    ((whole marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).map
      (fun output => PacketResponseSource.Control.source output.1 output.2) := rfl

end Foundation.Hash.Native.AdaptivePublicCaller
