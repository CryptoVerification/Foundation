import Foundation.Constructions.Hash.NativePublicWorldRound
import Foundation.Crypto.Semantics.Oracle.SourcePrefixStraightLine
import Foundation.Crypto.Semantics.Oracle.PacketResponseTerminal

/-! A concrete fixed caller first hashes its input and then queries public
compression with the returned digest. The second packet is built by ordinary
single-cell tape instructions, rather than a host continuation. -/
namespace Foundation.Hash.Native.AdaptivePublicCaller
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability TimedExecution
open Foundation.Symmetric StraightLine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Append a marked payload to the actual response, rewind, and physically
prepend the public compression window tag. -/
def actions (n : Nat) {κ : Nat} (marker : Bool) (payload : Bits κ) : List Action :=
  prepareActions n (marker :: payload.toList) ++ [.left .output, .write .output (some true)]

def preparationCost (n κ : Nat) : Nat := 2 * n + 3 * (κ + 1) + 2

def code (n : Nat) {κ : Nat} (marker : Bool) (payload : Bits κ) : Code :=
  [.call] ++ StraightLine.code (actions n marker payload) ++ [.call, .native .halt]

@[simp] theorem actions_length (n : Nat) {κ : Nat} (marker : Bool) (payload : Bits κ) :
    (actions n marker payload).length = preparationCost n κ := by
  simp [actions, preparationCost]

@[simp] theorem code_length (n : Nat) {κ : Nat} (marker : Bool) (payload : Bits κ) :
    (code n marker payload).length = preparationCost n κ + 3 := by
  simp [code, StraightLine.code]

/-- Two physical instructions prefix the window bit without resetting the
tape. The represented trailing blank remains present. -/
theorem prefix_execute (pc : Nat) (input : Tape) (bits : List Bool) :
    execute [.left .output, .write .output (some true)]
      { pc := pc, inputTape := input, outputTape := ResponseLoading.loaded bits } =
    ({ pc := pc + 2, inputTape := input, outputTape := ResponseLoading.loaded (true :: bits) } : Machine.Configuration) := by
  cases bits <;>
    simp [execute, StraightLine.apply, Machine.Configuration.updateTape, Machine.Configuration.advance,
      Tape.moveLeft, Tape.write, ResponseLoading.loaded, ResponseLoading.fromCells, Nat.add_assoc]

theorem actions_execute {n κ : Nat} (pc : Nat) (input : Tape) (digest : Bits n)
    (marker : Bool) (payload : Bits κ) :
    execute (actions n marker payload)
      { pc := pc, inputTape := input, outputTape := ResponseLoading.loaded digest.toList } =
    ({ pc := pc + preparationCost n κ, inputTape := input,
        outputTape := ResponseLoading.loaded (nativeWorldPacket (.inr (digest, (marker, payload)))) } : Machine.Configuration) := by
  unfold actions
  rw [execute_append]
  have prep := prepare_execute pc input digest.toList (marker :: payload.toList)
  simp only [Bits.length_toList] at prep
  rw [prep, prefix_execute]
  simp only [Bits.length_toList, List.length_cons, preparationCost, nativeWorldPacket, compressionPacket]
  congr 1

/-- Exact physical machine at the second call. Its request depends on the
preceding random response; its finite code does not. -/
def secondMachine {n κ : Nat} (input : Tape) (digest : Bits n) (marker : Bool) (payload : Bits κ) : Machine.Configuration :=
  { pc := 1 + preparationCost n κ, inputTape := input,
    outputTape := ResponseLoading.loaded (nativeWorldPacket (.inr (digest, (marker, payload)))) }

variable {n κ : Nat} (marker : Bool) (payload : Bits κ) {State : Type*} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (input : Tape) (digest : Bits n)

/-- The public compression request is constructed and captured by the
actual caller, retaining input cells, local state, and preceding public trace. -/
theorem second_capture_run :
    TimedExecution.eval (SourcePrefix.step (code n marker payload) oracle)
      (preparationCost n κ + (2 * (nativeWorldPacket (.inr (digest, (marker, payload)))).length + 3))
      (⟨state, .running { pc := 1, inputTape := input, outputTape := ResponseLoading.loaded digest.toList }, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .awaiting (secondMachine input digest marker payload).advance
      (nativeWorldPacket (.inr (digest, (marker, payload)))), trace⟩ := by
  rw [TimedExecution.eval_add]
  have prep := SourcePrefix.straight_run oracle state trace [.call] [.call, .native .halt]
    (actions n marker payload)
    { pc := 1, inputTape := input, outputTape := ResponseLoading.loaded digest.toList } rfl rfl
  rw [actions_length, actions_execute] at prep
  change TimedExecution.eval (SourcePrefix.step (code n marker payload) oracle) _ _ =
    PMF.pure ⟨state, .running (secondMachine input digest marker payload), trace⟩ at prep
  rw [prep, PMF.pure_bind]
  apply SourcePrefix.capture_run (code n marker payload) oracle (secondMachine input digest marker payload)
    state trace (nativeWorldPacket (.inr (digest, (marker, payload)))) [] [] rfl
  · change (code n marker payload)[1 + preparationCost n κ]? = some .call
    simp only [code]
    rw [List.getElem?_append_right (by simp [StraightLine.code])]
    simp [StraightLine.code, Nat.add_comm]
  · rfl

noncomputable def secondSelection : SourcePrefix.Input (code n marker payload) oracle where
  start := ⟨state, .running { pc := 1, inputTape := input, outputTape := ResponseLoading.loaded digest.toList }, trace⟩
  budget := preparationCost n κ + (2 * (nativeWorldPacket (.inr (digest, (marker, payload)))).length + 3)
  complete := by
    intro frame hs
    rw [second_capture_run marker payload oracle state trace input digest, PMF.mem_support_pure_iff] at hs
    subst frame
    rfl

theorem secondSelection_valid :
    ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step (code n marker payload) oracle)
      (secondSelection marker payload oracle state trace input digest).budget
      (secondSelection marker payload oracle state trace input digest).start).support,
    NativeWorldAdmissible (n := n) (κ := κ)
      (nativeWorldBudget (.inr (digest, (marker, payload))) + (3 * n + 4)) frame := by
  intro frame hs
  dsimp only [secondSelection] at hs
  rw [second_capture_run, PMF.mem_support_pure_iff] at hs
  subst frame
  intro caller raw h
  cases h
  exact ⟨.inr (digest, (marker, payload)), rfl, Nat.le_refl _⟩

variable (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    (saved : Configuration (IdealTable n κ)) (table : CompressionTable (Bits κ) (Bits n))
    (cache : saved.state = encodeCompressionTable table)

noncomputable def secondRound :=
  nativeWorldSourceRound initial terminal prior (code n marker payload) oracle saved table cache
    (secondSelection marker payload oracle state trace input digest)
    (nativeWorldBudget (.inr (digest, (marker, payload))) + (3 * n + 4))
    (secondSelection_valid marker payload oracle state trace input digest)

theorem secondRound_semantics :
    (secondRound marker payload oracle state trace input digest initial terminal prior saved table cache).semantics () =
    (nativeWorldService initial terminal prior (code n marker payload) oracle
      (secondMachine input digest marker payload).advance state trace table (.inr (digest, (marker, payload)))).semantics () := by
  apply nativeWorldSourceRound_semantics_of_pure
  exact second_capture_run marker payload oracle state trace input digest

theorem secondRound_operational :
    Procedure.Operational (secondRound marker payload oracle state trace input digest initial terminal prior saved table cache) :=
  nativeWorldSourceRound_operational _ _ _ _ _ _ _ _ _ _ _

/-- Simultaneous distribution of the retained shared table and complete
resumed caller, including the adaptively constructed second public request. -/
theorem secondRound_packet :
    ((secondRound marker payload oracle state trace input digest initial terminal prior saved table cache).semantics ()).map
      (fun output => (output.1.state, output.2)) =
    (realWorld initial terminal table (.inr (digest, (marker, payload)))).map (fun answer =>
      (encodeCompressionTable answer.1, NativeCallback.resumed (secondMachine input digest marker payload).advance
        state trace (nativeWorldPacket (.inr (digest, (marker, payload)))) answer.2.toList)) := by
  rw [secondRound_semantics, nativeWorldService_packet]

end Foundation.Hash.Native.AdaptivePublicCaller
