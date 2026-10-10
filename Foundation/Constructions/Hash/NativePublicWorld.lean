import Foundation.Constructions.Hash.NativeRuntimeRawService
import Foundation.Constructions.Hash.NativePublicCompression
import Foundation.Crypto.Semantics.Oracle.StateMap

/-! One physical two-window dispatcher. A leading false selects native
hashing and true selects native public compression. Both starts retain the
same saved compression cache. The header is consumed by the already charged
caller-to-component ownership transition, not by a host request decoder. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev NativeWorldComponent (n κ : Nat) :=
  NativePacketLaunch.Control (IdealTable n κ) ⊕ NativePacketLaunch.Control (IdealTable n κ)

noncomputable def nativeWorldStep {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) : NativeWorldComponent n κ → PMF (NativeWorldComponent n κ)
  | .inl component =>
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList)
        (idealCompression n κ) false prior component).map Sum.inl
  | .inr component =>
      (NativePacketLaunch.step NativeCompressionCall.code (idealCompression n κ) false prior component).map Sum.inr

def nativeWorldBegin {n κ : Nat} (saved : Configuration (IdealTable n κ))
    (request : List Bool) : NativeWorldComponent n κ :=
  match request with
  | true :: rest => .inr (runtimeRawBegin saved rest)
  | false :: rest => .inl (runtimeRawBegin saved rest)
  | [] => .inl (runtimeRawBegin saved [])

def nativeWorldReady {n κ : Nat} : NativeWorldComponent n κ →
    Option (Configuration (IdealTable n κ) × List Bool)
  | .inl component => runtimeRawReady component
  | .inr component => runtimeRawReady component

def nativeWorldPacket {n κ : Nat} : WorldInput (Bits κ) (Bits n) → List Bool
  | .inl message => false :: runtimeInputBits (message.map Bits.toList)
  | .inr input => true :: compressionPacket input

theorem nativeWorld_ready_absorbing {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (component : NativeWorldComponent n κ)
    (ready : (nativeWorldReady component).isSome = true) :
    nativeWorldStep initial terminal prior component = PMF.pure component := by
  cases component with
  | inl component =>
      simp only [nativeWorldStep]
      rw [runtimeRawReady_absorbing _ _ prior component ready, PMF.pure_map]
  | inr component =>
      simp only [nativeWorldStep]
      rw [runtimeRawReady_absorbing _ _ prior component ready, PMF.pure_map]

/-- The dispatcher preserves every actual component transition. -/
theorem nativeWorld_hash_eval {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (fuel : Nat)
    (component : NativePacketLaunch.Control (IdealTable n κ)) :
    TimedExecution.eval (nativeWorldStep initial terminal prior) fuel (.inl component) =
    (TimedExecution.eval
      (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList)
        (idealCompression n κ) false prior) fuel component).map Sum.inl := by
  symm
  exact eval_map _ _ Sum.inl (fun _ => rfl) fuel component

theorem nativeWorld_compression_eval {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (fuel : Nat)
    (component : NativePacketLaunch.Control (IdealTable n κ)) :
    TimedExecution.eval (nativeWorldStep initial terminal prior) fuel (.inr component) =
    (TimedExecution.eval (NativePacketLaunch.step NativeCompressionCall.code
      (idealCompression n κ) false prior) fuel component).map Sum.inr := by
  symm
  exact eval_map _ _ Sum.inr (fun _ => rfl) fuel component

/-- Entering either window reads the same retained cache; a public call
never initializes an independent compression function table. -/
theorem nativeWorldBegin_hash {n κ : Nat} (saved : Configuration (IdealTable n κ))
    (message : List (Bits κ)) :
    nativeWorldBegin saved (nativeWorldPacket (n := n) (.inl message)) =
      .inl (.preparing saved.state (.loading (runtimeInputBits (message.map Bits.toList)) {})) := rfl

theorem nativeWorldBegin_compression {n κ : Nat} (saved : Configuration (IdealTable n κ))
    (input : CompressionInput (Bits κ) (Bits n)) :
    nativeWorldBegin saved (nativeWorldPacket (.inr input)) =
      .inr (.preparing saved.state (.loading (compressionPacket input) {})) := rfl

/-- The existing continuing caller with this concrete two-window dispatcher. -/
noncomputable def nativeWorldCallerStep {n κ : Nat} {State : Type*}
    (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    (callerCode : Code) (callerOracle : BitOracle State) :=
  PacketResponseSource.step (nativeWorldStep initial terminal prior)
    nativeWorldBegin nativeWorldReady callerCode callerOracle

/-- Window selection is included in the actual source ownership transition.
Only the leading Boolean is inspected; the rest remains a raw buffer. -/
theorem nativeWorldCaller_dispatch {n κ : Nat} {State : Type*}
    (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    (callerCode : Code) (callerOracle : BitOracle State)
    (saved : Configuration (IdealTable n κ)) (caller : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool)) (request : List Bool) :
    nativeWorldCallerStep initial terminal prior callerCode callerOracle
      (.source saved ⟨state, .awaiting caller request, trace⟩) =
    PMF.pure (.processing caller state trace request (nativeWorldBegin saved request)) := rfl

/-- Budget for one physical block; the public window tag is consumed by
begin's caller ownership transition, outside this component budget. -/
def nativeWorldBudget {n κ : Nat} : WorldInput (Bits κ) (Bits n) → Nat
  | .inl message => runtimeRawExportSteps n κ message.length
  | .inr _ => NativeCompressionCall.rawSteps (n + κ + 1) n

/-- Proof-side observation of an already physically exported packet.
The fallback is irrelevant on the valid typed entry conditions proved below. -/
def nativeWorldRead {n κ : Nat} (fallback : IdealTable n κ)
    (component : NativeWorldComponent n κ) : IdealTable n κ × List Bool :=
  let raw := match component with | .inl raw => raw | .inr raw => raw
  match rawReturnedObservation raw with
  | some (packet, state, _) => (state, packet.getD [])
  | none => (fallback, [])

/-- Block semantics: execute the actual physical component from its raw
buffer and retain its actual updated cache. Request selection and this
observation are mathematical, not a compiled whole adversary or decoder. -/
noncomputable def nativeWorldOracle {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) :
    Oracle (WorldInput (Bits κ) (Bits n)) (List Bool) (IdealTable n κ) :=
  fun state request => (TimedExecution.eval (nativeWorldStep initial terminal prior)
    (nativeWorldBudget request)
    (nativeWorldBegin ⟨state, .finished false, prior⟩ (nativeWorldPacket request))).map (nativeWorldRead state)

/-- Both physical windows realize the original shared-table real world.
No new lazy table is sampled when switching between hash and compression. -/
theorem nativeWorldOracle_step {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool)) (table : CompressionTable (Bits κ) (Bits n))
    (request : WorldInput (Bits κ) (Bits n)) :
    nativeWorldOracle initial terminal prior (encodeCompressionTable table) request =
    (realWorld initial terminal table request).map (fun answer =>
      (encodeCompressionTable answer.1, answer.2.toList)) := by
  cases request with
  | inl message =>
      simp only [nativeWorldOracle, nativeWorldBudget, nativeWorldBegin_hash,
        nativeWorld_hash_eval, PMF.map_comp, Function.comp_def]
      have h := congrArg (fun distribution => distribution.map
        (fun observed : Option (Option (List Bool) × IdealTable n κ × List (List Bool × List Bool)) =>
          match observed with
          | some (packet, state, _) => (state, packet.getD [])
          | none => (encodeCompressionTable table, [])))
        (raw_linked_export_packet initial terminal message table prior)
      simp only [PMF.map_comp, Function.comp_def] at h
      simpa only [nativeWorldRead, realWorld, PMF.map_comp, Function.comp_def, Option.getD_some] using h
  | inr input =>
      simp only [nativeWorldOracle, nativeWorldBudget, nativeWorldBegin_compression,
        nativeWorld_compression_eval, native_public_compression_run, PMF.map_comp, Function.comp_def]
      rfl

/-- Complete adaptive block semantics, including local coins, public
request/response transcript and shared final table. This does not supply a
finite caller compiler or a machine-time bound for the host continuations. -/
theorem nativeWorld_adaptive_run {n κ : Nat} {Result : Type*}
    (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    (attack : Program (WorldInput (Bits κ) (Bits n)) (List Bool) Result)
    (table : CompressionTable (Bits κ) (Bits n)) :
    attack.run (nativeWorldOracle initial terminal prior) (encodeCompressionTable table) =
    (attack.run (Program.adaptOracle id Bits.toList (realWorld initial terminal)) table).map
      (Program.mapState encodeCompressionTable) := by
  symm
  apply Program.run_state_map encodeCompressionTable
  intro state request
  rw [nativeWorldOracle_step, Program.adaptOracle, PMF.map_comp]
  rfl

end Foundation.Hash.Native
