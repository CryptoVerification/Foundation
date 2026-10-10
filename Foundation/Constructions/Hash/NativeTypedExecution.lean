import Foundation.Constructions.Hash.NativeTypedCompression

/-! The specialized finite native code realizes exactly the typed hash used
by the security proof, including reindexed private compression state and the
whole compression transcript. The representation change is proved, not a
security or execution axiom. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

def typedHashFinish {n κ : Nat} (pc : Nat) (input : Tape)
    (out : Outcome (CompressionInput (Bits κ) (Bits n)) (Bits n) (Bits n)
      (CompressionTable (Bits κ) (Bits n))) : Configuration (IdealTable n κ) :=
  ⟨encodeCompressionTable out.state,
    .running { pc := pc, inputTape := input, outputTape := ResponseLoading.loaded out.result.toList, halted := true },
    (out.trace.map (fun entry => (compressionPacket entry.1, entry.2.toList))).reverse⟩

/-- Concrete native code, concrete ideal capability, and the original typed
prefix-free MD experiment have the same full joint distribution. -/
theorem typed_prefixFree_run {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ)) (input : List Bool)
    (table : CompressionTable (Bits κ) (Bits n)) :
    Reification.eval
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))
      (idealCompression n κ)
      (3 * n + (message.length + 1) * (7 * n + 5 * κ + 11) + 1)
      (Configuration.initial (encodeCompressionTable table) input) =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
      (typedHashFinish ((prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)).length - 1)
        (Tape.ofBits input)) := by
  rw [ideal_prefixFree_run]
  have blocks : Foundation.Hash.encode terminal.toList (message.map Bits.toList) =
      (Foundation.Hash.encode terminal message).map (fun block => (block.1, block.2.toList)) := by
    simp [Foundation.Hash.encode, List.map_map, Function.comp_def]
  change ((Foundation.Hash.iterate initial.toList _).run _ (encodeCompressionTable table)).map _ = _
  rw [blocks]
  have h := iterate_encoded_state_run Bits.toList
    (fun block : Bool × Bits κ => (block.1, block.2.toList)) encodeCompressionTable
    RandomOracle.oracle
    (Program.adaptOracle (fun pair : List Bool × (Bool × List Bool) => pair.1 ++ pair.2.1 :: pair.2.2)
      id (idealCompression n κ))
    (fun state previous payload => by
      change (idealCompression n κ (encodeCompressionTable state)
        (compressionPacket (previous, payload))).map id =
        (RandomOracle.oracle state (previous, payload)).map
          (fun answer => (encodeCompressionTable answer.1, answer.2.toList))
      rw [PMF.map_id]
      exact typed_compression_step state (previous, payload))
    initial (Foundation.Hash.encode terminal message) table
  rw [h]
  simp only [PMF.map_comp, Function.comp_def, Foundation.Hash.prefixFreeMD]
  congr 1
  funext out
  simp [hashFinish, typedHashFinish, encodeIterationOutcome, compressionPacket,
    List.map_map, Function.comp_def]

/-- Reading the written digest is a mathematical packet observation. This
lemma assigns no machine cost to extracting a host-language list. -/
theorem loaded_bits (bits : List Bool) : (ResponseLoading.loaded bits).bits = bits := by
  cases bits <;> simp [ResponseLoading.loaded, ResponseLoading.fromCells, Tape.bits,
    List.filterMap_map]

theorem typedHashFinish_packet {n κ : Nat} (pc : Nat) (input : Tape)
    (out : Outcome (CompressionInput (Bits κ) (Bits n)) (Bits n) (Bits n)
      (CompressionTable (Bits κ) (Bits n))) :
    Reification.packet (typedHashFinish pc input out).control = some out.result.toList := by
  simp [typedHashFinish, Reification.packet, Machine.Configuration.outputBits, loaded_bits]

/-- Native digest equality is exactly the original typed hash event. It is
an observation equality, not a CPU certificate for a separate verifier. -/
theorem typed_prefixFree_output {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ)) (input : List Bool)
    (table : CompressionTable (Bits κ) (Bits n)) (expected : Bits n) :
    eventProb (Reification.eval
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))
      (idealCompression n κ)
      (3 * n + (message.length + 1) * (7 * n + 5 * κ + 11) + 1)
      (Configuration.initial (encodeCompressionTable table) input))
      (fun finish => Reification.packet finish.control = some expected.toList) =
    eventProb ((Foundation.Hash.prefixFreeMD initial terminal message).run RandomOracle.oracle table)
      (fun out => out.result = expected) := by
  rw [typed_prefixFree_run, eventProb_map]
  simp only [typedHashFinish_packet, Option.some.injEq, Bits.toList, List.ofFn_injective.eq_iff]

/-- The native stopping condition holds for the same typed initial cache. -/
theorem typed_prefixFree_halts {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ)) (input : List Bool)
    (table : CompressionTable (Bits κ) (Bits n)) :
    Reification.HaltsWithin
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))
      (idealCompression n κ) (Configuration.initial (encodeCompressionTable table) input)
      (3 * n + (message.length + 1) * (7 * n + 5 * κ + 11) + 1) :=
  ideal_prefixFree_halts n κ initial terminal message input (encodeCompressionTable table)

/-- Every supported iterate branch makes exactly one query per block,
even when the stateful oracle answers adaptively or caches repeated requests. -/
theorem iterate_trace_length {Digest Payload State : Type}
    (oracle : Oracle (Digest × Payload) Digest State) (initial : Digest) (blocks : List Payload)
    (state : State) (out : Outcome (Digest × Payload) Digest Digest State)
    (support : out ∈ ((Foundation.Hash.iterate initial blocks).run oracle state).support) :
    out.trace.length = blocks.length := by
  induction blocks generalizing initial state out with
  | nil =>
      simp only [Foundation.Hash.iterate, Program.run, PMF.mem_support_pure_iff] at support
      subst out
      rfl
  | cons block rest ih =>
      rw [Foundation.Hash.iterate, Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, _, hTail⟩ := support
      rw [PMF.mem_support_map_iff] at hTail
      obtain ⟨tail, hTail, rfl⟩ := hTail
      simp only [List.length_cons, ih answer.2 answer.1 tail hTail]

/-- Count actual native capability calls from the complete supported trace.
Cached compression evaluations still count as calls. The terminal counts once. -/
theorem typed_prefixFree_queries {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ)) (input : List Bool)
    (table : CompressionTable (Bits κ) (Bits n))
    (finish : Configuration (IdealTable n κ))
    (support : finish ∈ (Reification.eval
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))
      (idealCompression n κ)
      (3 * n + (message.length + 1) * (7 * n + 5 * κ + 11) + 1)
      (Configuration.initial (encodeCompressionTable table) input)).support) :
    finish.reverseTrace.length = message.length + 1 := by
  rw [typed_prefixFree_run, PMF.mem_support_map_iff] at support
  obtain ⟨out, hOut, rfl⟩ := support
  have h := iterate_trace_length RandomOracle.oracle initial (Foundation.Hash.encode terminal message)
    table out hOut
  simpa [typedHashFinish] using h

/-- The full encoded-space theorem applies at every intermediate time with
the actual encoded typed table, not a newly independent random cache. -/
theorem typed_prefixFree_encoded_peak {n κ : Nat}
    (initial : Bits n) (terminal : Bits κ) (message : List (Bits κ)) (input : List Bool)
    (table : CompressionTable (Bits κ) (Bits n)) (elapsed : Nat)
    (within : elapsed ≤ 3 * n + (message.length + 1) * (7 * n + 5 * κ + 11) + 1)
    (target : Configuration (IdealTable n κ))
    (support : target ∈ (Reification.eval
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))
      (idealCompression n κ) elapsed (Configuration.initial (encodeCompressionTable table) input)).support) :
    (EncodedStorage.codeEncoding.encode
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList))).length +
      ((ConfigurationEncoding.frame (tableEncoding n κ)).encode target).length ≤
    EncodedStorage.bound
      (prefixFreeCode initial.toList terminal.toList (message.map Bits.toList)) 0
      (ControllerExtent.frameExtent (tableSize n κ) (Configuration.initial (encodeCompressionTable table) input))
      (3 * n + (message.length + 1) * (7 * n + 5 * κ + 11) + 1)
      (entryIncrement n κ) n :=
  ideal_prefixFree_encoded_peak n κ initial terminal message input (encodeCompressionTable table)
    elapsed within target support

end Foundation.Hash.Native
