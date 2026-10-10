import Foundation.Constructions.Hash.NativeAdaptivePublicCaller

/-! Compose the two actual calls in one finite caller. Certificates retain
the complete physical cache; their typed views are mathematical observations,
not instructions that construct a request or reset a machine. -/
namespace Foundation.Hash.Native.AdaptivePublicCaller
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The native table representation preserves every entry, including its
order. It is not a quotient that forgets prior oracle answers. -/
theorem table_encoding_injective {n κ : Nat} : Function.Injective (@encodeCompressionTable n κ) := by
  have hf : Function.Injective (fun entry : CompressionInput (Bits κ) (Bits n) × Bits n =>
      (compressionKey entry.1, entry.2)) := by
    intro left right equal
    have keys : left.1 = right.1 := compressionKey_injective n κ (congrArg Prod.fst equal)
    have values : left.2 = right.2 := congrArg (fun entry : Bits (n + κ + 1) × Bits n => entry.2) equal
    exact Prod.ext keys values
  exact List.map_injective_iff.mpr hf

variable {n κ : Nat} (marker : Bool) (payload : Bits κ) {State : Type*} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (input : Tape) (message : List (Bits κ))
    (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    (saved : Configuration (IdealTable n κ)) (table : CompressionTable (Bits κ) (Bits n))
    (cache : saved.state = encodeCompressionTable table)

def firstMachine : Machine.Configuration :=
  { inputTape := input, outputTape := ResponseLoading.loaded (nativeWorldPacket (.inl message : WorldInput (Bits κ) (Bits n))) }

def replyCaller (answer : CompressionTable (Bits κ) (Bits n) × Bits n) : Configuration State :=
  ⟨state, .running { pc := 1, inputTape := input, outputTape := ResponseLoading.loaded answer.2.toList },
    (nativeWorldPacket (.inl message : WorldInput (Bits κ) (Bits n)), answer.2.toList) :: trace⟩

def replyObservation (answer : CompressionTable (Bits κ) (Bits n) × Bits n) :=
  (encodeCompressionTable answer.1, replyCaller state trace input message answer)

theorem replyObservation_injective : Function.Injective (replyObservation state trace input message (n := n)) := by
  intro left right equal
  have tables := table_encoding_injective (congrArg Prod.fst equal)
  have traces := congrArg (fun observed => observed.2.reverseTrace) equal
  change (_, left.2.toList) :: trace = (_, right.2.toList) :: trace at traces
  have digests := congrArg Prod.snd (List.cons.inj traces).1
  exact Prod.ext tables (List.ofFn_injective digests)

noncomputable def firstRound :=
  nativeWorldCaptureRound initial terminal prior (code n marker payload) oracle
    (firstMachine (n := n) input message) state trace (.inl message) [] [] rfl rfl rfl saved table cache

theorem firstRound_packet :
    ((firstRound marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).map
      (fun output => (output.1.state, output.2)) =
      (realWorld initial terminal table (.inl message)).map (replyObservation state trace input message) := by
  rw [firstRound, nativeWorldCaptureRound_packet]
  rfl

def FirstLayout (output : Configuration (IdealTable n κ) × Configuration State) : Prop :=
  ∃ answer : CompressionTable (Bits κ) (Bits n) × Bits n,
    output.1.state = encodeCompressionTable answer.1 ∧ output.2 = replyCaller state trace input message answer

theorem firstRound_layout (output : Configuration (IdealTable n κ) × Configuration State)
    (hs : output ∈ ((firstRound marker payload oracle state trace input message
      initial terminal prior saved table cache).semantics ()).support) :
    FirstLayout state trace input message output := by
  have hm : (output.1.state, output.2) ∈
      (((firstRound marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).map
        (fun result => (result.1.state, result.2))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨output, hs, rfl⟩
  rw [firstRound_packet, PMF.mem_support_map_iff] at hm
  obtain ⟨answer, _, he⟩ := hm
  exact ⟨answer, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

noncomputable def firstCertified :=
  (firstRound marker payload oracle state trace input message initial terminal prior saved table cache).certify
    (FirstLayout state trace input message)
    (fun _ output hs => firstRound_layout marker payload oracle state trace input message initial terminal prior saved table cache output hs)

noncomputable def selectedAnswer
    (selected : {output : Configuration (IdealTable n κ) × Configuration State // FirstLayout state trace input message output}) :
    CompressionTable (Bits κ) (Bits n) × Bits n := selected.property.choose

/-- The proof-level typed view of the physical first reply has exactly the
original real-world distribution. Certificate choice does not resample it. -/
theorem firstCertified_answers :
    ((firstCertified marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).map
      (selectedAnswer state trace input message) = realWorld initial terminal table (.inl message) := by
  let D := (firstCertified marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()
  have erase := Procedure.certify_semantics
    (firstRound marker payload oracle state trace input message initial terminal prior saved table cache)
    (FirstLayout state trace input message)
    (fun _ output hs => firstRound_layout marker payload oracle state trace input message initial terminal prior saved table cache output hs) ()
  have image : D.map (fun selected => replyObservation state trace input message (selectedAnswer state trace input message selected)) =
      (realWorld initial terminal table (.inl message)).map (replyObservation state trace input message) := by
    rw [← firstRound_packet marker payload oracle state trace input message initial terminal prior saved table cache, ← erase, PMF.map_comp]
    congr 1
    funext selected
    exact Prod.ext selected.property.choose_spec.1.symm selected.property.choose_spec.2.symm
  have inverse := congrArg (fun distribution => distribution.map (Function.invFun (replyObservation state trace input message))) image
  have unencode (answer : CompressionTable (Bits κ) (Bits n) × Bits n) :
      Function.invFun (replyObservation state trace input message) (replyObservation state trace input message answer) = answer :=
    Function.leftInverse_invFun (replyObservation_injective state trace input message) answer
  simpa only [PMF.map_comp, Function.comp_def, unencode,
    show (fun x : CompressionTable (Bits κ) (Bits n) × Bits n => x) = id by rfl, PMF.map_id] using inverse

/-- Uniform second-round cap includes ordinary packet construction, capture,
window transfer, native compression, and physical response loading. -/
def secondCap (n κ : Nat) : Nat :=
  preparationCost n κ + (2 * (n + κ + 2) + 3) +
    (1 + (NativeCompressionCall.rawSteps (n + κ + 1) n + (3 * n + 4)))

theorem secondRound_budget (digest : Bits n) :
    (secondRound marker payload oracle state trace input digest initial terminal prior saved table cache).budget () = secondCap n κ := by
  rw [secondRound, nativeWorldSourceRound_budget]
  simp [secondSelection, secondCap, nativeWorldPacket, compressionPacket, nativeWorldBudget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

noncomputable def secondFamily
    (selected : {output : Configuration (IdealTable n κ) × Configuration State // FirstLayout state trace input message output}) :=
  let answer := selectedAnswer state trace input message selected
  secondRound marker payload oracle state
    ((nativeWorldPacket (.inl message : WorldInput (Bits κ) (Bits n)), answer.2.toList) :: trace)
    input answer.2 initial terminal prior selected.val.1 answer.1 selected.property.choose_spec.1

noncomputable def bothCalls :=
  ((firstCertified marker payload oracle state trace input message initial terminal prior saved table cache).seq
    (Procedure.dispatch (secondFamily marker payload oracle state trace input message initial terminal prior))
    (fun _ selected _ => by
      change PacketResponseSource.Control.source selected.val.1
        (replyCaller state trace input message (selectedAnswer state trace input message selected)) =
        PacketResponseSource.Control.source selected.val.1 selected.val.2
      rw [selected.property.choose_spec.2]
      rfl)
    (fun _ => secondCap n κ)
    (fun _ selected _ => le_of_eq (secondRound_budget marker payload oracle state _ input
      initial terminal prior selected.val.1 _ selected.property.choose_spec.1 _))).observe
      Prod.snd (fun _ output => PacketResponseSource.Control.source output.1 output.2) (fun _ _ _ => rfl)

theorem bothCalls_entry :
    (bothCalls marker payload oracle state trace input message initial terminal prior saved table cache).entry () =
    .source saved ⟨state, .running (firstMachine (n := n) input message), trace⟩ := rfl

theorem bothCalls_exit (output : Configuration (IdealTable n κ) × Configuration State) :
    (bothCalls marker payload oracle state trace input message initial terminal prior saved table cache).exit () output =
      .source output.1 output.2 := rfl

theorem bothCalls_budget :
    (bothCalls marker payload oracle state trace input message initial terminal prior saved table cache).budget () =
      (2 * (nativeWorldPacket (.inl message : WorldInput (Bits κ) (Bits n))).length + 3) +
        (1 + (nativeWorldBudget (.inl message : WorldInput (Bits κ) (Bits n)) + (3 * n + 4))) + secondCap n κ := rfl

theorem bothCalls_operational :
    Procedure.Operational (bothCalls marker payload oracle state trace input message initial terminal prior saved table cache) := by
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · apply Procedure.operational_certify
    exact nativeWorldCaptureRound_operational _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · apply Procedure.operational_dispatch
    intro selected
    exact secondRound_operational _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The specification retains both public request/response pairs and the
updated table. The second request uses the first random digest. -/
noncomputable def afterFirst (first : CompressionTable (Bits κ) (Bits n) × Bits n) :=
  (realWorld initial terminal first.1 (.inr (first.2, (marker, payload)))).map (fun second =>
    (encodeCompressionTable second.1,
      NativeCallback.resumed (secondMachine input first.2 marker payload).advance state
        ((nativeWorldPacket (.inl message : WorldInput (Bits κ) (Bits n)), first.2.toList) :: trace)
        (nativeWorldPacket (.inr (first.2, (marker, payload)))) second.2.toList))

noncomputable def twoWorld :=
  (realWorld initial terminal table (.inl message)).bind
    (afterFirst marker payload state trace input message initial terminal)

/-- Full public caller/table distribution for two physically composed native
calls. The first return's actual private frame enters the second call. -/
theorem bothCalls_packet :
    ((bothCalls marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).map
      (fun output => (output.1.state, output.2)) =
      twoWorld marker payload state trace input message initial terminal table := by
  simp only [bothCalls, Procedure.observe, Procedure.seq, Procedure.dispatch, PMF.map_bind,
    PMF.map_comp, Function.comp_def]
  simp only [secondFamily, secondRound_packet]
  change ((firstCertified marker payload oracle state trace input message initial terminal prior saved table cache).semantics ()).bind
    (afterFirst marker payload state trace input message initial terminal ∘ selectedAnswer state trace input message) = _
  rw [← PMF.bind_map, firstCertified_answers]
  rfl

end Foundation.Hash.Native.AdaptivePublicCaller
