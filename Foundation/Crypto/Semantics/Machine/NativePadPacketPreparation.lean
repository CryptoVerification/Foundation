import Foundation.Crypto.Semantics.Machine.NativePublicHeader
import Foundation.Crypto.Semantics.Machine.NativePadPhysicalPreparation
import Foundation.Crypto.Semantics.Machine.NativeComponentReindex

/-! A concrete fixed native preparer for a public parameter, a delimited
message and a delimited pad. It erases the unary header and source fields,
writes the flagged request/raw-pad packet, and rewinds the actual output.
No preallocated scratch space or runtime packet loader is assumed. -/
namespace Machine.NativePadPacketPreparation
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev Input := Nat × NativePadEncryption.Input

def rawInput (input : Input) : List Bool :=
  List.replicate input.1 true ++ false ::
    (FiniteBitEncoding.delimit input.2.message ++ FiniteBitEncoding.delimit input.2.pad)

def headerInput (input : Input) : NativePublicHeader.Input :=
  {count := input.1, suffix := FiniteBitEncoding.delimit input.2.message ++ FiniteBitEncoding.delimit input.2.pad}

def messageInput (input : Input) : NativeDelimitedTransfer.Input :=
  {consumed := input.1 + 1, data := input.2.message, suffix := FiniteBitEncoding.delimit input.2.pad}

def padInput (input : Input) : NativeDelimitedTransfer.Input :=
  {consumed := input.1 + 1 + 2 * input.2.message.length + 1,
   prefixBits := FiniteBitEncoding.delimit input.2.message, data := input.2.pad}

noncomputable def header : NativeComponent Input Configuration := NativePublicHeader.component.reindex headerInput

noncomputable def firstLink : TypedNativeComposition.Link header.procedure (NativeDelimitedTransfer.component true).procedure :=
  header.link (NativeDelimitedTransfer.component true)
    (fun _ machine => {machine.resumeAt 6 with halted := true})
    (by intro input output h; change output ∈ (PMF.pure (NativePublicHeader.finish (headerInput input))).support at h
        rw [PMF.mem_support_pure_iff] at h; subst output; rfl)
    (fun input _ => messageInput input)
    (by intro input output h; change output ∈ (PMF.pure (NativePublicHeader.finish (headerInput input))).support at h
        rw [PMF.mem_support_pure_iff] at h; subst output
        change (NativeDelimitedTransfer.initial (messageInput input)).rebasePc 8 =
          (NativePublicHeader.finish (headerInput input)).resumeAt 8
        simp [NativeDelimitedTransfer.initial, NativePublicHeader.finish, messageInput, headerInput,
          NativeDelimitedTransfer.destination, Configuration.resumeAt, Configuration.rebasePc])
    (fun input => 12 * input.2.message.length + 6) (fun _ _ _ => Nat.le_refl _)

def firstFinish (input : Input) : Configuration :=
  {(NativeDelimitedTransfer.finish true (messageInput input)).resumeAt 30 with halted := true}

theorem first_semantics (input : Input) : firstLink.native.execution.semantics input = PMF.pure (firstFinish input) := by
  rw [firstLink.semantics]
  change (PMF.pure (NativePublicHeader.finish (headerInput input))).bind _ = _
  rw [PMF.pure_bind]
  change (PMF.pure (NativeDelimitedTransfer.finish true (messageInput input))).map _ = _
  rw [PMF.pure_map]
  rfl

noncomputable def secondLink : TypedNativeComposition.Link firstLink.native (NativeDelimitedTransfer.component false).procedure :=
  firstLink.append (NativeDelimitedTransfer.component false) (fun input _ => padInput input)
    (by
      intro input output h
      rw [first_semantics, PMF.mem_support_pure_iff] at h
      subst output
      change (NativeDelimitedTransfer.initial (padInput input)).rebasePc 32 = (firstFinish input).resumeAt 32
      simp [NativeDelimitedTransfer.initial, NativeDelimitedTransfer.finish, NativeDelimitedTransfer.emit,
        messageInput, padInput, firstFinish, Configuration.resumeAt, Configuration.rebasePc])
    (fun input => 12 * input.2.message.length + 6) (by
      intro input _ _
      change 12 * (padInput input).data.length + 6 ≤ _
      simp [padInput, input.2.sameLength])

def secondFinish (input : Input) : Configuration :=
  {(NativeDelimitedTransfer.finish false (padInput input)).resumeAt 54 with halted := true}

theorem second_semantics (input : Input) : secondLink.native.execution.semantics input = PMF.pure (secondFinish input) := by
  rw [secondLink.semantics, first_semantics, PMF.pure_bind]
  change (PMF.pure (NativeDelimitedTransfer.finish false (padInput input))).map _ = _
  rw [PMF.pure_map]
  rfl

def rewindInput (input : Input) : NativeBitstringRewind.Input :=
  {bits := FiniteBitEncoding.delimit input.2.message ++ input.2.pad,
   other := NativeDelimitedTransfer.source
     ((padInput input).consumed + 2 * input.2.pad.length + 1) []}

noncomputable def link : TypedNativeComposition.Link secondLink.native NativeBitstringRewind.outputComponent.procedure :=
  secondLink.append NativeBitstringRewind.outputComponent (fun input _ => rewindInput input)
    (by
      intro input output h
      rw [second_semantics, PMF.mem_support_pure_iff] at h
      subst output
      change ((NativeBitstringRewind.initial (rewindInput input)).swapTapes).rebasePc 56 =
        (secondFinish input).resumeAt 56
      simp [NativeBitstringRewind.outputComponent, NativeBitstringRewind.initial, NativeDelimitedTransfer.finish,
        NativeDelimitedTransfer.destination, NativeDelimitedTransfer.emit, padInput, secondFinish, rewindInput,
        Configuration.resumeAt, Configuration.rebasePc, Configuration.swapTapes])
    (fun input => 6 * input.2.message.length + 6) (by
      intro input _ _
      change 2 * (rewindInput input).bits.length + 4 ≤ _
      simp only [rewindInput, List.length_append, FiniteBitEncoding.delimit_length, input.2.sameLength]
      omega)

def fixedCode : Program := ((NativePublicHeader.code.followedBy (NativeDelimitedTransfer.code true)).followedBy
  (NativeDelimitedTransfer.code false)).followedBy rewindBitstring.swapTapes

theorem fixedCode_eq : fixedCode = link.code := rfl

theorem code_length : fixedCode.length = 62 := by
  rw [fixedCode_eq, link.code_length]
  change secondLink.code.length + 4 + 3 = _
  rw [secondLink.code_length]
  change firstLink.code.length + 21 + 3 + 4 + 3 = _
  rw [firstLink.code_length]
  rfl

def finish (input : Input) : Configuration :=
  {(NativeBitstringRewind.finish (rewindInput input)).swapTapes.resumeAt 61 with halted := true}

theorem semantics (input : Input) : link.native.execution.semantics input = PMF.pure (finish input) := by
  rw [link.semantics, second_semantics, PMF.pure_bind]
  change (PMF.pure (NativeBitstringRewind.finish (rewindInput input))).map _ = _
  rw [PMF.pure_map]
  rfl

def timeBound (input : Input) : Nat := 4 * input.1 + 30 * input.2.message.length + 25

theorem budget (input : Input) : link.native.execution.budget input = timeBound input := by
  rw [link.budget, secondLink.budget, firstLink.budget]
  change (4 * input.1 + 4) + (12 * input.2.message.length + 6) + 1 +
    (12 * input.2.message.length + 6) + 1 + (6 * input.2.message.length + 6) + 1 = _
  unfold timeBound
  omega

theorem entry (input : Input) : link.native.execution.entry input = Configuration.initial (rawInput input) := by
  rw [link.native_entry, secondLink.native_entry, firstLink.native_entry]
  change NativePublicHeader.initial (headerInput input) = Configuration.initial (rawInput input)
  simp [NativePublicHeader.initial, headerInput, NativeDelimitedTransfer.source, Configuration.initial, rawInput]
  cases h : input.1 <;> simp [h, List.replicate_succ, Tape.ofBits]

theorem run (input : Input) (horizon : Nat) (hTime : timeBound input ≤ horizon) :
    evalConfigWithin fixedCode (Configuration.initial (rawInput input)) horizon = PMF.pure (finish input) := by
  have h := link.run input horizon (by rw [← link.budget, budget]; exact hTime)
  change evalConfigWithin link.code (link.native.execution.entry input) horizon = link.native.execution.semantics input at h
  rw [entry, semantics] at h
  exact h

private theorem request_eq_delimit (bits : List Bool) : FlaggedBlockXor.request bits = FiniteBitEncoding.delimit bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      change true :: bit :: FlaggedBlockXor.request rest = true :: bit :: FiniteBitEncoding.delimit rest
      rw [ih]

theorem handoff (input : Input) : ((finish input).resumeAt 0).Equivalent (NativePadEncryption.initial input.2) := by
  change ((finish input).resumeAt 0).Equivalent
    ((FlaggedBlockXor.Contextual.initial (NativePadEncryption.maskInput input.2)).swapTapes)
  rw [FlaggedBlockXor.Contextual.initial_eq]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change (rewindInput input).other.Equivalent ({right := List.replicate input.2.message.length none ++ [none]} : Tape)
    change ({left := List.replicate _ none} : Tape).Equivalent _
    exact (Tape.append_left_blank_equivalent ({} : Tape) _ (by simp)).trans
      (Tape.append_right_blank_equivalent ({} : Tape) (List.replicate input.2.message.length none ++ [none]) (by
        intro cell h
        rcases List.mem_append.mp h with h | h
        · exact (List.mem_replicate.mp h).2
        · simpa using h)).symm
  · have hRequest := request_eq_delimit input.2.message
    cases hMessage : input.2.message <;>
      simp [finish, rewindInput, NativeBitstringRewind.finish, NativePadEncryption.maskInput,
        Configuration.resumeAt, Configuration.swapTapes, hMessage, request_eq_delimit,
        FiniteBitEncoding.delimit, OneTimePad.delimitedTape, Tape.moveRight, Tape.Equivalent]

noncomputable def component : NativeComponent Input NativePadEncryption.Input where
  procedure := Machine.Procedure.ofFixed fixedCode (fun input => Configuration.initial (rawInput input)) (fun input _ => finish input)
    (fun input => PMF.pure input.2) timeBound
    (fun input => by simpa only [PMF.pure_map] using run input (timeBound input) (Nat.le_refl _))
  closed := link.component.closed
  entry := fun _ => by change 0 < fixedCode.length; rw [code_length]; decide
  active := fun _ => rfl
  halted := fun _ _ _ => rfl

noncomputable def physical : NativePadPipeline.PhysicalPreparation Input where
  component := component
  read := fun input _ => input.2
  read_return := by intro input output h; change output ∈ (PMF.pure input.2).support at h
                    rw [PMF.mem_support_pure_iff] at h; exact h.symm
  handoff := by intro input output h; change output ∈ (PMF.pure input.2).support at h
                rw [PMF.mem_support_pure_iff] at h; subst output; exact handoff input
  width := fun input => input.2.message.length
  width_eq := by intro input output h; change output ∈ (PMF.pure input.2).support at h
                 rw [PMF.mem_support_pure_iff] at h; subst output; rfl

end Machine.NativePadPacketPreparation
