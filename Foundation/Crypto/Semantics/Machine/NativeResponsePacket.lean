import Foundation.Crypto.Semantics.Machine.NativeSingleChallengeControl

/-! Physical handoff facts for the generic challenge controller. The public
prefix is scanned, the received raw response is written cell by cell in
encoding, and the entire actual packet is rewound for the native consumer.
Outer blank padding survives; only cell equivalence is used at consumer entry. -/
namespace Machine.NativeResponsePacket
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def seekInput (prefixBits : List Bool) : NativeBitstringSeekEnd.Input := {data := prefixBits}

def rewindInput (prefixBits response : List Bool) : NativeBitstringRewind.Input :=
  {bits := prefixBits ++ FiniteBitEncoding.delimit response, other := {}}

theorem seek_entry (prefixBits : List Bool) :
    NativeBitstringSeekEnd.initial (seekInput prefixBits) = Configuration.initial prefixBits := by
  cases prefixBits <;> rfl

theorem seek_loader_entry (prefixBits : List Bool) :
    (NativeBitstringSeekEnd.finish (seekInput prefixBits)).resumeAt 0 =
      DelimitedResponseLoading.start prefixBits {} 0 := rfl

theorem loader_rewind_entry (prefixBits response : List Bool) (pc : Nat) :
    (DelimitedResponseLoading.finish prefixBits response {} pc).resumeAt 0 =
      NativeBitstringRewind.initial (rewindInput prefixBits response) := rfl

theorem rewind_consumer_entry (prefixBits response : List Bool) :
    ((NativeBitstringRewind.finish (rewindInput prefixBits response)).resumeAt 0).Equivalent
      (Configuration.initial (prefixBits ++ FiniteBitEncoding.delimit response)) := by
  refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
  exact rewindBitstringFinish_input_equivalent _ {}

theorem seek_handoff (distribution : PMF (List Bool)) (code : Program) (prefixBits response : List Bool) :
    NativeSingleChallenge.step distribution code
      (.seeking (NativeBitstringSeekEnd.finish (seekInput prefixBits)) response) =
        PMF.pure (.loading (.flag (DelimitedResponseLoading.start prefixBits {} 0) response)) := by
  change PMF.pure (NativeSingleChallenge.Control.loading (.flag ((NativeBitstringSeekEnd.finish (seekInput prefixBits)).resumeAt 0) response)) = _
  rw [seek_loader_entry]

theorem loader_handoff (distribution : PMF (List Bool)) (code : Program)
    (prefixBits response : List Bool) (pc : Nat) :
    NativeSingleChallenge.step distribution code
      (.loading (.done (DelimitedResponseLoading.finish prefixBits response {} pc))) =
        PMF.pure (.rewinding (NativeBitstringRewind.initial (rewindInput prefixBits response))) := by
  change PMF.pure (NativeSingleChallenge.Control.rewinding ((DelimitedResponseLoading.finish prefixBits response {} pc).resumeAt 0)) = _
  rw [loader_rewind_entry]

/-- Cost of seeking/loading/rewinding and the three actual control transfers,
excluding the external query and the native consumer. -/
def timeBound (prefixSize responseSize : Nat) : Nat := 5 * prefixSize + 8 * responseSize + 13

theorem timeBound_eq (prefixBits response : List Bool) :
    (3 * prefixBits.length + 2) + 1 + (4 * response.length + 2) + 1 +
      (2 * (prefixBits ++ FiniteBitEncoding.delimit response).length + 4) + 1 =
        timeBound prefixBits.length response.length := by
  simp only [List.length_append, FiniteBitEncoding.delimit_length, timeBound]
  omega

end Machine.NativeResponsePacket
