import Foundation.Crypto.Semantics.Machine.NativeResponsePacket
import Foundation.Crypto.Semantics.Machine.NativeFirstArrivalContinuation
import Foundation.Crypto.Semantics.Machine.NativeComponentReindex
import Foundation.Crypto.Semantics.ProcedureFixedContinuation

/-! A real execution contract for seeking the public prefix, loading the
received response, rewinding the packet and transferring into the consumer.
Every control transfer is charged. Native blocks retain first-arrival costs. -/
namespace Machine.NativeSingleChallenge
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable (distribution : PMF (List Bool)) (code : Program) (prefixBits response : List Bool)

def seekBoundary : Control → Bool
  | .seeking machine _ => machine.halted
  | _ => false

def rewindBoundary : Control → Bool
  | .rewinding machine => machine.halted
  | _ => false

def loaderSourceBoundary : DelimitedResponseLoading.Control → Bool
  | .done _ => true
  | _ => false

def loaderBoundary : Control → Bool
  | .loading state => loaderSourceBoundary state
  | _ => false

noncomputable def seek : TimedExecution.Procedure (step distribution code) Unit Configuration :=
  (NativeBitstringSeekEnd.component.reindex (fun _ : Unit => NativeResponsePacket.seekInput prefixBits)).continueIn
    (step distribution code) seekBoundary (fun machine => .seeking machine response) (fun _ => rfl)
    (fun machine h => by
      change step distribution code (.seeking machine response) = (stepPMF NativeBitstringSeekEnd.code machine).map (fun next => .seeking next response)
      simp [step, h])

theorem seek_semantics : (seek distribution code prefixBits response).semantics () =
    PMF.pure (NativeBitstringSeekEnd.finish (NativeResponsePacket.seekInput prefixBits)) := by
  change (PMF.pure (NativeBitstringSeekEnd.finish (NativeResponsePacket.seekInput prefixBits))).map (fun state => state) = _
  rw [PMF.pure_map]

noncomputable def seekHandoff : TimedExecution.Procedure (step distribution code) Unit Unit :=
  TimedExecution.Procedure.ofFixed (step distribution code)
    (fun _ => .seeking (NativeBitstringSeekEnd.finish (NativeResponsePacket.seekInput prefixBits)) response)
    (fun _ _ => .loading (.flag (DelimitedResponseLoading.start prefixBits {} 0) response)) (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by simp only [eval, PMF.pure_bind, PMF.pure_map, NativeResponsePacket.seek_handoff])

noncomputable def loader : TimedExecution.Procedure (step distribution code) Unit Configuration :=
  (DelimitedResponseLoading.procedure prefixBits response {} 0).liftBoundary loaderSourceBoundary
    (fun _ _ _ => rfl)
    (fun state h => by cases state <;> simp_all [loaderSourceBoundary, DelimitedResponseLoading.step])
    (fun _ state => match state with | .done machine => machine | _ => {}) (fun _ _ => rfl)
    (step distribution code) loaderBoundary Control.loading (fun _ => rfl)
    (fun state h => by cases state <;> simp_all [loaderSourceBoundary, step])

noncomputable def loaderHandoff : TimedExecution.Procedure (step distribution code) Unit Unit :=
  TimedExecution.Procedure.ofFixed (step distribution code)
    (fun _ => .loading (.done (DelimitedResponseLoading.finish prefixBits response {} 0)))
    (fun _ _ => .rewinding (NativeBitstringRewind.initial (NativeResponsePacket.rewindInput prefixBits response)))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by simp only [eval, PMF.pure_bind, PMF.pure_map, NativeResponsePacket.loader_handoff])

noncomputable def rewind : TimedExecution.Procedure (step distribution code) Unit Configuration :=
  (NativeBitstringRewind.component.reindex (fun _ : Unit => NativeResponsePacket.rewindInput prefixBits response)).continueIn
    (step distribution code) rewindBoundary Control.rewinding (fun _ => rfl)
    (fun machine h => by
      change step distribution code (.rewinding machine) = (stepPMF rewindBitstring machine).map Control.rewinding
      simp [step, h])

theorem rewind_semantics : (rewind distribution code prefixBits response).semantics () =
    PMF.pure (NativeBitstringRewind.finish (NativeResponsePacket.rewindInput prefixBits response)) := by
  change (PMF.pure (NativeBitstringRewind.finish (NativeResponsePacket.rewindInput prefixBits response))).map (fun state => state) = _
  rw [PMF.pure_map]

noncomputable def rewindHandoff : TimedExecution.Procedure (step distribution code) Unit Unit :=
  TimedExecution.Procedure.ofFixed (step distribution code)
    (fun _ => .rewinding (NativeBitstringRewind.finish (NativeResponsePacket.rewindInput prefixBits response)))
    (fun _ _ => .executing ((NativeBitstringRewind.finish (NativeResponsePacket.rewindInput prefixBits response)).resumeAt 0))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by simp [eval, step, NativeBitstringRewind.finish, PMF.pure_map])

noncomputable def throughSeek : TimedExecution.Procedure (step distribution code) Unit Unit :=
  (seek distribution code prefixBits response).andThen (seekHandoff distribution code prefixBits response) (by
    intro input state h
    cases input
    rw [seek_semantics, PMF.mem_support_pure_iff] at h
    subst state
    rfl)

noncomputable def throughLoader : TimedExecution.Procedure (step distribution code) Unit Unit :=
  ((throughSeek distribution code prefixBits response).andThen (loader distribution code prefixBits response) (fun _ _ _ => rfl)).andThen
    (loaderHandoff distribution code prefixBits response) (by
      intro input state h
      cases input
      rw [TimedExecution.Procedure.andThen_semantics] at h
      change state ∈ (PMF.pure (DelimitedResponseLoading.finish prefixBits response {} 0)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst state
      rfl)

noncomputable def preparation : TimedExecution.Procedure (step distribution code) Unit Unit :=
  ((throughLoader distribution code prefixBits response).andThen (rewind distribution code prefixBits response) (fun _ _ _ => rfl)).andThen
    (rewindHandoff distribution code prefixBits response) (by
      intro input state h
      cases input
      rw [TimedExecution.Procedure.andThen_semantics, rewind_semantics, PMF.mem_support_pure_iff] at h
      subst state
      rfl)

theorem preparation_entry : (preparation distribution code prefixBits response).entry () =
    .seeking (Configuration.initial prefixBits) response := by
  change Control.seeking (NativeBitstringSeekEnd.initial (NativeResponsePacket.seekInput prefixBits)) response = _
  rw [NativeResponsePacket.seek_entry]

theorem preparation_exit : (preparation distribution code prefixBits response).exit () () =
    .executing ((NativeBitstringRewind.finish (NativeResponsePacket.rewindInput prefixBits response)).resumeAt 0) := rfl

theorem preparation_semantics : (preparation distribution code prefixBits response).semantics () = PMF.pure () :=
  TimedExecution.Procedure.andThen_semantics _ _ _ _

theorem preparation_budget : (preparation distribution code prefixBits response).budget () =
    NativeResponsePacket.timeBound prefixBits.length response.length := by
  change (3 * prefixBits.length + 2) + 1 + (4 * response.length + 2) + 1 +
    (2 * (NativeResponsePacket.rewindInput prefixBits response).bits.length + 4) + 1 = _
  exact NativeResponsePacket.timeBound_eq prefixBits response

end Machine.NativeSingleChallenge
