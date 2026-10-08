import Foundation.Crypto.Semantics.Oracle.NativeCallback

/-! Deliver an already halted physical component to a suspended source,
retaining an arbitrary private frame. The input contract certifies the
existing tape; no packet tape is allocated or substituted at entry. -/
namespace CryptoOracle.Interactive.RetainedResponseDelivery
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false

structure Input where
  machine : Machine.Configuration
  packet : List Bool
  halted : machine.halted = true
  layout : machine.outputTape = Machine.ResponseExport.endTape packet

variable (native : Machine.Program)

/-- Identity contract at an existing physical halt. Producing this machine
is an obligation of the preceding component, not a zero-cost computation. -/
noncomputable def ready (input : Input) : Machine.Procedure Unit Unit :=
  Machine.Procedure.ofFixed native (fun _ => input.machine)
    (fun _ _ => input.machine) (fun _ => PMF.pure ()) (fun _ => 0)
    (fun _ => by simp [Machine.evalConfigWithin, PMF.pure_map])

variable {State : Type u} (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

noncomputable def delivery (input : Input) :=
  NativeCallback.callback (ready native input) (fun _ => input.packet)
    (fun _ _ => input.halted) (fun _ _ => input.layout)
    (fun _ _ => ()) (fun _ _ => rfl)
    (fun _ => input.packet.length) (fun _ _ _ => Nat.le_refl _)
    code oracle saved state trace request

variable (input : Input)

theorem budget :
    (delivery native code oracle saved state trace request input).budget () =
      6 * input.packet.length + 7 := by
  rw [delivery, NativeCallback.callback_budget]
  change 0 + (6 * input.packet.length + 7) = _
  exact Nat.zero_add _

/-- The retained frame is never an argument of the component or source step. -/
noncomputable def framed (Saved : Type v) :=
  (delivery native code oracle saved state trace request input).frame Saved

theorem framed_budget {Saved : Type v} (retained : Saved) :
    (framed native code oracle saved state trace request input Saved).budget ((), retained) =
      6 * input.packet.length + 7 := budget native code oracle saved state trace request input

/-- The exact physical native configuration, rather than a reconstructed
packet configuration, is the entry state. -/
theorem framed_entry {Saved : Type v} (retained : Saved) :
    (framed native code oracle saved state trace request input Saved).entry ((), retained) =
      (NativeCallback.Control.responding (.running input.machine), retained) := rfl

theorem framed_semantics {Saved : Type v} (retained : Saved) :
    (framed native code oracle saved state trace request input Saved).semantics ((), retained) =
      PMF.pure (input.packet, ()) := by
  simp [framed, delivery, NativeCallback.callback, NativeCallback.exported, NativeCallback.transfer,
    ready, Machine.Procedure.ofFixed, Procedure.frame, Procedure.seq, Procedure.liftBoundary,
    Procedure.ofFixed, PMF.pure_map]

theorem framed_distribution {Saved : Type v} (retained : Saved) :
    ((framed native code oracle saved state trace request input Saved).costed ((), retained)).map
      (fun result => (framed native code oracle saved state trace request input Saved).exit ((), retained) result.1) =
      PMF.pure (NativeCallback.Control.source
        (NativeCallback.resumed saved state trace request input.packet), retained) := by
  let P := framed native code oracle saved state trace request input Saved
  have h := congrArg (fun distribution => distribution.map (P.exit ((), retained)))
    (P.correct ((), retained))
  rw [framed_semantics, PMF.pure_map] at h
  have he : P.exit ((), retained) (input.packet, ()) =
      (NativeCallback.Control.source (NativeCallback.resumed saved state trace request input.packet), retained) := rfl
  rw [he] at h
  simpa only [P, PMF.map_comp, Function.comp_def] using h

/-- Residual time continues the actual saved caller; the response endpoint
is not artificially made absorbing. -/
theorem framed_law {Saved : Type v} (retained : Saved) (horizon : Nat)
    (hBudget : 6 * input.packet.length + 7 ≤ horizon) :
    TimedExecution.eval (framedStep (NativeCallback.step native code oracle saved state trace request)) horizon
      (NativeCallback.Control.responding (.running input.machine), retained) =
      ((framed native code oracle saved state trace request input Saved).costed ((), retained)).bind
        (fun result => TimedExecution.eval (framedStep (NativeCallback.step native code oracle saved state trace request))
          (horizon - result.2)
          (NativeCallback.Control.source (NativeCallback.resumed saved state trace request result.1.1), retained)) := by
  exact (framed native code oracle saved state trace request input Saved).law ((), retained) horizon
    (by rw [framed_budget]; exact hBudget)

/-- Preservation holds at every prefix, including after source resumption. -/
theorem retained_prefix {Saved : Type v} (retained : Saved) (horizon : Nat)
    (target : NativeCallback.Control State × Saved)
    (hTarget : target ∈ (TimedExecution.eval
      (framedStep (NativeCallback.step native code oracle saved state trace request)) horizon
      (NativeCallback.Control.responding (.running input.machine), retained)).support) :
    target.2 = retained :=
  framed_saved _ horizon _ retained target hTarget

end CryptoOracle.Interactive.RetainedResponseDelivery
