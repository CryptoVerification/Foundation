import Foundation.Examples.ReusableResponseTwoQueriesPotential
import Foundation.Crypto.Semantics.Oracle.ReusableBitInitialization

/-! One fixed native sampler generates any-width private keys, physically
aligns the real output tape, then executes both adaptive requests and the
actual caller halt. The whole key/cost correlation is retained. -/
namespace Foundation.Examples.ReusableResponseInitializedTwoQueries
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ResponseHandoffProgram
universe u
set_option backward.isDefEq.respectTransparency false

variable {State : Type u} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (width : Nat)

noncomputable abbrev componentStep := ResponseHandoffProgram.step ReusableResponseTwoQueries.native
abbrev ready := ResponseHandoffProgram.Callback.ready
abbrev callerFrame := (⟨state, .running (ReusableResponseTwoQueries.caller request), trace⟩ : Configuration State)
noncomputable abbrev step := ReusableResponseInitialization.step componentStep ReusableResponse.begin ready
  OneTimePad.keygen ReusableResponseTwoQueries.native ReusableResponseTwoQueries.code oracle (callerFrame state trace request)

noncomputable def initialization :=
  ReusableBitInitialization.initialization componentStep ReusableResponse.begin ready
    ReusableResponseTwoQueries.native ReusableResponseTwoQueries.code oracle (callerFrame state trace request) width

noncomputable def consumer := Procedure.dispatch (fun key : Bits width =>
  (ReusableResponseTwoQueries.Potential.whole oracle key.toList state trace request).reindex (fun _ : Unit => .first))

theorem consumer_budget (key : Bits width) :
    (consumer oracle state trace request width).budget key = 18 * width + 5 * request.length + 66 := by
  change (ReusableResponseTwoQueries.Potential.whole oracle key.toList state trace request).budget .first = _
  rw [ReusableResponseTwoQueries.Potential.budget]
  simp [ReusableResponseTwoQueries.Potential.remaining]

theorem consumer_semantics (key : Bits width) :
    (consumer oracle state trace request width).semantics key = PMF.pure .stopped :=
  ReusableResponseTwoQueries.Potential.whole_semantics oracle key.toList state trace request

noncomputable def whole :=
  ReusableResponseInitialization.follow componentStep ReusableResponse.begin ready OneTimePad.keygen
    ReusableResponseTwoQueries.native ReusableResponseTwoQueries.code oracle (callerFrame state trace request)
    (initialization oracle state trace request width)
    (fun key : Bits width => retainedKey key.toList) (fun _ _ _ => rfl)
    (consumer oracle state trace request width) (fun _ => rfl)
    (fun _ => 18 * width + 5 * request.length + 66)
    (fun _ result _ => le_of_eq (consumer_budget oracle state trace request width result.1))

theorem budget : (whole oracle state trace request width).budget () = 24 * width + 5 * request.length + 72 := by
  rw [whole, ReusableResponseInitialization.follow_budget]
  change (initialization oracle state trace request width).budget () + (18 * width + 5 * request.length + 66) = _
  rw [initialization, ReusableBitInitialization.budget]
  omega

theorem semantics :
    (whole oracle state trace request width).semantics () =
      (uniform (Bits width)).map (fun key => ((key, ()), ReusableResponseTwoQueries.Potential.Phase.stopped)) := by
  rw [whole, ReusableResponseInitialization.follow_semantics]
  change ((initialization oracle state trace request width).semantics ()).bind _ = _
  rw [initialization, ReusableBitInitialization.initialization, ReusableResponseInitialization.semantics]
  change ((uniform (Bits width)).map (fun key => (key, ()))).bind _ = _
  simp only [PMF.bind_map, consumer_semantics, PMF.pure_map, Function.comp_def]
  rfl

theorem exit (result : (Bits width × Unit) × ReusableResponseTwoQueries.Potential.Phase) :
    (whole oracle state trace request width).exit () result =
      .active (ReusableResponseTwoQueries.Potential.embed result.1.1.toList state trace request result.2) := rfl

theorem costed : (whole oracle state trace request width).costed () =
    ((initialization oracle state trace request width).costed ()).bind (fun generated =>
      ((consumer oracle state trace request width).costed generated.1.1).map (fun returned =>
        ((generated.1, returned.1), generated.2 + returned.2))) := rfl

theorem run (horizon : Nat) (hBudget : 24 * width + 5 * request.length + 72 ≤ horizon) :
    TimedExecution.eval (step oracle state trace request) horizon
      (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      (uniform (Bits width)).map (fun key => ReusableResponseInitialization.Control.active
        (ReusableResponseSource.Control.source (retainedKey key.toList)
          ⟨state, .running (ReusableResponseTwoQueries.finalCaller request), ReusableResponseTwoQueries.finalTrace trace request⟩)) := by
  have h := (whole oracle state trace request width).final_run ()
    (by
      intro result hResult
      rw [semantics, PMF.mem_support_map_iff] at hResult
      obtain ⟨key, _, rfl⟩ := hResult
      rw [exit]
      simp [ReusableResponseInitialization.step, ReusableResponseTwoQueries.Potential.embed,
        ReusableResponseTwoQueries.Potential.frame, ReusableResponseSource.step, Reification.timedStep,
        Reification.terminal, ReusableResponseTwoQueries.finalCaller, PMF.pure_map])
    horizon (by rw [budget]; exact hBudget)
  rw [semantics, PMF.map_comp] at h
  exact h

end Foundation.Examples.ReusableResponseInitializedTwoQueries
