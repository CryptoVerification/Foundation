import Foundation.Examples.SeededGeneratorAssembly
import Foundation.Crypto.Semantics.Machine.NativeCompositionResources

/-! Use the same native link for joint tape observations, actual-cost
reachability and storage. The identity expander is an implementation
regression only, not an assumption of secure stretching. -/
namespace Foundation.Examples.NativeCompositionCertificates
open Machine Foundation.Probability Foundation.Symmetric TimedExecution
open Foundation.Symmetric.EncryptThenMAC
open SeededGeneratorAssembly (generator expander finish)
set_option backward.isDefEq.respectTransparency false

/-- Observe both tapes together, dropping heads only in this logical
observation. The runtime result still retains the complete physical state. -/
theorem joint_observation (width : Nat) (target : Configuration)
    (hTarget : target ∈ ((expander.assembled width).execution.semantics ()).support) :
    (target.inputTape.bits, target.outputTape.bits.length) = (List.replicate width true, width) := by
  apply (expander.link width).tapes_frame
    (fun input output => (input.bits, output.bits.length))
    (fun _ => (List.replicate width true, width)) _ _ () target hTarget
  · intro input seed _
    change ((ResponseExport.endTape (List.replicate width true)).bits,
      (ResponseExport.endTape seed.toList).bits.length) = _
    simp [ResponseExport.endTape, Tape.bits, List.filterMap_map, Bits.length_toList, generator]
  · intro seed output hOutput
    change output ∈ (PMF.pure (finish (SeededGeneratorImplementation.seedEntry generator width seed))).support at hOutput
    rw [PMF.mem_support_pure_iff] at hOutput
    subst output
    rfl

theorem costed_reachable (width : Nat) (result : Configuration × Nat)
    (hResult : result ∈ ((expander.assembled width).execution.costed ()).support) :
    result.1 ∈ (TimedExecution.eval (stepPMF (OneTimePad.keygen.followedBy expander.code)) result.2
      (Configuration.initial (List.replicate width true))).support := by
  have h := expander.assembled_operational width () result hResult
  change result.1 ∈ (TimedExecution.eval (stepPMF (OneTimePad.keygen.followedBy expander.code)) result.2
    ((Configuration.initial (List.replicate width true)).rebasePc 0)).support at h
  simpa only [Configuration.rebasePc, Nat.zero_add] using h

theorem costed_storage (width : Nat) (result : Configuration × Nat)
    (hResult : result ∈ ((expander.assembled width).execution.costed ()).support) :
    (NativeEncodedResources.completeEncoding.encode (OneTimePad.keygen.followedBy expander.code, result.1)).length ≤
      NativeEncodedResources.bound (OneTimePad.keygen.followedBy expander.code) 0
        (Configuration.initial (List.replicate width true)).tapeCells result.2 :=
  (expander.link width).storage_costed () result hResult

end Foundation.Examples.NativeCompositionCertificates
