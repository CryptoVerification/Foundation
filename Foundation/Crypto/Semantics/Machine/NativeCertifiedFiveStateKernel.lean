import Foundation.Crypto.Semantics.Machine.NativeCleanFiveStateSampler
import Foundation.Crypto.Semantics.Probability.FairCycleRelations

/-! Compile any certified five-by-five integer table of row total 4096 to a
clean native sampler. Local edit paths supply the certificate constructively.
This contract fixes five states, twelve fair bits, and a one-bit retained label. -/
namespace Machine.NativeCertifiedFiveStateKernel
open Foundation.Probability IntegerKernelCycles NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
variable {source target : Fin 5 → Nat} {table : Fin 5 → Fin 5 → ℤ}

def draw (certificate : Certificate source target (2 ^ 12) table) : NativeFiveStateSampler.Sampler :=
  fun key coins => sampleCounts (natural table key) (certificate.natural_rows key) (bitIndexEquiv 12 coins)

theorem draw_law (certificate : Certificate source target (2 ^ 12) table) (key : Fin 5) :
    (uniform (Fin 12 → Bool)).map (draw certificate key) = FairCycleKernel.kernel 12 certificate key :=
  FiniteFairKernelCertificate.bits_law 12 (natural table) certificate.natural_rows key

theorem kernel_eq (certificate : Certificate source target (2 ^ 12) table) :
    NativeFiveStateSampler.kernel (draw certificate) = FairCycleKernel.kernel 12 certificate := funext (draw_law certificate)

def code (certificate : Certificate source target (2 ^ 12) table) : Program := NativeCleanFiveStateSampler.code (draw certificate)

theorem stops (certificate : Certificate source target (2 ^ 12) table) : StopsEverywhere (code certificate) 307 :=
  NativeCleanFiveStateSampler.stops (draw certificate)

theorem code_length (certificate : Certificate source target (2 ^ 12) table) : (code certificate).length ≤ 985484 :=
  NativeCleanFiveStateSampler.code_length (draw certificate)

theorem full_run (certificate : Certificate source target (2 ^ 12) table) (key : Fin 5) (ciphertext : Bool)
    (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (code certificate) (NativeFiveStateSampler.entry key ciphertext inputSuffix outputSuffix) 307 =
      (FairCycleKernel.kernel 12 certificate key).map (fun result => NativeCleanFiveStateSampler.finish
        ((NativeFiveStateSampler.code (draw certificate)).length + NativeCleanFiveStateSampler.cleanup.length + 2)
        result ciphertext inputSuffix outputSuffix) := by
  rw [code,NativeCleanFiveStateSampler.full_run,kernel_eq]

theorem initial_law (certificate : Certificate source target (2 ^ 12) table) (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin (code certificate) (Configuration.initial (NativeFiveStateSampler.rawInput key ciphertext)) 307).map
      NativeEightBitCipher.observe = (FairCycleKernel.kernel 12 certificate key).map (fun result => some (result,ciphertext)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativeFiveStateSampler.entry_equivalent key ciphertext).symm
    307 _ NativeControlledCipherInitial.observe_equivalent]
  rw [code,NativeCleanFiveStateSampler.framed_law,kernel_eq]

theorem initial_state_law (certificate : Certificate source target (2 ^ 12) table) (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin (code certificate) (Configuration.initial (NativeFiveStateSampler.rawInput key ciphertext)) 307).map
      NativePreparedState.state = (FairCycleKernel.kernel 12 certificate key).map (fun result => NativePreparedState.state
        (NativeCleanFiveStateSampler.finish
          ((NativeFiveStateSampler.code (draw certificate)).length + NativeCleanFiveStateSampler.cleanup.length + 2)
          result ciphertext {} {})) := by
  rw [code,NativeCleanFiveStateSampler.initial_state_law,kernel_eq]

def bounded (certificate : Certificate source target (2 ^ 12) table) : CryptoLogic.BoundedProgram :=
  NativeCleanFiveStateSampler.bounded (draw certificate)

theorem polynomial_time (certificate : Certificate source target (2 ^ 12) table) : PolynomialTime (code certificate) :=
  (bounded certificate).polynomialTime

def pathCode {before after : Fin 5 → Fin 5 → ℤ} (certificate : Certificate source target (2 ^ 12) before)
    (path : Path source before after) : Program := code (path.sound certificate)

theorem path_stops {before after : Fin 5 → Fin 5 → ℤ} (certificate : Certificate source target (2 ^ 12) before)
    (path : Path source before after) : StopsEverywhere (pathCode certificate path) 307 := stops (path.sound certificate)

theorem path_length {before after : Fin 5 → Fin 5 → ℤ} (certificate : Certificate source target (2 ^ 12) before)
    (path : Path source before after) : (pathCode certificate path).length ≤ 985484 := code_length (path.sound certificate)

theorem path_polynomial_time {before after : Fin 5 → Fin 5 → ℤ} (certificate : Certificate source target (2 ^ 12) before)
    (path : Path source before after) : PolynomialTime (pathCode certificate path) := polynomial_time (path.sound certificate)

theorem path_joint_law {before after : Fin 5 → Fin 5 → ℤ} (D : Nat) (positive : 0 < D)
    (certificate : Certificate source target (2 ^ 12) before) (path : Path source before after)
    (p q : PMF (Fin 5))
    (sourceMass : ∀ a, (p a).toReal = (source a : ℝ) / D)
    (targetMass : ∀ b, (q b).toReal = (target b : ℝ) / D)
    (inputLabel outputLabel : Fin 5 → Bool)
    (old : ∀ a b, before a b ≠ 0 → outputLabel b = inputLabel a)
    (compatible : Respects (fun a b => outputLabel b = inputLabel a) path) :
    ((p.map (fun key => (key,inputLabel key))).bind (fun original =>
      evalConfigWithin (pathCode certificate path)
        (Configuration.initial (NativeFiveStateSampler.rawInput original.1 original.2)) 307)).map NativeEightBitCipher.observe =
      (q.map (fun key => (key,outputLabel key))).map some := by
  unfold pathCode
  rw [PMF.map_bind]
  simp_rw [initial_law]
  have h := congrArg (PMF.map some) (FairCycleKernel.path_joint_preserves 12 D positive certificate path p q
    sourceMass targetMass inputLabel outputLabel old compatible)
  simpa only [PMF.map_bind,PMF.map_comp,Function.comp_def,FairCycleKernel.pathKernel] using h

theorem path_joint_state_law {before after : Fin 5 → Fin 5 → ℤ} (D : Nat) (positive : 0 < D)
    (certificate : Certificate source target (2 ^ 12) before) (path : Path source before after)
    (p q : PMF (Fin 5))
    (sourceMass : ∀ a, (p a).toReal = (source a : ℝ) / D)
    (targetMass : ∀ b, (q b).toReal = (target b : ℝ) / D)
    (inputLabel outputLabel : Fin 5 → Bool)
    (old : ∀ a b, before a b ≠ 0 → outputLabel b = inputLabel a)
    (compatible : Respects (fun a b => outputLabel b = inputLabel a) path) :
    ((p.map (fun key => (key,inputLabel key))).bind (fun original =>
      evalConfigWithin (pathCode certificate path)
        (Configuration.initial (NativeFiveStateSampler.rawInput original.1 original.2)) 307)).map NativePreparedState.state =
      (q.map (fun key => (key,outputLabel key))).map (fun final => NativePreparedState.state
        (NativeCleanFiveStateSampler.finish
          ((NativeFiveStateSampler.code (draw (path.sound certificate))).length + NativeCleanFiveStateSampler.cleanup.length + 2)
          final.1 final.2 {} {})) := by
  unfold pathCode
  rw [PMF.map_bind]
  simp_rw [initial_state_law]
  have h := congrArg (PMF.map (fun final : Fin 5 × Bool => NativePreparedState.state
    (NativeCleanFiveStateSampler.finish
      ((NativeFiveStateSampler.code (draw (path.sound certificate))).length + NativeCleanFiveStateSampler.cleanup.length + 2)
      final.1 final.2 {} {}))) (FairCycleKernel.path_joint_preserves 12 D positive certificate path p q
        sourceMass targetMass inputLabel outputLabel old compatible)
  simpa only [PMF.map_bind,PMF.map_comp,Function.comp_def,FairCycleKernel.pathKernel] using h

end Machine.NativeCertifiedFiveStateKernel
