import Foundation.Crypto.Semantics.Machine.NativeReferenceCouplingExecution

/-! A native exit adapter restores the reference public packet while keeping
the sampled private key. Cell equivalence handles only redundant blank cells;
the output writes and all head movements are executed and charged. -/
namespace Machine.NativeCouplingExitAdapter
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def leaf (decision : Bool) : Program :=
  [.moveLeft .output, .write .output decision, .moveLeft .output,
   .branch .output 10 4 6, .write .output true, .jump 8,
   .write .output false, .jump 8, .moveRight .output, .moveRight .output, .halt]

theorem leaf_run (decision oldBit ciphertext : Bool) (input : Tape) :
    evalConfigWithin (leaf decision)
      (NativeBitChoice.start input {left := [some oldBit,some ciphertext]}) 9 =
      PMF.pure {pc := 10, inputTape := input, outputTape := {left := [some decision,some (!ciphertext)]}, halted := true} := by
  cases ciphertext <;>
    simp [leaf, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.moveLeft, Tape.moveRight, Tape.write]

theorem leaf_stops (decision : Bool) : StopsEverywhere (leaf decision) 9 := by
  intro input output finish trace
  have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  cases h : output.left with
  | nil =>
    simp [leaf, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
      Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.moveLeft, Tape.write, h] at member
    subst finish
    rfl
  | cons a rest =>
    cases hr : rest with
    | nil =>
      simp [leaf, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
        Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
        Tape.moveLeft, Tape.write, h, hr] at member
      subst finish
      rfl
    | cons b tail =>
      cases b with
      | none =>
        simp [leaf, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
          Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
          Tape.moveLeft, Tape.write, h, hr] at member
        subst finish
        rfl
      | some value =>
        cases value <;>
          simp [leaf, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
            Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
            Tape.moveLeft, Tape.moveRight, Tape.write, h, hr] at member <;>
          subst finish <;> rfl

def decoder : Program := compile 3 (fun bits => leaf (NativeKeyPairObserver.accepts bits))
def code : Program := NativeKeyPairObserver.rewind.followedBy decoder

theorem decoder_stops : StopsEverywhere decoder 18 :=
  NativeBitDecoderTotal.compile_stops_everywhere 3 _ 9 (fun _bits => leaf_stops _)

theorem stops : StopsEverywhere code 29 :=
  NativeUniformSequence.stops NativeKeyPairObserver.rewind decoder 10 18
    NativeKeyPairObserver.rewind_stops decoder_stops

def finish (pc : ℕ) (result : Fin 5 × Bool) : Configuration :=
  {pc := pc,
   inputTape := NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 9 none},
   outputTape := {left := [some (keyPairTest result),some (!result.2)]}, halted := true}

theorem run (oldPc : ℕ) (bit : Bool) (result : Fin 5 × Bool) :
    evalConfigWithin code
      ((NativeCleanRecoverableCoupling.finish oldPc bit result.2 result.1 {} {}).resumeAt 0) 29 =
      PMF.pure (finish (NativeKeyPairObserver.rewind.length + decoder.length + 2) result) := by
  unfold code
  change evalConfigWithin (NativeKeyPairObserver.rewind.followedBy decoder)
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 9 none})
      {left := [some bit,some result.2]}) 29 = _
  rw [NativeUniformSequence.run _ _ 10 18 NativeKeyPairObserver.rewind_stops decoder_stops]
  have hr := NativePrivateHistoryErasure.run [.left,.left,.left]
    (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 9 none})
    {left := [some bit,some result.2]}
  rw [NativeKeyPairObserver.rewind_tape] at hr
  change evalConfigWithin NativeKeyPairObserver.rewind (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 9 none})
      {left := [some bit,some result.2]}) 10 = _ at hr
  rw [hr, PMF.pure_bind]
  change (evalConfigWithin (compile 3 (fun bits => leaf (NativeKeyPairObserver.accepts bits)))
    (NativeBitChoice.start
      (preload (List.ofFn (NativeEightBitCipher.encodeKey result.1)) {left := List.replicate 9 none})
      {left := [some bit,some result.2]}) 18).map _ = _
  rw [compile_run 3 _ 9 (fun bits input output => leaf_stops _ input output),
    NativeKeyPairObserver.after_read_key, leaf_run, PMF.pure_map, PMF.pure_map,
    NativeKeyPairObserver.accepts_encoded]
  rfl

theorem finish_equivalent (pc : ℕ) (result : Fin 5 × Bool) :
    (finish pc result).Equivalent (NativePreparedState.finish pc result) := by
  have h := (NativeAdaptedRecoverableCoupling.blank_left 9).trans
    (NativeAdaptedRecoverableCoupling.blank_left 27).symm
  refine ⟨rfl,rfl,⟨rfl,?_,fun _ => rfl⟩,Tape.Equivalent.refl _⟩
  intro i
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i => exact h.2.1 i

noncomputable def kernelAt (pc : ℕ) : NativePreparedState.State → PMF NativePreparedState.State :=
  Quotient.lift (fun c => (evalConfigWithin code (c.resumeAt 0) 29).map
      (NativeAdaptedRecoverableCoupling.atControl pc)) (by
    intro c d h
    exact evalConfigWithin_map_eq_of_equivalent _ _ _
      (show (c.resumeAt 0).Equivalent (d.resumeAt 0) from ⟨rfl,rfl,h.2.2⟩) 29 _
        (NativeAdaptedRecoverableCoupling.atControl_equivalent pc))

theorem kernelAt_clean (pc oldPc : ℕ) (result : Fin 5 × Bool) :
    kernelAt pc (NativeReferenceCouplingExecution.cleanEncode oldPc result) =
      PMF.pure (NativePreparedState.state (NativePreparedState.finish pc result)) := by
  change (evalConfigWithin code
    ((NativeCleanRecoverableCoupling.finish oldPc (Recoverable.parent result.1) result.2 result.1 {} {}).resumeAt 0) 29).map
      (NativeAdaptedRecoverableCoupling.atControl pc) = _
  rw [run, PMF.pure_map]
  change PMF.pure (NativePreparedState.state (finish pc result)) = _
  rw [NativePreparedState.state_equivalent _ _ (finish_equivalent pc result)]

theorem code_length : code.length ≤ 149 := by
  have hd := compile_length_bound 3 (fun bits => leaf (NativeKeyPairObserver.accepts bits))
    11 (fun bits => by rfl)
  change decoder.length + 6 ≤ (11 + 6) * 2 ^ 3 at hd
  have hr : NativeKeyPairObserver.rewind.length = 16 :=
    NativePrivateHistoryErasure.code_length [.left,.left,.left]
  rw [code, NativeUniformSequence.code_length, hr]
  omega

end Machine.NativeCouplingExitAdapter
