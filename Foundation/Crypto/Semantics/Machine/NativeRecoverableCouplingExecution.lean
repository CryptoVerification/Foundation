import Foundation.Crypto.Semantics.Machine.NativeRecoverableKeyObserver
import Foundation.Crypto.Semantics.Machine.NativePreparedInternalResult

/-! One continuing native execution samples the repaired key then calls a
native observer that recovers the source bit. The joint view retains the
sampled private key, ciphertext and written recovery bit. This does not assert
that the entire configuration equals a canonical reference-cipher exit. -/
namespace Machine.NativeRecoverableCouplingExecution
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def code : Program := NativeRecoverableKeySampler.code.followedBy NativeRecoverableKeyObserver.code

def read (c : Configuration) : Option Bool := c.outputTape.left.getD 0 none

def keyCiphertext (c : Configuration) : Option (Fin 5 × Bool) :=
  NativeEightBitCipher.observe (NativePreparedInternalResult.withoutDecision c)

def observe (c : Configuration) : Option (Fin 5 × Bool) × Option Bool := (keyCiphertext c,read c)

def history (bit ciphertext : Bool) (inputSuffix : Tape) (coins : Fin 7 → Bool) : Tape :=
  afterRead (List.ofFn coins) (afterRead (NativeRecoverableKeySampler.rawInput bit ciphertext) inputSuffix)

def finish (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) (coins : Fin 7 → Bool) : Configuration :=
  let before := NativeRecoverableKeySampler.finish bit ciphertext inputSuffix outputSuffix coins
  {pc := NativeRecoverableKeySampler.code.length + NativeRecoverableKeyObserver.code.length + 2, inputTape := before.inputTape,
    outputTape := (before.outputTape.write (some bit)).moveRight, halted := true}

theorem sampler_resume (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) (coins : Fin 7 → Bool) :
    (NativeRecoverableKeySampler.finish bit ciphertext inputSuffix outputSuffix coins).resumeAt 0 =
      NativeBitChoice.start
        (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey (RecoverableSampler.sample bit coins))
          (history bit ciphertext inputSuffix coins))
        {outputSuffix with left := some ciphertext :: outputSuffix.left} := by
  rw [NativeRecoverableKeySampler.finish, NativeRecoverableKeySampler.finishControl_resume]
  rfl

theorem full_run (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin code (NativeRecoverableKeySampler.entry bit ciphertext inputSuffix outputSuffix) 111 =
      (uniform (Fin 7 → Bool)).map (finish bit ciphertext inputSuffix outputSuffix) := by
  unfold code NativeRecoverableKeySampler.entry
  rw [show 111 = 87 + 23 + 1 from rfl,
    NativeUniformSequence.run _ _ 87 23 NativeRecoverableKeySampler.stops NativeRecoverableKeyObserver.stops]
  change (evalConfigWithin NativeRecoverableKeySampler.code (NativeRecoverableKeySampler.entry bit ciphertext inputSuffix outputSuffix) 87).bind _ = _
  rw [NativeRecoverableKeySampler.full_run, PMF.bind_map]
  simp only [Function.comp_def, sampler_resume, NativeRecoverableKeyObserver.run, PMF.pure_map,
    NativeRecoverableKeyObserver.accepts_encoded, RecoverableSampler.sample_parent]
  rfl

theorem written_left (t : Tape) (bit : Bool) : (t.write (some bit)).moveRight.left = some bit :: t.left := by
  cases h : t.right <;> simp [Tape.write, Tape.moveRight, h]

theorem read_finish (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) (coins : Fin 7 → Bool) :
    read (finish bit ciphertext inputSuffix outputSuffix coins) = some bit := by
  simp only [read, finish, written_left, List.getD_cons_zero]

theorem observe_by_left (c d : Configuration) (input : c.inputTape.left = d.inputTape.left)
    (output : c.outputTape.left = d.outputTape.left) : NativeEightBitCipher.observe c = NativeEightBitCipher.observe d := by
  unfold NativeEightBitCipher.observe NativeRandomPrivateResult.observe
  rw [input, output]

theorem keyCiphertext_finish (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) (coins : Fin 7 → Bool) :
    keyCiphertext (finish bit ciphertext inputSuffix outputSuffix coins) =
      some (RecoverableSampler.sample bit coins,ciphertext) := by
  rw [keyCiphertext]
  trans NativeEightBitCipher.observe (NativeRecoverableKeySampler.finish bit ciphertext inputSuffix outputSuffix coins)
  · apply observe_by_left
    · rfl
    · change ((NativeRecoverableKeySampler.finish bit ciphertext inputSuffix outputSuffix coins).outputTape.write
        (some bit)).moveRight.left.drop 1 = _
      rw [written_left]
      rfl
  · exact NativeRecoverableKeySampler.observe_finish bit ciphertext inputSuffix outputSuffix coins

theorem observe_equivalent (c d : Configuration) (h : c.Equivalent d) : observe c = observe d := by
  apply Prod.ext
  · exact NativeControlledCipherInitial.observe_equivalent _ _ (NativePreparedInternalResult.withoutDecision_equivalent c d h)
  · exact h.2.2.2.2.1 0

theorem framed_law (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin code (NativeRecoverableKeySampler.entry bit ciphertext inputSuffix outputSuffix) 111).map observe =
      (Recoverable.forward bit).map (fun key => (some (key,ciphertext),some bit)) := by
  rw [full_run, PMF.map_comp]
  have h : observe ∘ finish bit ciphertext inputSuffix outputSuffix =
      (fun key => (some (key,ciphertext),some bit)) ∘ RecoverableSampler.sample bit := by
    funext coins
    exact Prod.ext (keyCiphertext_finish bit ciphertext inputSuffix outputSuffix coins)
      (read_finish bit ciphertext inputSuffix outputSuffix coins)
  rw [h, ← PMF.map_comp, RecoverableSampler.sample_law]

theorem initial_law (bit ciphertext : Bool) :
    (evalConfigWithin code (Configuration.initial (NativeRecoverableKeySampler.rawInput bit ciphertext)) 111).map observe =
      (Recoverable.forward bit).map (fun key => (some (key,ciphertext),some bit)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativeRecoverableKeySampler.entry_equivalent bit ciphertext).symm
    111 _ observe_equivalent]
  exact framed_law bit ciphertext {} {}

theorem recovered_bit (bit ciphertext : Bool) :
    (evalConfigWithin code (Configuration.initial (NativeRecoverableKeySampler.rawInput bit ciphertext)) 111).map read =
      PMF.pure (some bit) := by
  have h := congrArg (fun law => law.map Prod.snd) (initial_law bit ciphertext)
  rw [PMF.map_comp, PMF.map_comp] at h
  change (evalConfigWithin code (Configuration.initial (NativeRecoverableKeySampler.rawInput bit ciphertext)) 111).map read =
    (Recoverable.forward bit).map (Function.const (Fin 5) (some bit)) at h
  simpa only [PMF.map_const] using h

theorem stops : StopsEverywhere code 111 :=
  NativeUniformSequence.stops NativeRecoverableKeySampler.code NativeRecoverableKeyObserver.code 87 23 NativeRecoverableKeySampler.stops NativeRecoverableKeyObserver.stops

theorem haltsWithin (input : List Bool) : HaltsWithin code input 111 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 111
  polynomial := PolynomiallyBounded.const 111
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

theorem code_length : code.length ≤ 8086 := by
  have hs := NativeRecoverableKeySampler.code_length
  have ho := NativeRecoverableKeyObserver.code_length
  rw [code, NativeUniformSequence.code_length]
  omega

end Machine.NativeRecoverableCouplingExecution
