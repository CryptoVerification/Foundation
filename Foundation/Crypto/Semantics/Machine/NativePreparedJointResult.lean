import Foundation.Crypto.Semantics.Machine.NativePreparedInternalResult

/-! Joint public packet and retained labelled result from one execution.
Conditional point masses, not unrelated endpoint marginals, establish their
correlation. Private labels remain an explicit internal-state observation. -/
namespace Machine.NativePreparedJointResult
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

attribute [local irreducible] NativeControlledEightBitCipher.code

abbrev Output := List Bool × Option (Fin 5 × Bool)

def observe (c : Configuration) : Output := (c.outputBits, NativePreparedInternalResult.observe c)

def encode (result : Fin 5 × Bool) : Output := ([!result.2, keyPairTest result], some result)

theorem pair_map_of_pure_views {C A B : Type*} (law : PMF C) (f : C → A) (g : C → B)
    (a : A) (b : B) (hf : law.map f = PMF.pure a) (hg : law.map g = PMF.pure b) :
    law.map (fun c => (f c, g c)) = PMF.pure (a, b) := by
  change (law.bind fun c => PMF.pure (f c, g c)) = _
  calc
    _ = law.bind (fun _ => PMF.pure (a, b)) := by
      apply bind_congr_of_support
      intro c hc
      have hfc : f c ∈ (law.map f).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨c, hc, rfl⟩
      have hgc : g c ∈ (law.map g).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨c, hc, rfl⟩
      rw [hf, PMF.mem_support_pure_iff] at hfc
      rw [hg, PMF.mem_support_pure_iff] at hgc
      rw [hfc, hgc]
    _ = _ := PMF.bind_const _ _

theorem observe_control (c : Configuration) (pc : ℕ) :
    observe {c with pc := pc, halted := true} = observe c := rfl

theorem observe_equivalent (c d : Configuration) (h : c.Equivalent d) : observe c = observe d :=
  Prod.ext h.outputBits (NativePreparedInternalResult.observe_equivalent c d h)

theorem kernel_law (result : Fin 5 × Bool) :
    (NativeCleanCipherContinuation.kernel NativeKeyPairDecisionExecution.caller 30 {} {} result).map observe =
      PMF.pure (encode result) :=
  pair_map_of_pure_views _ Configuration.outputBits NativePreparedInternalResult.observe _ _
    (NativeKeyPairOutputPacket.kernel_packet result) (NativePreparedInternalResult.kernel_law result)

theorem callee_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativeKeyPairDecisionExecution.code (NativeControlledEightBitCipher.entry v message {} {}) 442).map observe =
      (tableEightBitLaw v message).map encode := by
  unfold NativeKeyPairDecisionExecution.code
  rw [NativeCleanCipherContinuation.run _ 30 NativeKeyPairDecisionExecution.caller_stops, PMF.map_bind]
  simp only [kernel_law]
  rfl

theorem source_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativePreparedKeyDecision.source ((NativePreparedKeyDecision.prepared v message).resumeAt 0) 442).map observe =
      (tableEightBitLaw v message).map encode := by
  unfold NativePreparedKeyDecision.source
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativePreparedKeyDecision.handoff v message) 442 _ observe_equivalent]
  exact callee_law v message

theorem framed_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.entry v message) 930).map observe =
      (tableEightBitLaw v message).map encode := by
  unfold NativePreparedKeyDecision.code NativePreparedKeyDecision.entry
  rw [show 930 = 487 + 442 + 1 from rfl,
    NativeUniformSequence.run _ _ _ _ NativePreparedKeyDecision.preparation_stops NativePreparedKeyDecision.source_stops]
  change ((evalConfigWithin NativePreparedKeyDecision.preparation (NativePreparedKeyDecision.entry v message) 487).bind _).map observe = _
  rw [NativePreparedKeyDecision.preparation_run, PMF.pure_bind, PMF.map_comp]
  simp only [Function.comp_def, observe_control]
  exact source_law v message

theorem initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativePreparedKeyDecision.code
      (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 930).map observe =
      (tableEightBitLaw v message).map encode := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativePreparedKeyDecision.entry_equivalent v message).symm
    930 _ observe_equivalent]
  exact framed_law v message

end Machine.NativePreparedJointResult
