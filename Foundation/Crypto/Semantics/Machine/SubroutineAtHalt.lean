import Foundation.Crypto.Semantics.Machine.SubroutineProbability

/-! Return to a known caller halt even when other code precedes it in the suffix. -/
namespace Machine
open Foundation.Probability

theorem Program.evalConfigWithin_withSubroutine_haltAt
    (pre source suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ source.length → pre.length + pc ≠ returnPc)
    (hInstruction : (withSubroutine pre source suffix returnPc)[returnPc]? = some .halt)
    (start : Configuration) (hpc : start.pc ≤ source.length)
    (hactive : start.halted = false) (steps : Nat)
    (halts : ∀ finish, PaddedRunsFor source start finish steps → finish.halted = true) :
    evalConfigWithin (withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) (steps + 1) =
      (evalConfigWithin source start steps).map
        (fun c => { c with pc := returnPc, halted := true }) := by
  let caller := withSubroutine pre source suffix returnPc
  have hReturn := evalReturnWithin_configuration_eq_of_halted pre source suffix
    returnPc hLayout start hpc hactive steps halts
  have hHalted (c : Configuration) (hc : c.halted = true) (extra : Nat) :
      evalConfigWithin caller c extra = PMF.pure c := by
    induction extra with
    | zero => rfl
    | succ extra ih => simp [evalConfigWithin, ih, stepPMF, next, hc]
  have hTail (d : Configuration) (hd : d.pc = returnPc) (extra : Nat) :
      evalConfigWithin caller d (1 + extra) = PMF.pure { d with halted := true } := by
    have hSingle : evalConfigWithin caller d 1 = PMF.pure { d with halted := true } := by
      cases d with
      | mk pc input output active =>
        cases active <;>
          simp_all [caller, evalConfigWithin, stepPMF, next, Instruction.next]
    rw [evalConfigWithin_add, hSingle, PMF.pure_bind]
    exact hHalted _ rfl extra
  have hAfter := evalConfigWithin_after_return caller returnPc (start.rebasePc pre.length)
    steps 1 id (by
      intro d _hd hPc extra
      rw [hTail d hPc extra, hTail d hPc 0])
  simp only [PMF.map_id] at hAfter
  rw [hAfter, hReturn, PMF.bind_map]
  change (evalConfigWithin source start steps).bind _ = _
  simp only [Function.comp_def]
  have hTailReturned (c : Configuration) := hTail (c.resumeAt returnPc) rfl 0
  simp_rw [hTailReturned]
  simp only [Configuration.resumeAt]
  rfl

end Machine
