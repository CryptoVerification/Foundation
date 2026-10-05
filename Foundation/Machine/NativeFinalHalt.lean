import Foundation.Machine.ClosedSubroutineProbability
import Foundation.Machine.ConfigurationExpectation

namespace Machine

private def report (c : Configuration) : Option (List Bool) :=
  if c.halted then some c.outputBits else none

private theorem halt_at_return (pre source : Program) (c : Configuration)
    (hpc : c.pc = pre.length+source.length+1) (extra : Nat) :
    evalConfigWithin (Program.withSubroutine pre source [.halt]
      (pre.length+source.length+1)) c (1+extra) = PMF.pure {c with halted := true} := by
  have lookup : (Program.withSubroutine pre source [.halt]
      (pre.length+source.length+1))[c.pc]? = some .halt := by
    rw [hpc]
    simpa using Program.withSubroutine_getElem?_suffix pre source [.halt]
      (pre.length+source.length+1) 0
  have first : stepPMF (Program.withSubroutine pre source [.halt]
      (pre.length+source.length+1)) c = PMF.pure {c with halted := true} := by
    cases hh : c.halted
    · simp [stepPMF, next, hh, lookup, Instruction.next]
    · have same : {c with halted := true} = c := by cases c; simp_all
      simp [stepPMF, next, hh, same]
  have rest : evalConfigWithin (Program.withSubroutine pre source [.halt]
      (pre.length+source.length+1)) {c with halted := true} extra =
      PMF.pure {c with halted := true} := by
    induction extra with
    | zero => rfl
    | succ extra ih => simp [evalConfigWithin, ih, stepPMF, next]
  rw [show 1+extra = extra+1 by omega, evalConfigWithin_succ_head, first, PMF.pure_bind, rest]

/-- A native call followed by a charged halt reports every returned output
with its full probability. Active source branches keep running; no common
finite stopping bound is imposed on the random source. -/
theorem Program.report_after_closed_call (pre source : Program)
    (start : Configuration) (hpc : start.pc < source.length)
    (hActive : start.halted = false)
    (closed : ∀ c d, c.pc < source.length → Step source c d →
      d.halted = false → d.pc < source.length) (steps : Nat) :
    (evalConfigWithin (withSubroutine pre source [.halt] (pre.length+source.length+1))
      (start.rebasePc pre.length) (steps+1)).map report =
      (evalConfigWithin source start steps).bind (fun c =>
        (evalConfigWithin (withSubroutine pre source [.halt] (pre.length+source.length+1))
          (if c.halted then c.resumeAt (pre.length+source.length+1)
            else c.rebasePc pre.length) 1).map report) := by
  have stable (d : Configuration) (_ : d ∈ (evalReturnWithin
      (withSubroutine pre source [.halt] (pre.length+source.length+1))
      (pre.length+source.length+1) (start.rebasePc pre.length) steps).support)
      (h : d.pc = pre.length+source.length+1) (extra : Nat) :
      (evalConfigWithin (withSubroutine pre source [.halt] (pre.length+source.length+1))
        d (1+extra)).map report =
      (evalConfigWithin (withSubroutine pre source [.halt] (pre.length+source.length+1))
        d 1).map report := by
    rw [halt_at_return pre source d h extra,
      show (1 : Nat) = 1+0 by rfl, halt_at_return pre source d h 0]
  rw [evalConfigWithin_after_return _ _ _ steps 1 report stable,
    evalReturnWithin_configuration_eq_of_closed pre source [.halt] _
      (by intro pc hp; omega) closed start hpc hActive steps, PMF.bind_map]
  rfl

/-- One charged caller halt adds at most one step to the source timeout
tail, including for sources with unbounded rejection retries. -/
theorem Program.timeout_after_closed_call_le (pre source : Program)
    (start : Configuration) (hpc : start.pc < source.length)
    (hActive : start.halted = false)
    (closed : ∀ c d, c.pc < source.length → Step source c d →
      d.halted = false → d.pc < source.length) (steps : Nat) :
    timeoutProbabilityFrom (withSubroutine pre source [.halt] (pre.length+source.length+1))
      (start.rebasePc pre.length) (steps+1) ≤ timeoutProbabilityFrom source start steps := by
  classical
  unfold timeoutProbabilityFrom
  change ((evalConfigWithin _ _ (steps+1)).map report) none ≤
    ((evalConfigWithin source start steps).map report) none
  rw [report_after_closed_call pre source start hpc hActive closed steps,
    PMF.bind_apply, PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro c
  cases hh : c.halted with
  | false =>
    simp only [report, hh, Bool.false_eq_true, ↓reduceIte, ite_true]
    exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
  | true =>
    simp only [hh, ↓reduceIte]
    rw [show (1 : Nat) = 1+0 by rfl,
      halt_at_return pre source (c.resumeAt _) rfl 0, PMF.pure_map]
    simp [report, hh]

theorem Program.output_after_closed_call_le (pre source : Program)
    (start : Configuration) (hpc : start.pc < source.length)
    (hActive : start.halted = false)
    (closed : ∀ c d, c.pc < source.length → Step source c d →
      d.halted = false → d.pc < source.length) (steps : Nat) (bits : List Bool) :
    ((evalConfigWithin source start steps).map report) (some bits) ≤
      ((evalConfigWithin (withSubroutine pre source [.halt] (pre.length+source.length+1))
        (start.rebasePc pre.length) (steps+1)).map report) (some bits) := by
  classical
  rw [report_after_closed_call pre source start hpc hActive closed steps,
    PMF.bind_apply, PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro c
  cases hh : c.halted with
  | false => simp [report, hh]
  | true =>
    simp only [hh, ↓reduceIte]
    rw [show (1 : Nat) = 1+0 by rfl,
      halt_at_return pre source (c.resumeAt _) rfl 0, PMF.pure_map]
    simp [report, hh, Configuration.resumeAt, Configuration.outputBits]

end Machine
