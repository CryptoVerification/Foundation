import Foundation.Crypto.Semantics.Machine.TapeEquivalence

/-! Native execution preserves exact output layout when inputs describe the
same cells but retain different outer blank representations. This is a proof
about the original transitions; it does not normalize any tape at runtime. -/
namespace Machine
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

namespace Configuration
def SameOutput (c d : Configuration) : Prop :=
  c.pc = d.pc ∧ c.halted = d.halted ∧
    c.inputTape.Equivalent d.inputTape ∧ c.outputTape = d.outputTape

namespace SameOutput
theorem equivalent {c d : Configuration} (h : c.SameOutput d) : c.Equivalent d :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 ▸ Tape.Equivalent.refl _⟩

theorem updateTape {c d : Configuration} (h : c.SameOutput d)
    (tape : TapeId) (f : Tape → Tape)
    (hf : ∀ t s, t.Equivalent s → (f t).Equivalent (f s)) :
    (c.updateTape tape f).SameOutput (d.updateTape tape f) := by
  cases tape
  · exact ⟨h.1, h.2.1, hf _ _ h.2.2.1, h.2.2.2⟩
  · exact ⟨h.1, h.2.1, h.2.2.1, congrArg f h.2.2.2⟩

theorem advance {c d : Configuration} (h : c.SameOutput d) : c.advance.SameOutput d.advance :=
  ⟨congrArg (· + 1) h.1, h.2⟩

theorem withPc {c d : Configuration} (h : c.SameOutput d) (pc : Nat) :
    ({ c with pc := pc } : Configuration).SameOutput { d with pc := pc } := ⟨rfl, h.2⟩

theorem withHalted {c d : Configuration} (h : c.SameOutput d) (halted : Bool) :
    ({ c with halted := halted } : Configuration).SameOutput { d with halted := halted } :=
  ⟨h.1, rfl, h.2.2⟩
end SameOutput
end Configuration

theorem stepPMF_bind_eq_of_sameOutput {α : Type*} (p : Program)
    (c d : Configuration) (h : c.SameOutput d) (k : Configuration → PMF α)
    (hk : ∀ c d, c.SameOutput d → k c = k d) :
    (stepPMF p c).bind k = (stepPMF p d).bind k := by
  by_cases hHalt : c.halted = true
  · have hd : d.halted = true := h.2.1.symm.trans hHalt
    simpa [stepPMF, next, hHalt, hd] using hk c d h
  · have hc : c.halted = false := by cases hh : c.halted <;> simp_all
    have hd : d.halted = false := h.2.1.symm.trans hc
    cases hInstr : p[c.pc]? with
    | none =>
        have hOther : p[d.pc]? = none := by simpa [← h.1] using hInstr
        simpa [stepPMF, next, hc, hd, hInstr, hOther] using hk _ _ (h.withHalted true)
    | some instr =>
        have hOther : p[d.pc]? = some instr := by simpa [← h.1] using hInstr
        have hUpdate (tape : TapeId) (f : Tape → Tape)
            (hf : ∀ t s, t.Equivalent s → (f t).Equivalent (f s)) :
            k ((c.updateTape tape f).advance) = k ((d.updateTape tape f).advance) :=
          hk _ _ ((h.updateTape tape f hf).advance)
        cases instr with
        | halt =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using hk _ _ (h.withHalted true)
        | jump pc =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using hk _ _ (h.withPc pc)
        | moveLeft tape =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using
              hUpdate tape Tape.moveLeft (fun _ _ ht => ht.moveLeft)
        | moveRight tape =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using
              hUpdate tape Tape.moveRight (fun _ _ ht => ht.moveRight)
        | write tape bit =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using
              hUpdate tape (fun t => t.write (some bit)) (fun _ _ ht => ht.write _)
        | erase tape =>
            simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next] using
              hUpdate tape (fun t => t.write none) (fun _ _ ht => ht.write _)
        | branch tape blankPc zeroPc onePc =>
            have hCell := (h.equivalent.tape tape).1
            cases hCurrent : (c.tape tape).current with
            | none =>
                simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next, ← hCell, hCurrent] using
                  hk _ _ (h.withPc blankPc)
            | some bit =>
                cases bit <;>
                  simpa [stepPMF, next, hc, hd, hInstr, hOther, Instruction.next, ← hCell, hCurrent] using
                    hk _ _ (h.withPc _)
        | randomBit tape =>
            simp only [stepPMF, next, hc, hd, Bool.false_eq_true, ↓reduceIte,
              hInstr, hOther, Instruction.next, PMF.bind_map, Function.comp_def]
            congr 1
            funext bit
            cases bit <;> exact hUpdate tape _ (fun _ _ ht => ht.write _)

/-- Equality retains the output head and every explicitly represented output
cell, as well as any other observation invariant under input-cell equivalence. -/
theorem evalConfigWithin_map_eq_of_sameOutput {α : Type*} (p : Program)
    (c d : Configuration) (h : c.SameOutput d) (steps : Nat)
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.SameOutput d → observe c = observe d) :
    (evalConfigWithin p c steps).map observe = (evalConfigWithin p d steps).map observe := by
  induction steps generalizing c d with
  | zero => simp [evalConfigWithin, PMF.pure_map, hObserve c d h]
  | succ steps ih =>
      rw [evalConfigWithin_succ_head, evalConfigWithin_succ_head, PMF.map_bind, PMF.map_bind]
      exact stepPMF_bind_eq_of_sameOutput p c d h _ (fun c d h => ih c d h)

end Machine
