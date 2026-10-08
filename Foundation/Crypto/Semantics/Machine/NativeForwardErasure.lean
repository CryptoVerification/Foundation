import Foundation.Crypto.Semantics.Machine.NativeFixedComponent
import Foundation.Crypto.Semantics.Machine.TapeSwapProcedure
import Foundation.Crypto.Semantics.Machine.TapeEquivalence

/-! Erase a contiguous block from its first cell through its last bit.
Stop at the following blank. Saved cells on both sides and the other tape
are retained exactly; represented blank cells are never normalized away. -/
namespace Machine.NativeForwardErasure
open Foundation.Probability TimedExecution

def code : Program :=
  [.branch .input 4 1 1, .erase .input, .moveRight .input, .jump 0, .halt]

structure Input where
  bits : List Bool
  before : List (Option Bool) := []
  after : List (Option Bool) := []
  other : Tape

def initial (input : Input) : Configuration :=
  { inputTape := {
      left := input.before,
      current := (input.bits.map some ++ none :: input.after).headD none,
      right := (input.bits.map some ++ none :: input.after).tail},
    outputTape := input.other }

def finish (input : Input) : Configuration :=
  { pc := 4, inputTape := {
      left := List.replicate input.bits.length none ++ input.before,
      right := input.after}, outputTape := input.other, halted := true }

theorem run (input : Input) :
    evalConfigWithin code (initial input) (4 * input.bits.length + 2) = PMF.pure (finish input) := by
  rcases input with ⟨bits, before, after, other⟩
  induction bits generalizing before with
  | nil =>
      simp [initial, finish, code, evalConfigWithin, stepPMF, Machine.next,
        Instruction.next, Configuration.tape]
  | cons bit bits ih =>
      let rest : Input := ⟨bits, none :: before, after, other⟩
      have cell : evalConfigWithin code (initial ⟨bit :: bits, before, after, other⟩) 4 =
          PMF.pure (initial rest) := by
        cases bit <;> cases bits <;>
          simp [initial, rest, code, evalConfigWithin, stepPMF, Machine.next,
            Instruction.next, Configuration.tape, Configuration.updateTape,
            Configuration.advance, Tape.write, Tape.moveRight]
      rw [show 4 * (bit :: bits).length + 2 = 4 + (4 * bits.length + 2) by simp; omega,
        evalConfigWithin_add, cell, PMF.pure_bind]
      change evalConfigWithin code (initial ⟨bits, none :: before, after, other⟩) _ = _
      rw [ih]
      simp [finish, List.replicate_succ', List.append_assoc]

noncomputable def component : NativeComponent Input Configuration :=
  NativeComponent.ofFixed code initial (fun _ output => output)
    (fun input => PMF.pure (finish input)) (fun input => 4 * input.bits.length + 2)
    (fun input => by simpa only [PMF.pure_map] using run input)
    (by decide) (fun _ => by change 0 < 5; decide) (fun _ => rfl)
    (by
      intro input output h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)

noncomputable def outputComponent : NativeComponent Input Configuration := component.swapTapes

theorem budget (input : Input) : component.procedure.execution.budget input = 4 * input.bits.length + 2 := rfl

theorem saved_other (input : Input) : (finish input).outputTape = input.other := rfl

theorem erased_cells (input : Input) : (finish input).inputTape =
    {left := List.replicate input.bits.length none ++ input.before, right := input.after} := rfl

def bitBound (size : Nat) : Nat :=
  NativeEncodedResources.bound code 0 (size + 1) (4 * size + 2)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))
    (((PolynomiallyBounded.const 4).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 2))

theorem initial_cells (input : Input) : (initial input).tapeCells =
    input.bits.length + input.before.length + input.after.length + input.other.cells + 1 := by
  cases h : input.bits <;> simp [initial, h, Configuration.tapeCells, Tape.cells] <;> omega

theorem storage_peak (input : Input) (elapsed : Nat)
    (hElapsed : elapsed ≤ 4 * input.bits.length + 2) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF code) elapsed (initial input)).support) :
    (NativeEncodedResources.completeEncoding.encode (code, target)).length ≤
      bitBound (input.bits.length + input.before.length + input.after.length + input.other.cells) := by
  have h := NativeEncodedResources.peak code _ elapsed hElapsed _ target hTarget
  exact h.trans (NativeEncodedResources.bound_mono _ (Nat.le_refl 0)
    (by rw [initial_cells]) (by omega))

end Machine.NativeForwardErasure
