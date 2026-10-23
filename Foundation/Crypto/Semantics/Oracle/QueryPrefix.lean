import Foundation.Crypto.Semantics.Oracle.RepresentationLocality
import Foundation.Crypto.Semantics.Oracle.Composition

/-! Extract a real execution prefix and retain its exact remaining program.
No oracle response, local coin already drawn, hidden cache, or ordered prefix
trace is reconstructed from an independently sampled copy. -/
namespace CryptoOracle.Program
open Foundation.Probability
variable {Request Response Result State : Type}

def pauseAfter : Nat → Program Request Response Result →
    Program Request Response (Program Request Response Result)
  | 0, program => .done program
  | _ + 1, .done result => .done (.done result)
  | count + 1, .coin next => .coin fun bit => pauseAfter (count + 1) (next bit)
  | count + 1, .query request next => .query request fun response => pauseAfter count (next response)

theorem pauseAfter_resume (count : Nat) (program : Program Request Response Result) :
    (pauseAfter count program).bind id = program := by
  induction program generalizing count with
  | done result => cases count <;> rfl
  | coin next ih =>
      cases count with
      | zero => rfl
      | succ count => simp only [pauseAfter, bind]; congr 1; funext bit; exact ih bit (count + 1)
  | query request next ih =>
      cases count with
      | zero => rfl
      | succ count => simp only [pauseAfter, bind]; congr 1; funext response; exact ih response count

theorem pauseAfter_continuation (count : Nat) (program : Program Request Response Result)
    (world : Oracle Request Response State) (state : State) :
    ((pauseAfter count program).run world state).bind (fun past =>
      (past.result.run world past.state).map (fun last => {last with trace := past.trace ++ last.trace})) =
      program.run world state := by
  have law := run_bind (pauseAfter count program) id world state
  rw [pauseAfter_resume] at law
  exact law.symm

theorem pauseAfter_bounded (count : Nat) (program : Program Request Response Result) :
    (pauseAfter count program).BoundedQueries count := by
  induction program generalizing count with
  | done result => cases count <;> exact .done _ _
  | coin next ih =>
      cases count with
      | zero => exact .done _ _
      | succ count => exact .coin _ _ (fun bit => ih bit (count + 1))
  | query request next ih =>
      cases count with
      | zero => exact .done _ _
      | succ count => exact .query _ _ _ (fun response => ih response count)

variable [DecidableEq Request] [Fintype Response]

theorem pauseAfter_footprintAt (count position : Nat) (program : Program Request Response Result) :
    footprintAt position (pauseAfter count program) =
      if position < count then footprintAt position program else ∅ := by
  induction program generalizing count position with
  | done result => cases count <;> simp [pauseAfter, footprintAt]
  | coin next ih =>
      cases count with
      | zero => simp [pauseAfter, footprintAt]
      | succ count =>
          simp only [pauseAfter, footprintAt, ih]
          split <;> simp
  | query request next ih =>
      cases count with
      | zero => simp [pauseAfter, footprintAt]
      | succ count =>
          cases position with
          | zero => simp [pauseAfter, footprintAt]
          | succ position =>
              simp only [pauseAfter, footprintAt, ih, Nat.succ_lt_succ_iff]
              by_cases small : position < count
              · simp only [if_pos small]
              · simp only [if_neg small]
                ext input
                simp

theorem pauseAfter_unaffected (count : Nat) (program : Program Request Response Result)
    (changed : Finset Request) (unaffected : affectedPositions changed count program = []) :
    Disjoint (pauseAfter count program).footprint changed := by
  apply Finset.disjoint_left.mpr
  intro request reachable patched
  obtain ⟨position, small, member⟩ := ((pauseAfter_bounded count program).footprint_positions request).mp reachable
  rw [pauseAfter_footprintAt, if_pos small] at member
  have affected := (affectedPositions_mem changed count position program).mpr ⟨small, request, member, patched⟩
  rw [unaffected] at affected
  exact List.not_mem_nil affected

/-- This preserves the actual suspended continuation and prefix state. The
two suffixes may still differ when an affected later query is resumed. -/
theorem pauseAfter_representation_patch {Stored : Type} [Nonempty Response]
    (left right : Request → Response ≃ Stored) (changed : Finset Request)
    (agree : ∀ request ∉ changed, left request = right request)
    (count : Nat) (program : Program Request Response Result)
    (unaffected : affectedPositions changed count program = []) (saved : RandomOracle.Table Request Stored) :
    (pauseAfter count program).run (RandomOracle.Representation.oracle left) saved =
      (pauseAfter count program).run (RandomOracle.Representation.oracle right) saved :=
  RandomOracle.Representation.run_unaffected_patch left right changed agree (pauseAfter count program)
    (pauseAfter_unaffected count program changed unaffected) saved

end CryptoOracle.Program
