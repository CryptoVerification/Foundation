import Foundation.Crypto.Semantics.Machine.RankedFamilyResources

/-! Add independently verified functional invariants to ranked code without
reproving termination. The full state/time law and represented storage bound
are unchanged. These are proof transformations, not machine instructions. -/
namespace Machine.Program.Ranking

def restrict {code : Program} {first second : Program.Assertions}
    (ranking : Program.Ranking first code)
    (implies : ∀ machine, second.Holds machine → first.Holds machine) :
    Program.Ranking second code where
  rank := ranking.rank
  instruction := fun pc start hPc hActive h =>
    ranking.instruction pc start hPc hActive (implies start h)

end Machine.Program.Ranking

namespace Machine.Program.RankedFamily
open Foundation.Probability TimedExecution
universe u
variable {code : Program} {Input : Type u} (F : Program.RankedFamily code Input)

def enrich (extra : Input → Program.Assertions)
    (verified : ∀ input, (extra input).Verified code)
    (initial : ∀ input, (extra input).Holds (F.entry input)) : Program.RankedFamily code Input where
  assertions := fun input => (F.assertions input).inter (extra input)
  verified := fun input => (F.verified input).inter (verified input)
  ranking := fun input => (F.ranking input).restrict (fun machine h =>
    ((Program.Assertions.holds_inter _ _ machine).mp h).1)
  entry := F.entry
  valid := fun input => (Program.Assertions.holds_inter _ _ _).mpr ⟨F.valid input, initial input⟩

variable (extra : Input → Program.Assertions)
    (verified : ∀ input, (extra input).Verified code)
    (initial : ∀ input, (extra input).Holds (F.entry input))

theorem enrich_entry (input : Input) : (F.enrich extra verified initial).entry input = F.entry input := rfl

theorem enrich_budget (input : Input) :
    (F.enrich extra verified initial).execution.budget input = F.execution.budget input := rfl

theorem enrich_costed (input : Input) :
    (F.enrich extra verified initial).execution.costed input = F.execution.costed input := by
  rw [(F.enrich extra verified initial).costed, F.costed]
  rfl

theorem enrich_semantics (input : Input) :
    (F.enrich extra verified initial).execution.semantics input = F.execution.semantics input := by
  rw [← (F.enrich extra verified initial).execution.correct input, ← F.execution.correct input,
    F.enrich_costed extra verified initial input]

theorem enrich_bitBound (input : Input) :
    (F.enrich extra verified initial).bitBound input = F.bitBound input := rfl

include verified initial in
/-- The new invariant holds at supported endpoints of the original family,
so existing clients need not switch to a new runtime contract. -/
theorem extra_postcondition (input : Input) (target : Configuration)
    (hTarget : target ∈ (F.execution.semantics input).support) :
    (extra input).stopped target.pc target.inputTape target.outputTape := by
  rw [← F.enrich_semantics extra verified initial input] at hTarget
  exact ((F.enrich extra verified initial).stopped input target hTarget).2

end Machine.Program.RankedFamily
