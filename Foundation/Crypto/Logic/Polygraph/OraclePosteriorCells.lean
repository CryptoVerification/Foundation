import Foundation.Crypto.Logic.Polygraph.OracleLocalEdits
import Foundation.Crypto.Semantics.Oracle.PosteriorCoupling

/-! A common realization of a mixed square: elementary history/cache proof
editing horizontally, and eager/lazy sampling with different hidden state
types vertically. The whole finite function is retained in the witness.
Reconstructing it independently is not identified with retaining it.
This construction uses the endpoint soundness of edits; it is not a proof
that higher cells are necessary or that ordinary lemma sharing is weaker.
-/
namespace CryptoOracle.ProofEdits.PosteriorCells
open Foundation.Probability CryptoOracle.RandomOracle
open CryptoOracle.RandomOracle.Posterior
set_option backward.isDefEq.respectTransparency false
variable {Input Tag Result : Type} [DecidableEq Input]
  [Fintype Input] [Fintype Tag] [Nonempty Tag]

structure Corners (Input Tag Result : Type) where
  eagerBefore : Outcome Input Tag (Result × List Input) (Input → Tag)
  lazyBefore : Outcome Input Tag (Result × List Input) (Table Input Tag)
  eagerAfter : Outcome Input Tag (Result × List Input) (Input → Tag)
  lazyAfter : Outcome Input Tag (Result × List Input) (Table Input Tag)

def corners (pair : Outcome Input Tag (Result × List Input) (Input → Tag) ×
    Outcome Input Tag (Result × List Input) (Table Input Tag)) : Corners Input Tag Result :=
  ⟨pair.1, pair.2, pair.1, pair.2⟩

/-- Only a syntactic edit with no initial cache facts is accepted here.
There is no constructor accepting a whole-program semantic equality. -/
noncomputable def joint {p q : Command Input Tag Result} (_edit : LocalEdit [] p q)
    (signed : List Input) : PMF (Corners Input Tag Result) :=
  (completionJoint (p.compile signed)).map corners

theorem completion_eq {p q : Command Input Tag Result} (edit : LocalEdit [] p q)
    (signed : List Input) :
    completionJoint (p.compile signed) = completionJoint (q.compile signed) := by
  have same := edit.sound oracle lazy_cache_laws signed [] (knows_nil [])
  change (p.compile signed).run oracle [] = (q.compile signed).run oracle [] at same
  simp only [completionJoint, retained]
  rw [same]

theorem eager_before {p q : Command Input Tag Result} (edit : LocalEdit [] p q)
    (signed : List Input) :
    (joint edit signed).map Corners.eagerBefore =
      (uniform (Input → Tag)).bind (fun function =>
        (p.compile signed).run functionOracle function) := by
  simpa only [joint, PMF.map_comp, Function.comp_def, corners] using
    completion_left (p.compile signed)

theorem lazy_before {p q : Command Input Tag Result} (edit : LocalEdit [] p q)
    (signed : List Input) :
    (joint edit signed).map Corners.lazyBefore = p.run oracle signed [] := by
  simpa only [joint, PMF.map_comp, Function.comp_def, corners, Command.run] using
    completion_right (p.compile signed)

theorem eager_after {p q : Command Input Tag Result} (edit : LocalEdit [] p q)
    (signed : List Input) :
    (joint edit signed).map Corners.eagerAfter =
      (uniform (Input → Tag)).bind (fun function =>
        (q.compile signed).run functionOracle function) := by
  simp only [joint, PMF.map_comp, Function.comp_def, corners]
  rw [completion_eq edit signed]
  exact completion_left _

theorem lazy_after {p q : Command Input Tag Result} (edit : LocalEdit [] p q)
    (signed : List Input) :
    (joint edit signed).map Corners.lazyAfter = q.run oracle signed [] := by
  simp only [joint, PMF.map_comp, Function.comp_def, corners]
  rw [completion_eq edit signed]
  exact completion_right _

/-- Both transformation orders preserve the very same function and the
complete history, including the order of repeated requests and responses. -/
theorem compatible {p q : Command Input Tag Result} (edit : LocalEdit [] p q)
    (signed : List Input) (square : Corners Input Tag Result)
    (supported : square ∈ (joint edit signed).support) :
    square.eagerBefore = square.eagerAfter ∧ square.lazyBefore = square.lazyAfter ∧
      square.eagerBefore.result = square.lazyBefore.result ∧
      square.eagerBefore.trace = square.lazyBefore.trace ∧
      ∀ input tag, square.lazyBefore.state.lookup input = some tag →
        square.eagerBefore.state input = tag := by
  rw [joint, PMF.mem_support_map_iff] at supported
  obtain ⟨pair, reachable, rfl⟩ := supported
  obtain ⟨result, trace, cache⟩ := completion_related (p.compile signed) pair reachable
  exact ⟨rfl, rfl, result, trace, cache⟩

/-- The present common realization depends only on the endpoints. Thus this
theorem does not yet use a higher comparison between the two edit witnesses. -/
theorem same_endpoints {p q : Command Input Tag Result} (first second : LocalEdit [] p q)
    (signed : List Input) : joint first signed = joint second signed := rfl

end CryptoOracle.ProofEdits.PosteriorCells
