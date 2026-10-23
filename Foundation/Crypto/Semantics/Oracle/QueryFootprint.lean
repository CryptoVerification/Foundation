import Foundation.Crypto.Semantics.Oracle.StateMap

/-! Finite syntactic query effects, extracted from every response branch.
These are conservative sets, independent of the chosen oracle or probabilities.
The extractor can enumerate response branches; no polynomial cost is claimed. -/
namespace CryptoOracle.Program
open Foundation.Probability
variable {Request Response Result State : Type} [DecidableEq Request] [Fintype Response]

def footprint : Program Request Response Result → Finset Request
  | .done _ => ∅
  | .coin next => footprint (next false) ∪ footprint (next true)
  | .query request next => insert request (Finset.univ.biUnion fun response => footprint (next response))

/-- Requests at a zero-based query position. Local coins do not consume a
position; every syntactic response is considered, including impossible ones. -/
def footprintAt : Nat → Program Request Response Result → Finset Request
  | _, .done _ => ∅
  | position, .coin next => footprintAt position (next false) ∪ footprintAt position (next true)
  | 0, .query request _ => {request}
  | position + 1, .query _ next => Finset.univ.biUnion fun response => footprintAt position (next response)

theorem continuation_subset (request : Request) (next : Response → Program Request Response Result)
    (response : Response) : footprint (next response) ⊆ footprint (.query request next) := by
  intro input member
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨response, Finset.mem_univ _, member⟩)

theorem footprintAt_subset (position : Nat) (program : Program Request Response Result) :
    footprintAt position program ⊆ footprint program := by
  induction program generalizing position with
  | done result => simp [footprintAt]
  | coin next ih =>
      intro input member
      rcases Finset.mem_union.mp member with left | right
      · exact Finset.mem_union_left _ (ih false position left)
      · exact Finset.mem_union_right _ (ih true position right)
  | query request next ih =>
      cases position with
      | zero => simp [footprintAt, footprint]
      | succ position =>
          intro input member
          obtain ⟨response, _, reachable⟩ := Finset.mem_biUnion.mp member
          exact continuation_subset request next response (ih response position reachable)

/-- The bound certifies that the finite position list covers all syntactic
queries. It is not inferred by running any particular oracle. -/
theorem BoundedQueries.footprint_positions {program : Program Request Response Result} {bound : Nat}
    (bounded : program.BoundedQueries bound) (input : Request) :
    input ∈ footprint program ↔ ∃ position < bound, input ∈ footprintAt position program := by
  induction bounded with
  | done result q => simp [footprint, footprintAt]
  | coin next q h ih =>
      simp only [footprint, footprintAt, Finset.mem_union]
      constructor
      · rintro (left | right)
        · obtain ⟨position, small, member⟩ := (ih false).mp left
          exact ⟨position, small, Or.inl member⟩
        · obtain ⟨position, small, member⟩ := (ih true).mp right
          exact ⟨position, small, Or.inr member⟩
      · rintro ⟨position, small, left | right⟩
        · exact Or.inl ((ih false).mpr ⟨position, small, left⟩)
        · exact Or.inr ((ih true).mpr ⟨position, small, right⟩)
  | query request next q h ih =>
      constructor
      · intro member
        rcases Finset.mem_insert.mp member with same | later
        · exact ⟨0, Nat.zero_lt_succ _, by simp [footprintAt, same]⟩
        · obtain ⟨response, _, member⟩ := Finset.mem_biUnion.mp later
          obtain ⟨position, small, member⟩ := (ih response).mp member
          exact ⟨position + 1, Nat.succ_lt_succ small,
            Finset.mem_biUnion.mpr ⟨response, Finset.mem_univ _, member⟩⟩
      · rintro ⟨position, small, member⟩
        cases position with
        | zero =>
            have same : input = request := by simpa [footprintAt] using member
            simp [footprint, same]
        | succ position =>
            obtain ⟨response, _, member⟩ := Finset.mem_biUnion.mp member
            exact continuation_subset request next response
              ((ih response).mpr ⟨position, Nat.lt_of_succ_lt_succ small, member⟩)

theorem footprint_trace (program : Program Request Response Result) (world : Oracle Request Response State)
    (state : State) (out : Outcome Request Response Result State)
    (supported : out ∈ (program.run world state).support) :
    ∀ entry ∈ out.trace, entry.1 ∈ footprint program := by
  induction program generalizing state out with
  | done result =>
      simp only [run, PMF.mem_support_pure_iff] at supported
      subst out
      simp
  | coin next ih =>
      rw [run, PMF.mem_support_bind_iff] at supported
      obtain ⟨bit, _, tail⟩ := supported
      intro entry member
      have inner := ih bit state out tail entry member
      cases bit with
      | false => exact Finset.mem_union_left _ inner
      | true => exact Finset.mem_union_right _ inner
  | query request next ih =>
      rw [run, PMF.mem_support_bind_iff] at supported
      obtain ⟨answer, _, tail⟩ := supported
      rw [PMF.mem_support_map_iff] at tail
      obtain ⟨last, reachable, rfl⟩ := tail
      intro entry member
      rcases List.mem_cons.mp member with same | later
      · subst entry; exact Finset.mem_insert_self _ _
      · exact continuation_subset request next answer.2 (ih answer.2 answer.1 last reachable entry later)

/-- Equal local kernels only on extracted requests suffice for equality of
the COMPLETE outcome: result, final hidden state, and ordered transcript. -/
theorem run_congr_on_footprint (program : Program Request Response Result)
    (left right : Oracle Request Response State)
    (agree : ∀ request ∈ footprint program, ∀ state, left state request = right state request)
    (state : State) : program.run left state = program.run right state := by
  induction program generalizing state with
  | done result => rfl
  | coin next ih =>
      simp only [run]
      congr 1
      funext bit
      apply ih bit
      intro request member state
      apply agree request
      cases bit with
      | false => exact Finset.mem_union_left _ member
      | true => exact Finset.mem_union_right _ member
  | query request next ih =>
      simp only [run, agree request (Finset.mem_insert_self _ _) state]
      congr 1
      funext answer
      rw [ih answer.2 (fun input member => agree input (continuation_subset request next answer.2 member))]

def affectedPositions (changed : Finset Request) (bound : Nat) (program : Program Request Response Result) : List Nat :=
  (List.range bound).filter fun position => !(Disjoint (footprintAt position program) changed)

theorem affectedPositions_mem (changed : Finset Request) (bound position : Nat)
    (program : Program Request Response Result) :
    position ∈ affectedPositions changed bound program ↔
      position < bound ∧ ∃ request ∈ footprintAt position program, request ∈ changed := by
  simp [affectedPositions, Finset.disjoint_left]

theorem BoundedQueries.unaffected_iff {program : Program Request Response Result} {bound : Nat}
    (bounded : program.BoundedQueries bound) (changed : Finset Request) :
    Disjoint program.footprint changed ↔ affectedPositions changed bound program = [] := by
  constructor
  · intro disjoint
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro position member
    obtain ⟨_, request, reachable, patched⟩ := (affectedPositions_mem changed bound position program).mp member
    exact Finset.disjoint_left.mp disjoint (footprintAt_subset position program reachable) patched
  · intro empty
    apply Finset.disjoint_left.mpr
    intro request reachable patched
    obtain ⟨position, small, member⟩ := (bounded.footprint_positions request).mp reachable
    have affected := (affectedPositions_mem changed bound position program).mpr ⟨small, request, member, patched⟩
    rw [empty] at affected
    exact List.not_mem_nil affected

end CryptoOracle.Program
