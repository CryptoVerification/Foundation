import Foundation.Constructions.Hash.CoordinateAllocation
import Foundation.Constructions.Hash.LatentPublicTerminal

/-! Exhaustive one-call correspondence for the actual coordinate worlds.
The common premises are explicit induction obligations. This theorem unifies
all query cases; it does not assume their responses agree, and it does not yet
establish these premises at every prefix of a coupled execution. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest]
  [DecidableEq Label] [Fintype Digest] [Nonempty Digest] [Fintype Label]

local instance : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq
local instance : BEq ((Digest ⊕ Label) × Payload) := instBEqOfDecidableEq
local instance : BEq Label := instBEqOfDecidableEq

/-- Every actual outer query preserves data-table correspondence and supply
agreement and returns equal responses under the common good-state obligations.
A genuine next real proof record retains public paths and the no-guess flag.
The capacity counts data blocks for a hash call and one possible allocation for
a public compression call. No time or encoded-memory bound follows from it. -/
theorem coordinate_pair_step
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (injective : Function.Injective function) (avoid : ∀ label, function label ≠ initial)
    (hashFunction : List Payload → Digest)
    (real : TrackedRealState Payload Digest) (state : LatentState Payload Digest Label)
    (publicSame : real.exposed = state.exposed) (publicConsistent : PublicConsistent real)
    (paths : ExposedPaths initial real) (hiddenComplete : HiddenTerminalsComplete initial terminal real)
    (beforeGood : ForwardFresh initial real.full)
    (relation : LatentDataRelation function real.full state)
    (consistent : RandomOracle.TableConsistent real.full)
    (allocation : state.AllocationValid) (freshSupply : state.FreshSupply)
    (unique : state.ChildrenUnique) (values : RandomOracle.TableValues function state.revealed)
    (separate : state.LiteralAvoids function) (noOverflow : state.overflow = false)
    (realHashes idealHashes : RandomOracle.Table (List Payload) Digest)
    (realCoordinates : RandomOracle.Table Label Digest) (flag : Bool)
    (privateFresh : ∀ label ∈ state.supply, realCoordinates.lookup label = none)
    (covered : TerminalConsistent initial terminal real.full realHashes)
    (realValues : RandomOracle.TableValues hashFunction realHashes)
    (idealValues : RandomOracle.TableValues hashFunction idealHashes)
    (notGuessed : real.guessed = false)
    (request : WorldInput Payload Digest)
    (noHit : latentGuessHit function (state, (idealHashes, state.revealed)) request = false)
    (capacity : (match request with | .inl message => message.length | .inr _ => 1) ≤ state.supply.length)
    (realAnswer : CoordinateRealState Payload Digest Label × Digest)
    (idealAnswer : LatentWorldState Payload Digest Label × Digest)
    (realSupport : realAnswer ∈ (coordinateRealWorld initial terminal (RandomOracle.eager function)
      (RandomOracle.eager hashFunction) (real.full, ((state.supply, flag), (realHashes, realCoordinates))) request).support)
    (idealSupport : idealAnswer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      (RandomOracle.eager hashFunction) (state, (idealHashes, state.revealed)) request).support)
    (afterGood : ForwardFresh initial realAnswer.1.1) :
    realAnswer.2 = idealAnswer.2 ∧
    LatentDataRelation function realAnswer.1.1 idealAnswer.1.1 ∧
    realAnswer.1.2.1.1 = idealAnswer.1.1.supply ∧
    ∃ trackedAnswer : TrackedRealState Payload Digest × Digest,
      trackedAnswer ∈ (trackedRealWorld initial terminal real request).support ∧
      (trackedAnswer.1.full, trackedAnswer.2) = (realAnswer.1.1, realAnswer.2) ∧
      trackedAnswer.1.exposed = idealAnswer.1.1.exposed ∧
      PublicConsistent trackedAnswer.1 ∧ HiddenTerminalsComplete initial terminal trackedAnswer.1 ∧
      trackedAnswer.1.guessed = false ∧ ExposedPaths initial trackedAnswer.1 := by
  have paired :
    realAnswer.2 = idealAnswer.2 ∧
    LatentDataRelation function realAnswer.1.1 idealAnswer.1.1 ∧
    realAnswer.1.2.1.1 = idealAnswer.1.1.supply := by
    cases request with
    | inl message =>
        have paired := coordinate_high_pair initial terminal function injective avoid hashFunction message state real.full
          realHashes idealHashes realCoordinates state.revealed flag relation consistent allocation freshSupply separate
          privateFresh noOverflow capacity covered realValues idealValues realAnswer idealAnswer realSupport idealSupport afterGood
        exact ⟨paired.1, paired.2.1, paired.2.2.1⟩
    | inr input =>
        have noGuess := latentGuessHit_no_guess function (state, (idealHashes, state.revealed)) input noHit
        cases known : state.exposed.lookup input with
        | some output =>
            have paired := coordinate_public_known_pair initial terminal function real state publicSame publicConsistent
              relation realHashes idealHashes realCoordinates state.revealed flag (RandomOracle.eager hashFunction)
              input output known realAnswer idealAnswer realSupport idealSupport
            exact ⟨paired.1, paired.2.1, paired.2.2.1⟩
        | none =>
            have nonempty : state.supply ≠ [] := by
              intro empty
              simp only [empty, List.length_nil] at capacity
              omega
            rcases input with ⟨value, marker, block⟩
            cases marker with
            | false =>
                cases edge : state.graph.lookup (latentParent initial state value, block) with
                | some child =>
                    have paired := coordinate_pending_data_pair initial terminal function state real.full relation consistent
                      allocation unique values realHashes idealHashes realCoordinates flag (RandomOracle.eager hashFunction)
                      value block child edge known realAnswer idealAnswer realSupport idealSupport
                    exact ⟨paired.1, paired.2.1, paired.2.2.1⟩
                | none =>
                    cases supply : state.supply with
                    | nil => exact False.elim (nonempty supply)
                    | cons child rest =>
                        have fresh := privateFresh child (by rw [supply]; exact List.mem_cons_self)
                        have paired := coordinate_fresh_data_pair initial terminal function injective avoid state real.full
                          relation consistent allocation unique freshSupply values realHashes idealHashes realCoordinates flag
                          (RandomOracle.eager hashFunction) value block child rest supply fresh known edge noGuess
                          (separate.stable initial values) realAnswer idealAnswer realSupport idealSupport
                        exact ⟨paired.1, paired.2.1, paired.2.2.1⟩
            | true =>
                cases recognized : terminalMessage initial terminal state.exposed (value, (true, block)) with
                | some message =>
                    have paired := coordinate_recognized_terminal_pair initial terminal function hashFunction real state
                      publicSame publicConsistent paths beforeGood relation consistent realHashes idealHashes realCoordinates
                      state.revealed flag covered realValues idealValues (value, (true, block)) message known recognized
                      noGuess realAnswer idealAnswer realSupport idealSupport
                    exact ⟨paired.1, paired.2.1, paired.2.2.1⟩
                | none =>
                    cases supply : state.supply with
                    | nil => exact False.elim (nonempty supply)
                    | cons child rest =>
                        have fresh := privateFresh child (by rw [supply]; exact List.mem_cons_self)
                        have paired := coordinate_orphan_terminal_pair initial terminal function real state publicSame
                          publicConsistent paths beforeGood hiddenComplete relation consistent allocation freshSupply
                          realHashes idealHashes realCoordinates flag (RandomOracle.eager hashFunction) value block child rest
                          supply fresh known recognized noGuess realAnswer idealAnswer realSupport idealSupport
                        exact ⟨paired.1, paired.2.1, paired.2.2.1⟩
  have witness := coordinate_paired_tracked_step initial terminal function
    (RandomOracle.eager function) (RandomOracle.eager function)
    (RandomOracle.eager hashFunction) (RandomOracle.eager hashFunction)
    real (real.full, ((state.supply, flag), (realHashes, realCoordinates)))
    (state, (idealHashes, state.revealed)) rfl publicSame relation publicConsistent paths hiddenComplete
    notGuessed request noHit realAnswer idealAnswer realSupport idealSupport paired.1 afterGood
  exact ⟨paired.1, paired.2.1, paired.2.2, witness⟩

end Foundation.Hash
