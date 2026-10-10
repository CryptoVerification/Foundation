import Foundation.Constructions.Hash.SimulatorInvariant

/-! The full sampling order and the simulator's public exposure order differ.
This is a counterexample to bounding the private `ForwardFresh` failure by a
birthday estimate, not a distinguisher breaking prefix-free Merkle–Damgård.
The invariant remains valid as a conditional statement, but its premise need
not hold with high probability in the ideal world. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest : Type} [DecidableEq Payload] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

local instance : BEq (List Payload) := instBEqOfDecidableEq

/-- Learn an empty-message hash, use its output as an orphan data input, then
expose the terminal compression entry which was responsible for that hash. -/
def privateOrderAttack (initial : Digest) (terminal block : Payload) :
    Program (WorldInput Payload Digest) Digest Unit :=
  .query (.inl []) (fun hash =>
    .query (.inr (hash, (false, block))) (fun _ =>
      .query (.inr (initial, (true, terminal))) (fun _ => .done ())))


omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- The counterexample uses three public calls and only an empty hash input. -/
theorem privateOrder_bound (initial : Digest) (terminal block : Payload) :
    WorldBound 1 (privateOrderAttack initial terminal block) 3 := by
  exact .hash [] _ 2 (by simp) (fun _ =>
    .compression _ _ 1 (by decide) (fun _ =>
      .compression _ _ 0 (by decide) (fun _ => .done () 0)))

/-- Exact law of the actual candidate simulator with the shared ideal hash. -/
theorem privateOrder_run (initial : Digest) (terminal block : Payload) :
    (privateOrderAttack initial terminal block).run
      (idealWorld RandomOracle.oracle initial terminal) ([], []) =
    (uniform Digest).bind (fun hash =>
      (uniform Digest).map (fun orphan =>
        (⟨(),
          ([((initial, (true, terminal)), hash), ((hash, (false, block)), orphan)], [([], hash)]),
          [(.inl [], hash), (.inr (hash, (false, block)), orphan),
            (.inr (initial, (true, terminal)), hash)]⟩ :
          Outcome (WorldInput Payload Digest) Digest Unit
            (CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest)))) := by
  have different (hash : Digest) :
      (((initial, (true, terminal)) : CompressionInput Payload Digest) ==
        (hash, (false, block))) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have marker := congrArg (fun input : CompressionInput Payload Digest => input.2.1) he
    cases marker
  simp [privateOrderAttack, Program.run, idealWorld, compressionSimulator_eq,
    RandomOracle.oracle, messagePrefix, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, PMF.pure_map, Function.comp_def, List.lookup_cons, different]
  rfl

/-- The terminal output equals an older exposed input state by construction.
No rare collision or hidden-value guess is needed for this private-order failure. -/
theorem privateOrder_failure (initial : Digest) (terminal block : Payload) :
    eventProb ((privateOrderAttack initial terminal block).run
      (idealWorld RandomOracle.oracle initial terminal) ([], []))
      (fun out => ¬ForwardFresh initial out.state.1) = 1 := by
  rw [privateOrder_run]
  have he := eventProb_congr_of_support
    ((uniform Digest).bind (fun hash =>
      (uniform Digest).map (fun orphan =>
        (⟨(),
          ([((initial, (true, terminal)), hash), ((hash, (false, block)), orphan)], [([], hash)]),
          [(.inl [], hash), (.inr (hash, (false, block)), orphan),
            (.inr (initial, (true, terminal)), hash)]⟩ :
          Outcome (WorldInput Payload Digest) Digest Unit
            (CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest)))))
    (event := fun out => ¬ForwardFresh initial out.state.1) (other := fun _ => True)
    (by
      intro out support
      rw [PMF.mem_support_bind_iff] at support
      obtain ⟨hash, _, support⟩ := support
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨orphan, _, rfl⟩ := support
      simp [ForwardFresh, RandomOracle.Avoided, graphForbidden])
  rw [he]
  have all (law : PMF (Outcome (WorldInput Payload Digest) Digest Unit
      (CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest))) :
      eventProb law (fun _ => True) = 1 := by
    unfold eventProb
    rw [PMF.toOuterMeasure_apply]
    simp only [Set.ofPred_true, Set.indicator_univ, PMF.tsum_coe]
  exact all _

end Foundation.Hash
