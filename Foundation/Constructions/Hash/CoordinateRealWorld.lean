import Foundation.Constructions.Hash.RealCoordinates

/-! The finite-coordinate real experiment at the original two-window interface.
Internal compression calls remain hidden from the attacker. The existing
expansion/inlining theorems connect its full state and result to the already
verified compiled experiment. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

abbrev CoordinateRealState (Payload Digest Label : Type) :=
  CompressionTable Payload Digest × RealCoordinateState Payload Digest Label

/-- The same real hash computation and public compression interface, with all
internal compression queries handled by the full-table procedure. Only that
procedure's local draws are allocated coordinates. -/
noncomputable def coordinateRealWorld (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    Oracle (WorldInput Payload Digest) Digest (CoordinateRealState Payload Digest Label) :=
  Program.implementedOracle (compressionCall initial terminal)
    (Program.statefulOracle (simulatorProgram initial terminal) (realCoordinateWorld coordinates hashOracle))

omit [DecidableEq Label] in
/-- The public compression window is exactly the existing full-table
procedure, including its complete backend state. No internal hash expansion
is needed for this branch of the outer interface. -/
theorem coordinate_real_public_execution (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : CoordinateRealState Payload Digest Label) (input : CompressionInput Payload Digest) :
    coordinateRealWorld initial terminal coordinates hashOracle state (.inr input) =
      Program.statefulOracle (simulatorProgram initial terminal)
        (realCoordinateWorld coordinates hashOracle) state input := by
  simp [coordinateRealWorld, Program.implementedOracle, compressionCall, Program.run,
    PMF.map_bind, PMF.pure_map, Program.resultState]

omit [DecidableEq Label] in
/-- Both nested stateful inlinings and the hash expansion preserve the full
real state (compression, supply, hash cache, coordinate cache) jointly with
attacker result. It is an equality for any coordinate kernel. -/
theorem coordinate_real_compiled {Result : Type} (initial : Digest) (terminal : Payload)
    (supply : List Label) (attack : Program (WorldInput Payload Digest) Digest Result)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashes : RandomOracle.Table (List Payload) Digest) (table : RandomOracle.Table Label Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    ((realCoordinateCompiled supply (factoredRealCompiled initial terminal attack)).run
      (RandomOracle.withContext (simulatorBackend hashOracle) coordinates) (hashes, table)).map
        (fun out => ((out.result.2.1, (out.result.1, out.state)), out.result.2.2)) =
      (attack.run (coordinateRealWorld initial terminal coordinates hashOracle)
        ([], ((supply, false), (hashes, table)))).map Program.resultState := by
  have allocator := congrArg (PMF.map (fun pair =>
      ((pair.2.2.1, (pair.2.1, pair.1)), pair.2.2.2)))
    (real_coordinate_inline supply (factoredRealCompiled initial terminal attack) coordinates hashes table hashOracle)
  have simulator := congrArg (PMF.map (fun pair => ((pair.2.1, pair.1), pair.2.2)))
    (Program.inlineState_run (simulatorProgram initial terminal) (expand initial terminal attack)
      (realCoordinateWorld coordinates hashOracle) [] ((supply, false), (hashes, table)))
  have outer := Program.inline_run (compressionCall initial terminal) attack
    (Program.statefulOracle (simulatorProgram initial terminal) (realCoordinateWorld coordinates hashOracle))
    ([], ((supply, false), (hashes, table)))
  simp only [PMF.map_comp, Program.resultState, Function.comp_def, Prod.mk.eta] at allocator simulator
  exact allocator.trans (simulator.trans outer)

/-- At the original attacker interface, integrating a finite eager coordinate
function recovers the actual real result and final compression table exactly.
No claim about equality to the ideal world's distribution is made here. -/
theorem coordinate_real_eager_marginal [Fintype Label] {Result : Type}
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup)
    (attack : Program (WorldInput Payload Digest) Digest Result) :
    (uniform (Label → Digest)).bind (fun function =>
      (attack.run (coordinateRealWorld initial terminal (RandomOracle.eager function))
        ([], ((supply, false), ([], [])))).map (fun out => (out.state.1, out.result))) =
      (attack.run (realWorld initial terminal) []).map Program.resultState := by
  have same (function : Label → Digest) := congrArg (PMF.map (fun pair => (pair.1.1, pair.2)))
    (coordinate_real_compiled initial terminal supply attack (RandomOracle.eager function) [] [])
  simp only [PMF.map_comp, Program.resultState, Function.comp_def] at same
  simp_rw [← same]
  exact real_coordinate_real_marginal supply nodup initial terminal attack

/-- Capacity is now stated on actual outcomes at the original attacker's
interface, for every fixed coordinate function. -/
theorem coordinate_real_fin_capacity {Result : Type} {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (function : Fin (q * blockLimit) → Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result
      (CoordinateRealState Payload Digest (Fin (q * blockLimit))))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal (RandomOracle.eager function))
      ([], ((List.finRange (q * blockLimit), false), ([], [])))).support) :
    out.state.2.1.2 = false := by
  have mapped : Program.resultState out ∈ ((attack.run
      (coordinateRealWorld initial terminal (RandomOracle.eager function))
      ([], ((List.finRange (q * blockLimit), false), ([], [])))).map Program.resultState).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨out, support, rfl⟩
  rw [← coordinate_real_compiled, PMF.mem_support_map_iff] at mapped
  obtain ⟨compiledOut, reachable, same⟩ := mapped
  have flag := real_coordinate_fin_capacity bound initial terminal function compiledOut reachable
  have supplySame : compiledOut.result.1 = out.state.2.1 := congrArg (fun pair => pair.1.2.1) same
  rwa [supplySame] at flag

end Foundation.Hash
