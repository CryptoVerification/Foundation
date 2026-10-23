import Foundation.Examples.RandomFunctionMACRepairGame
import Foundation.Examples.RandomFunctionMACNativeBackendSecurity

/-! Observable connection of repaired full game correspondences to the
existing native ideal execution. Time is not part of gameView; this does not
construct a joint of physical configurations or their elapsed times. -/
namespace Foundation.Symmetric.RandomFunctionMACRepairNative
open Foundation.Probability Foundation.Probability.SelectedCouplingGraph
open CryptoOracle CryptoOracle.Interactive
open Foundation.Hash.Native CompactMACExecution
open scoped ENNReal
open RandomFunctionMACPosterior RandomFunctionMACCouplingRepair RandomFunctionMACRepairGame
set_option backward.isDefEq.respectTransparency false

variable {Vertex Edge State Source : Type} (G : Graph Vertex Edge)
    (oracle : BitOracle State) (callerOracle : BitOracle Source)
    (serverState : State) (callerState : Source)

include G in
/-- Every repaired vertex's complete rendered observation has exactly the
law of the same native caller/backend execution within its existing horizon. -/
theorem vertex_physical_observation (potential : SigningOutcome → Vertex → Bool) (vertex : Vertex) :
    (games potential).map (fun pair =>
      renderGame (Program.mapState encodeTable (pair.2 vertex))) =
    (TimedExecution.eval (CompactMACRound.step oracle callerOracle) 2091
      (.source (NativeCode.frame serverState [] RandomFunctionMACNativeCaller.NativeBackend.emptyMachine)
        ⟨callerState, .running {}, []⟩)).map gameView := by
  have law := congrArg (fun p => p.map (renderGame ∘ Program.mapState encodeTable))
    (vertex_game_law G potential vertex)
  simp only [PMF.map_comp, Function.comp_def] at law
  exact law.trans (RandomFunctionMACNativeCaller.NativeBackend.ideal_game_observation
    oracle callerOracle serverState callerState).symm

include G oracle callerOracle serverState callerState in
/-- The repaired vertex also inherits the already verified ideal success
bound; the repair does not introduce a new cryptographic bound. -/
theorem vertex_security (potential : SigningOutcome → Vertex → Bool) (vertex : Vertex) :
    eventProb ((games potential).map (fun pair => pair.2 vertex))
      (fun out => out.result = true) ≤ (256 : ℝ≥0∞)⁻¹ := by
  rw [vertex_game_law G]
  have law := RandomFunctionMACNativeCaller.NativeBackend.idealGame_eq_lazy
    oracle callerOracle serverState callerState
  have bound := RandomFunctionMACNativeCaller.NativeBackend.ideal_security
    oracle callerOracle serverState callerState
  rw [law, eventProb_map] at bound
  exact bound

end Foundation.Symmetric.RandomFunctionMACRepairNative
