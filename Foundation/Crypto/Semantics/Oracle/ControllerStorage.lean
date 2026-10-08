import Foundation.Crypto.Semantics.Machine.ControllerStorage
import Foundation.Crypto.Semantics.Oracle.SourceStorage
import Foundation.Crypto.Semantics.Oracle.OneUseInitialization
import Foundation.Crypto.Semantics.FramingStorage

/-! A common retained-data measure for complete private source controllers.
Duplicated saved callers, oracle states, traces, request lists, private stores,
and callback data are charged separately wherever they are retained.
Finite tags, native code, and address encodings are separate resources. -/
namespace CryptoOracle.Interactive.ControllerStorage
open Foundation.Probability TimedExecution
universe u
variable {State : Type u}

def callbackCells (stateSize : State → Nat) : NativeCallback.Control State → Nat
  | .responding component => Machine.ControllerStorage.exportCells component
  | .source frame => SourceStorage.cells stateSize frame

def checkedCells (stateSize : State → Nat) : CheckedCallback.Control State → Nat
  | .preparing preparation => Machine.ControllerStorage.checkCells preparation
  | .computing first second component =>
      first.cells + second.cells + Machine.ControllerStorage.exportCells component
  | .tagging first second packet =>
      first.cells + second.cells + Machine.ControllerStorage.packetCells packet
  | .calling first second callback => first.cells + second.cells + callbackCells stateSize callback

def sourceCells (stateSize : State → Nat) : OneUseSource.Control State → Nat
  | .source _ key frame => key.cells + SourceStorage.cells stateSize frame
  | .handling _ saved state trace request handler =>
      saved.tapeCells + stateSize state + SourceStorage.traceCells trace + request.length +
        checkedCells stateSize handler

/-- During generation the caller remains in the fixed runtime environment.
It is counted until the generated store is transferred to the active source. -/
def initializationCells (stateSize : State → Nat) (caller : Configuration State) :
    OneUseInitialization.Control State → Nat
  | .initializing component =>
      SourceStorage.cells stateSize caller + Machine.ControllerStorage.initializationCells component
  | .active source => sourceCells stateSize source

/-- Native computation inside the callback is framed by both private operands
and the complete suspended caller. Its peak bound needs no scheme-specific proof. -/
theorem computing_peak (stateSize : State → Nat) (native : Machine.Program)
    (first second : Machine.Tape) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : Machine.ResponseExport.Control)
    (h : intermediate ∈ (TimedExecution.eval (Machine.ResponseExport.step native) elapsed start).support)
    (used : Bool) :
    sourceCells stateSize (.handling used saved state trace request (.computing first second intermediate)) ≤
      sourceCells stateSize (.handling used saved state trace request (.computing first second start)) + 2 * horizon := by
  have hb := Machine.ControllerStorage.export_peak native horizon elapsed hElapsed start intermediate h
  simp only [sourceCells, checkedCells]
  omega

theorem preparing_peak (stateSize : State → Nat) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : Machine.PreparationCheck.Control)
    (h : intermediate ∈ (TimedExecution.eval Machine.PreparationCheck.step elapsed start).support) (used : Bool) :
    sourceCells stateSize (.handling used saved state trace request (.preparing intermediate)) ≤
      sourceCells stateSize (.handling used saved state trace request (.preparing start)) + horizon := by
  have hb := Machine.ControllerStorage.check_peak horizon elapsed hElapsed start intermediate h
  simp only [sourceCells, checkedCells]
  omega

/-- Arbitrary real native generators inherit the same peak bound while the
complete caller remains retained. This is the generation/rewind interval. -/
theorem generating_peak (stateSize : State → Nat) (caller : Configuration State)
    (generator : Machine.Program) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : Machine.PrivateInitialization.Control)
    (h : intermediate ∈ (TimedExecution.eval (Machine.PrivateInitialization.step generator) elapsed start).support) :
    initializationCells stateSize caller (.initializing intermediate) ≤
      initializationCells stateSize caller (.initializing start) + horizon := by
  have hb := Machine.ControllerStorage.initialization_peak generator horizon elapsed hElapsed start intermediate h
  simp only [initializationCells]
  omega

end CryptoOracle.Interactive.ControllerStorage
