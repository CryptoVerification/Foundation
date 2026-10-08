import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityCallback

/-! Native encryption-key sampling and ownership transfer into the actual
integrity controller. Initialization preserves the independent source tapes.
The third transition transfers the generated private key; it does not sample
another coin or start the source early. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

def initialized (state : State) (input : List Bool) (key : Bool) : Frame State :=
  ⟨state, .source key false (.running (Configuration.initial input)), [], []⟩

def afterCoin (state : State) (input : List Bool) (key : Bool) : Frame State :=
  ⟨state, .initializing (.running (Configuration.initial input))
    { pc := 1, outputTape := { current := some key } }, [], []⟩

theorem initial_step (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (state : State) (input : List Bool) :
    step code oracle (initial state input) = sampleBit.map (afterCoin state input) := by
  change sampleBit.map (fun bit => if bit then afterCoin state input true else afterCoin state input false) = _
  congr 1
  funext bit
  cases bit <;> rfl

theorem afterCoin_run (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (state : State) (input : List Bool) (key : Bool) :
    eval code oracle 2 (afterCoin state input key) = PMF.pure (initialized state input key) := by
  cases key <;> simp [eval, TimedExecution.eval, step, transition, nativeAction,
    afterCoin, initialized, next, OneBitEncryption.Native.keygenCode,
    Instruction.next]

theorem initialization_run (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (state : State) (input : List Bool) :
    eval code oracle 3 (initial state input) = sampleBit.map (initialized state input) := by
  rw [eval_succ, initial_step, PMF.bind_map]
  simp only [Function.comp_def]
  simp_rw [afterCoin_run]
  simpa only [Function.comp_def] using PMF.bind_pure_comp (initialized state input) sampleBit

theorem initialization_continue (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (state : State) (input : List Bool) (extra : Nat) :
    eval code oracle (3 + extra) (initial state input) =
      sampleBit.bind (fun key => eval code oracle extra (initialized state input key)) := by
  rw [eval_add, initialization_run, PMF.bind_map]
  rfl

noncomputable def initializationBlock (code : SourceCode)
    (oracle : State → Bool → PMF (State × List Bool)) (state : State) (input : List Bool) :
    TimedExecution.Block (step code oracle) (initial state input) :=
  TimedExecution.Block.fixed (step code oracle) 3 _

theorem initializationBlock_outcome (code : SourceCode)
    (oracle : State → Bool → PMF (State × List Bool)) (state : State) (input : List Bool) :
    (initializationBlock code oracle state input).outcome =
      sampleBit.map (fun key => (initialized state input key, 3)) := by
  change (eval code oracle 3 (initial state input)).map _ = _
  rw [initialization_run, PMF.map_comp]
  rfl

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
