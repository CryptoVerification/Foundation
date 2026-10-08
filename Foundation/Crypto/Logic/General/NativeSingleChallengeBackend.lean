import Foundation.Crypto.Semantics.Machine.NativeSingleChallengeResources
import Foundation.Crypto.Semantics.Machine.NativeSerializedObservation
import Foundation.Crypto.Logic.General.CountedContractObservedBackend
import Foundation.Crypto.Logic.General.Backends

/-! A reusable operational backend for a raw challenge port followed by
fixed native code. Contexts contain the public input and external reply law.
Goal-specific registrations must constrain these to their intended experiment.
The finite native code is interpreted with the explicit port controller. -/
namespace CryptoLogic.General.NativeSingleChallengeBackend
open Machine Foundation.Probability TimedExecution ContractObservedBackend

structure Context where
  prefixBits : List Bool
  distribution : PMF (List Bool)

noncomputable def runtime : Runtime Backends.system .native where
  Context := Context
  State := NativeSingleChallenge.Control
  step := fun code context => NativeSingleChallenge.step context.distribution code
  initial := fun _ context => NativeSingleChallenge.initial context.prefixBits
  terminal := fun _ _ => NativeSingleChallenge.terminal
  absorb := fun code context => NativeSingleChallenge.absorbing context.distribution code
  observe := fun _ _ => NativeSingleChallenge.Execution.result NativeSerializedObservation.decision

def event (_ : Program) (_ : Context) := NativeSingleChallenge.queryEvent

def measure (code : Program) (_ : Context) (state : NativeSingleChallenge.Control) : Nat :=
  (NativeSingleChallenge.Resources.completeEncoding.encode (code, state)).length

end CryptoLogic.General.NativeSingleChallengeBackend
