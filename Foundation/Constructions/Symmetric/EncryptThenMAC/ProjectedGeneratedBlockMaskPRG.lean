import Foundation.Constructions.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask
import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMaskPRG

/-! PRG implementation interface with private internal generator results.
The cryptographic real distribution is the projected output marginal; retained
seed/scratch state remains in the native physical contract and its costs. -/
namespace Foundation.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask.PRG
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open scoped ENNReal
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} {Result : Type w} (G : Generator) (n : Nat)
    (P : Machine.Procedure Input Result) (key : Result → Bits (G.outputLength n))
    (hHalt : ∀ input result, (P.execution.exit input result).halted = true)
    (hTape : ∀ input result, (P.execution.exit input result).outputTape = ResponseExport.endTape (key result).toList)
    (read : Input → Machine.Configuration → Result)
    (hRead : ∀ input result, read input (P.execution.exit input result) = result)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (input : Input) (hReal : (P.execution.semantics input).map key = G.real n)

include hHalt hTape hRead hReal in
theorem ciphertext_eq (message : Bits (G.outputLength n)) (horizon : Nat)
    (hTime : P.execution.budget input + 50 * G.outputLength n + 39 ≤ horizon) :
    ProjectedGeneratedBlockMask.ciphertext P oracle state trace message input horizon =
      (G.ciphertext n message).map Bits.toList := by
  rw [ProjectedGeneratedBlockMask.ciphertext_eq P key hHalt hTape read hRead oracle state trace message input horizon hTime,
    Generator.ciphertext, ← hReal, PMF.map_comp, PMF.map_comp]
  congr 1
  funext result
  exact congrArg Bits.toList (Bits.xor_comm (key result) message)

include hHalt hTape hRead hReal in
theorem advantage_le (messages : G.Messages n) (leftTime rightTime : Nat)
    (hLeft : P.execution.budget input + 50 * G.outputLength n + 39 ≤ leftTime)
    (hRight : P.execution.budget input + 50 * G.outputLength n + 39 ≤ rightTime)
    (observer : List Bool → PMF Bool) :
    probabilityGap
      (eventProb ((ProjectedGeneratedBlockMask.ciphertext P oracle state trace messages.1 input leftTime).bind observer) (· = true))
      (eventProb ((ProjectedGeneratedBlockMask.ciphertext P oracle state trace messages.2 input rightTime).bind observer) (· = true)) ≤
    G.prgGoal.advantage n messages (G.reduce messages false (fun ciphertext => observer ciphertext.toList)) +
      G.prgGoal.advantage n messages (G.reduce messages true (fun ciphertext => observer ciphertext.toList)) := by
  rw [ciphertext_eq G n P key hHalt hTape read hRead oracle state trace input hReal messages.1 leftTime hLeft,
    ciphertext_eq G n P key hHalt hTape read hRead oracle state trace input hReal messages.2 rightTime hRight,
    PMF.bind_map, PMF.bind_map]
  exact G.advantage_le n messages (fun ciphertext => observer ciphertext.toList)

/-- Uniform finite implementation with private outcomes distinct from keys.
Only exported keys must realize the PRG real distribution. -/
structure Implementation (G : Generator) where
  Input : Nat → Type v
  Result : Nat → Type w
  code : Machine.Program
  execution : ∀ n, TimedExecution.Procedure (stepPMF code) (Input n) (Result n)
  key : ∀ n, Result n → Bits (G.outputLength n)
  halt : ∀ n input result, ((execution n).exit input result).halted = true
  tape : ∀ n input result, ((execution n).exit input result).outputTape = ResponseExport.endTape (key n result).toList
  read : ∀ n, Input n → Machine.Configuration → Result n
  read_exit : ∀ n input result, read n input ((execution n).exit input result) = result
  implements : ∀ n input, ((execution n).semantics input).map (key n) = G.real n

namespace Implementation
variable {G : Generator} (I : Implementation.{v,w} G)

def native (n : Nat) : Machine.Procedure (I.Input n) (I.Result n) := ⟨I.code, I.execution n⟩

theorem native_code (n : Nat) : (I.native n).code = I.code := rfl

theorem ciphertext_eq (n : Nat) (input : I.Input n) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (message : Bits (G.outputLength n)) (horizon : Nat)
    (hTime : (I.execution n).budget input + 50 * G.outputLength n + 39 ≤ horizon) :
    ProjectedGeneratedBlockMask.ciphertext (I.native n) oracle state trace message input horizon =
      (G.ciphertext n message).map Bits.toList :=
  PRG.ciphertext_eq G n (I.native n) (I.key n) (I.halt n) (I.tape n) (I.read n) (I.read_exit n)
    oracle state trace input (I.implements n input) message horizon hTime

/-- Existing direct-output implementations are the identity-projection case. -/
def ofDirect (I : GeneratedBlockMask.PRG.Implementation.{v} G) : Implementation G where
  Input := I.Input
  Result := fun n => Bits (G.outputLength n)
  code := I.code
  execution := I.execution
  key := fun _ => id
  halt := I.halt
  tape := I.tape
  read := I.read
  read_exit := I.read_exit
  implements := fun n input => by simpa only [PMF.map_id] using I.implements n input

theorem ofDirect_code (I : GeneratedBlockMask.PRG.Implementation.{v} G) : (ofDirect I).code = I.code := rfl

end Implementation
end Foundation.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask.PRG
