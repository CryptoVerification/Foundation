import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMask

/-! Reuse the real generated-mask execution for PRG-based encryption. The
native generator's execution law must implement the PRG real distribution;
the PRG's distinguishing bounds remain explicit cryptographic premises. -/
namespace Foundation.Symmetric.EncryptThenMAC.GeneratedBlockMask.PRG
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open scoped ENNReal
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} (G : Generator) (n : Nat)
    (P : Machine.Procedure Input (Bits (G.outputLength n)))
    (hHalt : ∀ input key, (P.execution.exit input key).halted = true)
    (hTape : ∀ input key, (P.execution.exit input key).outputTape = ResponseExport.endTape key.toList)
    (read : Input → Machine.Configuration → Bits (G.outputLength n))
    (hRead : ∀ input key, read input (P.execution.exit input key) = key)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (input : Input) (hReal : P.execution.semantics input = G.real n)

include hHalt hTape hRead hReal in
theorem ciphertext_eq (message : Bits (G.outputLength n)) (horizon : Nat)
    (hTime : P.execution.budget input + 50 * G.outputLength n + 39 ≤ horizon) :
    GeneratedBlockMask.ciphertext P oracle state trace message input horizon =
      (G.ciphertext n message).map Bits.toList := by
  rw [GeneratedBlockMask.ciphertext_eq P hHalt hTape read hRead oracle state trace message input horizon hTime,
    hReal, Generator.ciphertext, PMF.map_comp]
  congr 1
  funext key
  exact congrArg Bits.toList (Bits.xor_comm key message)

include hHalt hTape hRead hReal in
theorem observer_eq (message : Bits (G.outputLength n)) (horizon : Nat)
    (hTime : P.execution.budget input + 50 * G.outputLength n + 39 ≤ horizon)
    (observer : List Bool → PMF Bool) :
    (GeneratedBlockMask.ciphertext P oracle state trace message input horizon).bind observer =
      (G.ciphertext n message).bind (fun ciphertext => observer ciphertext.toList) := by
  rw [ciphertext_eq G n P hHalt hTape read hRead oracle state trace input hReal message horizon hTime,
    PMF.bind_map]
  rfl

include hHalt hTape hRead hReal in
/-- Two genuine PRG distinguishing premises bound the actual native
encryption experiment. Only the ciphertext observation is mathematical;
all native generation, copying, masking and caller halt costs are charged. -/
theorem advantage_le (messages : G.Messages n) (leftTime rightTime : Nat)
    (hLeft : P.execution.budget input + 50 * G.outputLength n + 39 ≤ leftTime)
    (hRight : P.execution.budget input + 50 * G.outputLength n + 39 ≤ rightTime)
    (observer : List Bool → PMF Bool) :
    probabilityGap
      (eventProb ((GeneratedBlockMask.ciphertext P oracle state trace messages.1 input leftTime).bind observer) (· = true))
      (eventProb ((GeneratedBlockMask.ciphertext P oracle state trace messages.2 input rightTime).bind observer) (· = true)) ≤
    G.prgGoal.advantage n messages (G.reduce messages false (fun ciphertext => observer ciphertext.toList)) +
      G.prgGoal.advantage n messages (G.reduce messages true (fun ciphertext => observer ciphertext.toList)) := by
  rw [observer_eq G n P hHalt hTape read hRead oracle state trace input hReal messages.1 leftTime hLeft observer,
    observer_eq G n P hHalt hTape read hRead oracle state trace input hReal messages.2 rightTime hRight observer]
  exact G.advantage_le n messages (fun ciphertext => observer ciphertext.toList)

include hHalt hTape hRead hReal in
theorem advantage_le_sum (messages : G.Messages n) (leftTime rightTime : Nat)
    (hLeft : P.execution.budget input + 50 * G.outputLength n + 39 ≤ leftTime)
    (hRight : P.execution.budget input + 50 * G.outputLength n + 39 ≤ rightTime)
    (observer : List Bool → PMF Bool) (leftBound rightBound : ℝ≥0∞)
    (hLeftBound : G.prgGoal.advantage n messages
      (G.reduce messages false (fun ciphertext => observer ciphertext.toList)) ≤ leftBound)
    (hRightBound : G.prgGoal.advantage n messages
      (G.reduce messages true (fun ciphertext => observer ciphertext.toList)) ≤ rightBound) :
    probabilityGap
      (eventProb ((GeneratedBlockMask.ciphertext P oracle state trace messages.1 input leftTime).bind observer) (· = true))
      (eventProb ((GeneratedBlockMask.ciphertext P oracle state trace messages.2 input rightTime).bind observer) (· = true)) ≤
      leftBound + rightBound :=
  (advantage_le G n P hHalt hTape read hRead oracle state trace input hReal messages leftTime rightTime
    hLeft hRight observer).trans (add_le_add hLeftBound hRightBound)

/-- A uniform native implementation across all security parameters.
The finite generator code is fixed; public sizes are carried by physical
entry tapes, and each parameter has a genuine execution certificate. -/
structure Implementation (G : Generator) where
  Input : Nat → Type v
  code : Program
  execution : ∀ n, TimedExecution.Procedure (stepPMF code) (Input n) (Bits (G.outputLength n))
  halt : ∀ n input key, ((execution n).exit input key).halted = true
  tape : ∀ n input key, ((execution n).exit input key).outputTape = ResponseExport.endTape key.toList
  read : ∀ n, Input n → Machine.Configuration → Bits (G.outputLength n)
  read_exit : ∀ n input key, read n input ((execution n).exit input key) = key
  implements : ∀ n input, (execution n).semantics input = G.real n

namespace Implementation
variable {G : Generator} (I : Implementation.{v} G)

def native (n : Nat) : Machine.Procedure (I.Input n) (Bits (G.outputLength n)) :=
  ⟨I.code, I.execution n⟩

theorem native_code (n : Nat) : (I.native n).code = I.code := rfl

theorem time_polynomial (samples : ∀ n, I.Input n)
    (hGeneration : PolynomiallyBounded (fun n => (I.execution n).budget (samples n)))
    (hWidth : PolynomiallyBounded G.outputLength) :
    PolynomiallyBounded (fun n => (I.execution n).budget (samples n) + 50 * G.outputLength n + 39) :=
  GeneratedBlockMask.budget_polynomial hGeneration hWidth

theorem ciphertext_eq (n : Nat) (input : I.Input n) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (message : Bits (G.outputLength n)) (horizon : Nat)
    (hTime : (I.execution n).budget input + 50 * G.outputLength n + 39 ≤ horizon) :
    GeneratedBlockMask.ciphertext (I.native n) oracle state trace message input horizon =
      (G.ciphertext n message).map Bits.toList :=
  PRG.ciphertext_eq G n (I.native n) (I.halt n) (I.tape n) (I.read n) (I.read_exit n)
    oracle state trace input (I.implements n input) message horizon hTime

/-- Negligible PRG advantages for both message-dependent observers imply
negligible advantage for the actual fixed-code encryption family. Running
time and observer-class membership are separate proved obligations. -/
theorem negligible (samples : ∀ n, I.Input n) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (messages : ∀ n, G.Messages n)
    (observer : Nat → List Bool → PMF Bool) (horizon : Nat → Nat)
    (hTime : ∀ n, (I.execution n).budget (samples n) + 50 * G.outputLength n + 39 ≤ horizon n)
    (hLeft : Negligible (fun n => G.prgGoal.advantage n (messages n)
      (G.reduce (messages n) false (fun ciphertext => observer n ciphertext.toList))))
    (hRight : Negligible (fun n => G.prgGoal.advantage n (messages n)
      (G.reduce (messages n) true (fun ciphertext => observer n ciphertext.toList)))) :
    Negligible (fun n => probabilityGap
      (eventProb ((GeneratedBlockMask.ciphertext (I.native n) oracle state trace (messages n).1 (samples n) (horizon n)).bind
        (observer n)) (· = true))
      (eventProb ((GeneratedBlockMask.ciphertext (I.native n) oracle state trace (messages n).2 (samples n) (horizon n)).bind
        (observer n)) (· = true))) :=
  Negligible.mono
    (fun n => PRG.advantage_le G n (I.native n) (I.halt n) (I.tape n) (I.read n) (I.read_exit n)
      oracle state trace (samples n) (I.implements n (samples n)) (messages n) (horizon n) (horizon n)
      (hTime n) (hTime n) (observer n)) (hLeft.add hRight)

end Implementation

end Foundation.Symmetric.EncryptThenMAC.GeneratedBlockMask.PRG
