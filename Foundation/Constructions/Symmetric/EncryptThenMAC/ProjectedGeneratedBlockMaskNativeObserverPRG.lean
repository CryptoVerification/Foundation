import Foundation.Constructions.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMaskNativeObserver
import Foundation.Constructions.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMaskPRG

/-! PRG transfer for the actual generator/encryption/native-observer runtime.
Security of both message-dependent PRG distinguishers remains an explicit
premise. Runtime contracts never imply cryptographic pseudorandomness. -/
namespace Foundation.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask.PRG.NativeObserver
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Examples
open scoped ENNReal
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Input : Type v} {Result : Type w} {Output : Type x} (G : Generator) (n : Nat)
    (P : Machine.Procedure Input Result) (key : Result → Bits (G.outputLength n))
    (hHalt : ∀ input result, (P.execution.exit input result).halted = true)
    (hTape : ∀ input result, (P.execution.exit input result).outputTape = ResponseExport.endTape (key result).toList)
    (read : Input → Machine.Configuration → Result)
    (hRead : ∀ input result, read input (P.execution.exit input result) = result)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (input : Input) (hReal : (P.execution.semantics input).map key = G.real n)
    (Q : Machine.Procedure Machine.Configuration Output)
    (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hQHalt : ∀ machine output, output ∈ (Q.execution.semantics machine).support →
      (Q.execution.exit machine output).halted = true)
    (cap : Nat) (hCap : ∀ ciphertext : List Bool, ciphertext.length = G.outputLength n →
      Q.execution.budget (ReusableBlockPad.NativeObserver.publicCaller ciphertext) ≤ cap)

include hHalt hTape hRead hReal hEntry hQHalt hCap in
theorem game_eq (message : Bits (G.outputLength n)) (horizon : Nat)
    (hTime : P.execution.budget input + 50 * G.outputLength n + 40 + cap ≤ horizon) :
    ProjectedGeneratedBlockMask.NativeObserver.game P oracle state trace message input Q horizon =
      (G.ciphertext n message).bind
        (fun ciphertext => ReusableBlockPad.NativeObserver.observer Q ciphertext.toList) := by
  rw [ProjectedGeneratedBlockMask.NativeObserver.game_eq P key hHalt hTape read hRead oracle state trace message input
    Q hEntry hQHalt cap hCap horizon hTime]
  rw [PRG.ciphertext_eq G n P key hHalt hTape read hRead oracle state trace input hReal message _ (Nat.le_refl _),
    PMF.bind_map]
  rfl

include hHalt hTape hRead hReal hEntry hQHalt hCap in
theorem advantage_le (messages : G.Messages n) (leftTime rightTime : Nat)
    (hLeft : P.execution.budget input + 50 * G.outputLength n + 40 + cap ≤ leftTime)
    (hRight : P.execution.budget input + 50 * G.outputLength n + 40 + cap ≤ rightTime) :
    probabilityGap
      (eventProb (ProjectedGeneratedBlockMask.NativeObserver.game P oracle state trace messages.1 input Q leftTime) (· = true))
      (eventProb (ProjectedGeneratedBlockMask.NativeObserver.game P oracle state trace messages.2 input Q rightTime) (· = true)) ≤
    G.prgGoal.advantage n messages (G.reduce messages false
      (fun ciphertext => ReusableBlockPad.NativeObserver.observer Q ciphertext.toList)) +
    G.prgGoal.advantage n messages (G.reduce messages true
      (fun ciphertext => ReusableBlockPad.NativeObserver.observer Q ciphertext.toList)) := by
  rw [game_eq G n P key hHalt hTape read hRead oracle state trace input hReal Q hEntry hQHalt cap hCap
      messages.1 leftTime hLeft,
    game_eq G n P key hHalt hTape read hRead oracle state trace input hReal Q hEntry hQHalt cap hCap
      messages.2 rightTime hRight]
  exact G.advantage_le n messages (fun ciphertext => ReusableBlockPad.NativeObserver.observer Q ciphertext.toList)

include hHalt hTape hRead hReal hEntry hQHalt hCap in
theorem advantage_le_sum (messages : G.Messages n) (leftTime rightTime : Nat)
    (hLeft : P.execution.budget input + 50 * G.outputLength n + 40 + cap ≤ leftTime)
    (hRight : P.execution.budget input + 50 * G.outputLength n + 40 + cap ≤ rightTime)
    (leftBound rightBound : ℝ≥0∞)
    (hLeftBound : G.prgGoal.advantage n messages (G.reduce messages false
      (fun ciphertext => ReusableBlockPad.NativeObserver.observer Q ciphertext.toList)) ≤ leftBound)
    (hRightBound : G.prgGoal.advantage n messages (G.reduce messages true
      (fun ciphertext => ReusableBlockPad.NativeObserver.observer Q ciphertext.toList)) ≤ rightBound) :
    probabilityGap
      (eventProb (ProjectedGeneratedBlockMask.NativeObserver.game P oracle state trace messages.1 input Q leftTime) (· = true))
      (eventProb (ProjectedGeneratedBlockMask.NativeObserver.game P oracle state trace messages.2 input Q rightTime) (· = true)) ≤
      leftBound + rightBound :=
  (advantage_le G n P key hHalt hTape read hRead oracle state trace input hReal Q hEntry hQHalt cap hCap
    messages leftTime rightTime hLeft hRight).trans (add_le_add hLeftBound hRightBound)

namespace Implementation
variable {G : Generator} (I : PRG.Implementation.{v,w} G)

theorem time_polynomial (samples : ∀ n, I.Input n)
    (hGeneration : PolynomiallyBounded (fun n => (I.execution n).budget (samples n)))
    (hWidth : PolynomiallyBounded G.outputLength) {observerCap : Nat → Nat}
    (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded (fun n => (I.execution n).budget (samples n) + 50 * G.outputLength n + 40 + observerCap n) :=
  ProjectedGeneratedBlockMask.NativeObserver.time_polynomial hGeneration hWidth hObserver

/-- The generator and observer codes are fixed throughout the parameter
family. Only genuine executions on the physical parameter-dependent tapes
are used; no parameter-dependent native code compiler is assumed. -/
theorem negligible (samples : ∀ n, I.Input n) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (messages : ∀ n, G.Messages n)
    (Q : Machine.Procedure Machine.Configuration Output)
    (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hQHalt : ∀ machine output, output ∈ (Q.execution.semantics machine).support →
      (Q.execution.exit machine output).halted = true)
    (observerCap horizon : Nat → Nat)
    (hCap : ∀ n ciphertext, ciphertext.length = G.outputLength n →
      Q.execution.budget (ReusableBlockPad.NativeObserver.publicCaller ciphertext) ≤ observerCap n)
    (hTime : ∀ n, (I.execution n).budget (samples n) + 50 * G.outputLength n + 40 + observerCap n ≤ horizon n)
    (hLeft : Negligible (fun n => G.prgGoal.advantage n (messages n)
      (G.reduce (messages n) false
        (fun ciphertext => ReusableBlockPad.NativeObserver.observer Q ciphertext.toList))))
    (hRight : Negligible (fun n => G.prgGoal.advantage n (messages n)
      (G.reduce (messages n) true
        (fun ciphertext => ReusableBlockPad.NativeObserver.observer Q ciphertext.toList)))) :
    Negligible (fun n => probabilityGap
      (eventProb (ProjectedGeneratedBlockMask.NativeObserver.game (I.native n) oracle state trace (messages n).1 (samples n) Q (horizon n)) (· = true))
      (eventProb (ProjectedGeneratedBlockMask.NativeObserver.game (I.native n) oracle state trace (messages n).2 (samples n) Q (horizon n)) (· = true))) :=
  Negligible.mono
    (fun n => advantage_le G n (I.native n) (I.key n) (I.halt n) (I.tape n) (I.read n) (I.read_exit n)
      oracle state trace (samples n) (I.implements n (samples n)) Q hEntry hQHalt (observerCap n) (hCap n)
      (messages n) (horizon n) (horizon n) (hTime n) (hTime n)) (hLeft.add hRight)

end Implementation
end Foundation.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask.PRG.NativeObserver
