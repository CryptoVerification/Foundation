import Foundation.Crypto.Meta.Polygraph.CartesianCoherence
import Foundation.Examples.FinitePolygraphCoherence

/-! Full-syntax finite coherence examples, including genuinely different
routes under tensor, copy/delete, a selected shared output, empty outputs,
and preservation of concrete cryptographic interpretations. -/
namespace Foundation.Logic.Polygraph.Examples.CartesianCoherence
open Cartesian
set_option backward.isDefEq.respectTransparency false

universe j r
variable {T : Logic.Presentation.{j, r}}
  {Γ Δ Γ' Δ' : Logic.Context T}

def tensorFirst (d : Diagram T Γ Δ) (e : Diagram T Γ' Δ') :
    Diagram.Cell3 (.tensor (.seq (.identity Γ) d) (.seq e (.identity Δ'))) (.tensor d e) :=
  .comp (.step (.tensorLeft (.leftUnit d) (.seq e (.identity Δ'))))
    (.step (.tensorRight d (.rightUnit e)))

def tensorSecond (d : Diagram T Γ Δ) (e : Diagram T Γ' Δ') :
    Diagram.Cell3 (.tensor (.seq (.identity Γ) d) (.seq e (.identity Δ'))) (.tensor d e) :=
  .comp (.step (.tensorRight (.seq (.identity Γ) d) (.rightUnit e)))
    (.step (.tensorLeft (.leftUnit d) e))

def tensorExchange (d : Diagram T Γ Δ) (e : Diagram T Γ' Δ') :
    Cartesian.Cell4 (tensorFirst d e) (tensorSecond d e) := Cartesian.coherent _ _

def copyDeleteFirst (d : Diagram T Γ Δ) :
    Diagram.Cell3
      (.seq (.seq d (.wiring (Wiring.duplicate Δ)))
        (.wiring (Wiring.discard (Context.append Δ Δ))))
      (.wiring (Wiring.discard Γ)) :=
  .comp ((duplicateNatural d).seqLeft (.wiring (Wiring.discard (Context.append Δ Δ))))
    (discardNatural (.seq (.wiring (Wiring.duplicate Γ)) (.tensor d d)))

def copyDeleteSecond (d : Diagram T Γ Δ) :
    Diagram.Cell3
      (.seq (.seq d (.wiring (Wiring.duplicate Δ)))
        (.wiring (Wiring.discard (Context.append Δ Δ))))
      (.wiring (Wiring.discard Γ)) :=
  discardNatural (.seq d (.wiring (Wiring.duplicate Δ)))

def copyDelete (d : Diagram T Γ Δ) :
    Cartesian.Cell4 (copyDeleteFirst d) (copyDeleteSecond d) := Cartesian.coherent _ _

def outputFirst (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i)))
    (i : Fin Δ.length) :
    Diagram.Cell3
      (.tuple (Function.update children i (.seq (.identity Γ) (children i))))
      (.tuple (Function.update children i (children i))) :=
  .step (.tupleAt children i (.leftUnit (children i)))

def outputSecond (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i)))
    (i : Fin Δ.length) :
    Diagram.Cell3
      (.tuple (Function.update children i (.seq (.identity Γ) (children i))))
      (.tuple (Function.update children i (children i))) :=
  Diagram.connect _ _ (outputFirst children i).forest_eq

def outputComparison (children : ∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i)))
    (i : Fin Δ.length) : Cartesian.Cell4 (outputFirst children i) (outputSecond children i) :=
  Cartesian.coherent _ _

def emptyLoop (Γ : Logic.Context T) :
    Cartesian.Cell4 (.comp (tupleEta (.wiring (Wiring.discard Γ)))
      (.inv (tupleEta (.wiring (Wiring.discard Γ))))) (.refl _) := Cartesian.coherent _ _

-- Every one of the nine schema forms is inhabited, and its code is executed.
def schemaCodes : List Nat := [
  (Generator.root (.assoc (.identity one) (.identity one) (.identity one)) _ rfl).code.val,
  (Generator.root (.leftUnit (.identity (T := theory) one)) _ rfl).code.val,
  (Generator.root (.rightUnit (.identity (T := theory) one)) _ rfl).code.val,
  (Generator.normalLoop (Diagram.identity (T := theory) one).toForest).code.val,
  (Generator.contextReconstruct (.seqLeft (.identity one)) shared.toForest ⟨shared, rfl⟩).code.val,
  (Generator.contextReconstruct (.seqRight (.identity one)) shared.toForest ⟨shared, rfl⟩).code.val,
  (Generator.contextReconstruct (.tensorLeft (.identity one)) shared.toForest ⟨shared, rfl⟩).code.val,
  (Generator.contextReconstruct (.tensorRight (.identity one)) shared.toForest ⟨shared, rfl⟩).code.val,
  (Generator.contextReconstruct (.tupleAt (Δ := one) (fun _ => shared) 0)
    shared.toForest ⟨shared, rfl⟩).code.val]

/-- info: [0, 1, 2, 3, 4, 5, 6, 7, 8] -/
#guard_msgs in
#eval schemaCodes

/-- info: [6, 6] -/
#guard_msgs in
#eval List.ofFn ((Diagram.seq shared (.wiring (Wiring.duplicate one))).eval numeric (fun _ => 3))

/-- info: [] -/
#guard_msgs in
#eval List.ofFn ((Diagram.seq shared (.wiring (Wiring.discard one))).eval numeric (fun _ => 3))

example : Cartesian.Cell4 (tensorFirst shared shared) (tensorSecond shared shared) := tensorExchange _ _
example : Cartesian.Cell4 (copyDeleteFirst shared) (copyDeleteSecond shared) := copyDelete _
example : Cartesian.Cell4 (outputFirst (Δ := two) (fun _ => shared) 1)
    (outputSecond (Δ := two) (fun _ => shared) 1) := outputComparison _ _

/-- Equal boundaries cannot identify different rule trees. -/
theorem distinctRules : ¬ Nonempty (Diagram.Cell3
    (Diagram.generator (T := theory) .unary) (Diagram.generator (T := theory) .alternative)) := by
  rintro ⟨p⟩
  have h := congrFun (p.eval_eq numeric (fun _ => 3)) 0
  change 4 = 5 at h
  contradiction

namespace PRG
open Foundation.Symmetric.Generator
open CryptoLogic.General CryptoLogic.General.Backends
open scoped ENNReal

def start := Diagram.seq (Diagram.tuple (fun _ : Fin 1 => Polygraph.proof))
  (.wiring (Wiring.select (Logic.Context.singleton _) 0))
def path : Diagram.Cell3 start Polygraph.proof := tupleProjection
  (T := CryptoLogic.Presented.presentation Polygraph.parameters)
  (Δ := Logic.Context.singleton ⟨Polygraph.Object.encryption, ()⟩)
  (fun _ => Polygraph.proof) 0
def alternative : Diagram.Cell3 start Polygraph.proof := Diagram.connect _ _ path.forest_eq
def comparison : Cartesian.Cell4 path alternative := Cartesian.coherent _ _

theorem codes (code : Machine.Program) :
    CryptoLogic.Polygraph.Derivation.run start code =
      CryptoLogic.Polygraph.Derivation.run Polygraph.proof code :=
  CryptoLogic.Polygraph.CartesianCoherence.run_path path code

theorem loss (G : Foundation.Symmetric.Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (ε : Fin 1 → Nat → ℝ≥0∞) (n : Nat) :
    (CryptoLogic.Polygraph.Derivation.loss (Polygraph.interpretation G time F) start).eval ε n =
      2 * ε 0 n := by
  rw [CryptoLogic.Polygraph.CartesianCoherence.loss_path path]
  exact Polygraph.loss G time F ε n

theorem witnesses (G : Foundation.Symmetric.Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (A)
    (W : (Polygraph.object G time .encryption).Witness F A) :
    CryptoLogic.Polygraph.Derivation.runWitnesses (Polygraph.interpretation G time F) start A W =
      CryptoLogic.Polygraph.Derivation.runWitnesses (Polygraph.interpretation G time F)
        Polygraph.proof A W := CryptoLogic.Polygraph.CartesianCoherence.witnesses_path path
          (Polygraph.interpretation G time F) A W
end PRG

namespace EncryptThenMAC
open Foundation.Symmetric.EncryptThenMAC

def start := Diagram.tuple (fun i => Diagram.seq Polygraph.expandedProof
  (.wiring (Wiring.select (Logic.Context.singleton _) i)))
def path : Diagram.Cell3 start Polygraph.expandedProof := tupleEta _
def alternative : Diagram.Cell3 start Polygraph.expandedProof := Diagram.connect _ _ path.forest_eq
def comparison : Cartesian.Cell4 path alternative := Cartesian.coherent _ _

universe v
theorem interpretations (M : Logic.Model.{0, 0, v} Logic.lower)
    (env : Environment M (Logic.context.map Logic.expansion.judgment)) :
    start.eval M env = Polygraph.expandedProof.eval M env := path.eval_eq M env

open scoped ENNReal
theorem loss (ε δ : ℝ≥0∞) :
    start.eval Polygraph.lowerLoss
      (Fin.cases ε (fun _ => δ)) 0 = ε + δ := by
  have first := congrFun (interpretations Polygraph.lowerLoss (Fin.cases ε (fun _ => δ))) 0
  have second := congrFun (Polygraph.expansionPath.eval_eq Polygraph.lowerLoss
    (Fin.cases ε (fun _ => δ))) 0
  exact first.trans (second.symm.trans (Polygraph.proof_loss ε δ))

variable {K : CryptoLogic.General.CodeSystem} {auth enc mac : K.Machine}

theorem codes (cE : CryptoLogic.General.Compiler K auth enc)
    (cM : CryptoLogic.General.Compiler K auth mac) (code : K.Code auth) :
    start.eval (Operational.lowerCode cE cM 2)
      (fun i input => [(i, ⟨Operational.machine (Logic.context.claim i).object, input⟩)]) 0 code =
      [(0, ⟨enc, cE.run code⟩), (1, ⟨mac, cM.run code⟩)] := by
  have first := congrFun (congrFun (interpretations (Operational.lowerCode cE cM 2)
    (fun i input => [(i, ⟨Operational.machine (Logic.context.claim i).object, input⟩)])) 0) code
  have second := congrFun (congrFun (Polygraph.expansionPath.eval_eq
    (Operational.lowerCode cE cM 2)
    (fun i input => [(i, ⟨Operational.machine (Logic.context.claim i).object, input⟩)])) 0) code
  exact first.trans (second.symm.trans (Polygraph.proof_codes cE cM code))

variable {E : Encryption} {M : MAC E.Ciphertext}
  {X : Operational.Backend.{v} K auth (goal E M)}
  {Y : Operational.Backend.{v} K enc (encryptionGoal E)}
  {Z : Operational.Backend.{v} K mac (macGoal E M)}
  {cE : CryptoLogic.General.Compiler K auth enc} {cM : CryptoLogic.General.Compiler K auth mac}

theorem witnesses (R : Operational.Realization X Y Z cE cM) (length : Nat)
    (env : Environment (Operational.lowerWitnesses R length)
      (Logic.context.map Logic.expansion.judgment)) :
    start.eval (Operational.lowerWitnesses R length) env =
      Polygraph.expandedProof.eval (Operational.lowerWitnesses R length) env :=
  interpretations _ env


end EncryptThenMAC
end Foundation.Logic.Polygraph.Examples.CartesianCoherence
