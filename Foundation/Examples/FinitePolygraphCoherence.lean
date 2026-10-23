import Foundation.Logic.Polygraph.FiniteCompletion
import Foundation.Examples.PolygraphCoherence
import Foundation.Crypto.Meta.Polygraph.FiniteCoherence
import Foundation.Constructions.Symmetric.PRGPolygraphPaths
import Foundation.Constructions.Symmetric.EncryptThenMAC.Polygraph

/-! All five critical shapes, all five variable-overlap shapes, exchange,
context closure, reversals, and empty words. The mixed-boundary examples have
different source and target objects, rather than just one untyped object. -/
namespace Foundation.Logic.Polygraph.Examples.FiniteCoherence

open Foundation.Logic.Polygraph.Composition
open Composition.Finite
set_option backward.isDefEq.respectTransparency false

abbrev Edge (_ _ : Nat) := Unit
def f : Expr Edge 0 1 := .atom ()
def g : Expr Edge 1 2 := .atom ()
def h : Expr Edge 2 3 := .atom ()
def i : Expr Edge 3 4 := .atom ()

def kinds : List ForkKind := [
  (localJoin (.assoc (.seq f g) h i) (.left (.assoc f g h) i)).kind,
  (localJoin (.assoc (.identity 0) f g) (.left (.leftUnit f) g)).kind,
  (localJoin (.assoc f (.identity 1) g) (.left (.rightUnit f) g)).kind,
  (localJoin (.assoc f g (.identity 2)) (.rightUnit (.seq f g))).kind,
  (localJoin (.leftUnit (.identity (E := Edge) 0)) (.rightUnit (.identity 0))).kind,
  (localJoin (.leftUnit (.seq (.identity 0) f)) (.right (.identity 0) (.leftUnit f))).kind,
  (localJoin (.rightUnit (.seq (.identity 0) f)) (.left (.leftUnit f) (.identity 1))).kind,
  (localJoin (.assoc (.seq (.identity 0) f) g h) (.left (.left (.leftUnit f) g) h)).kind,
  (localJoin (.assoc f (.seq (.identity 1) g) h) (.left (.right f (.leftUnit g)) h)).kind,
  (localJoin (.assoc f g (.seq (.identity 2) h)) (.right (.seq f g) (.leftUnit h))).kind,
  (localJoin (.left (.leftUnit f) (.seq g (.identity 2)))
    (.right (.seq (.identity 0) f) (.rightUnit g))).kind,
  (localJoin (.left (.leftUnit f) g) (.left (.leftUnit f) g)).kind,
  (localJoin (.right f (.leftUnit g)) (.right f (.leftUnit g))).kind,
  (localJoin (.leftUnit f) (.leftUnit f)).kind]

/-- info: [Foundation.Logic.Polygraph.Composition.Finite.ForkKind.pentagon,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.assocLeftUnit,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.assocMiddleUnit,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.assocRightUnit,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.units,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.leftUnitNatural,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.rightUnitNatural,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.assocNaturalFirst,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.assocNaturalSecond,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.assocNaturalThird,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.exchange,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.nestedLeft,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.nestedRight,
 Foundation.Logic.Polygraph.Composition.Finite.ForkKind.identical] -/
#guard_msgs in
#eval kinds

def pentagon : Finite.Cell4 (Track.ofPath Coherence.upper) (Track.ofPath Coherence.lower) :=
  Finite.coherent _ _

def pentagonGenerator : Finite.Cell4 (Track.ofPath Coherence.upper) (Track.ofPath Coherence.lower) :=
  .generator (.pentagon Coherence.a Coherence.b Coherence.c Coherence.d)

def unitsComparison : Finite.Cell4 (Track.ofPath Coherence.unitShort)
    (Track.ofPath Coherence.unitLong) := Finite.coherent _ _

def reversedLoop : Finite.Cell4
    (.comp (.inv (Track.ofPath Coherence.upper)) (Track.ofPath Coherence.lower))
    (.refl Coherence.finish) := Finite.coherent _ _

def emptyWord : Expr Edge 0 0 := .seq (.identity 0) (.seq (.identity 0) (.identity 0))
def emptyNormal : Finite.Cell4 (Track.ofPath (Expr.normalizePath emptyWord))
    (Track.ofPath (Expr.normalizePath emptyWord)) := Finite.coherent _ _

def wrapped {O : Type} {E : O → O → Type} {a b : O} (e : Expr E a b) :=
  Expr.seq (.seq (.identity a) e) (.identity b)

def routeLeft {O : Type} {E : O → O → Type} {a b : O} (e : Expr E a b) :
    Expr.Path (wrapped e) e :=
  .cons (.left (.leftUnit e) (.identity b)) (.single (.rightUnit e))

def routeRight {O : Type} {E : O → O → Type} {a b : O} (e : Expr E a b) :
    Expr.Path (wrapped e) e :=
  .cons (.rightUnit (.seq (.identity a) e)) (.single (.leftUnit e))

def routeComparison {O : Type} {E : O → O → Type} {a b : O} (e : Expr E a b) :
    Finite.Cell4 (Track.ofPath (routeLeft e)) (Track.ofPath (routeRight e)) :=
  Finite.coherent _ _

namespace PRG
open Foundation.Symmetric.Generator
open CryptoLogic.General CryptoLogic.General.Backends
open scoped ENNReal

def expression := Diagram.quoteComposition Polygraph.proof
def comparison := routeComparison expression

theorem codes (code : Machine.Program) :
    CryptoLogic.Polygraph.Derivation.run (Diagram.denoteComposition (wrapped expression)) code =
      CryptoLogic.Polygraph.Derivation.run Polygraph.proof code := by
  have preserved := CryptoLogic.Polygraph.FiniteCoherence.run_path
    (Track.ofPath (routeLeft expression)) code
  simpa only [expression, Diagram.denote_quote] using preserved

theorem loss (G : Foundation.Symmetric.Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (ε : Fin 1 → Nat → ℝ≥0∞) (n : Nat) :
    (CryptoLogic.Polygraph.Derivation.loss (Polygraph.interpretation G time F)
      (Diagram.denoteComposition (wrapped expression))).eval ε n = 2 * ε 0 n := by
  have preserved := CryptoLogic.Polygraph.FiniteCoherence.loss_path
    (Track.ofPath (routeLeft expression)) (Polygraph.interpretation G time F)
  simp only [expression, Diagram.denote_quote] at preserved
  simp only [expression]
  rw [preserved]
  exact Polygraph.loss G time F ε n

theorem witnesses (G : Foundation.Symmetric.Generator) (time : Nat → Nat)
    (F : InstanceFamily G.encryptionGoal) (A)
    (W : (Polygraph.object G time .encryption).Witness F A) :
    CryptoLogic.Polygraph.Derivation.runWitnesses (Polygraph.interpretation G time F)
      (Diagram.denoteComposition (wrapped expression)) A W =
    CryptoLogic.Polygraph.Derivation.runWitnesses (Polygraph.interpretation G time F)
      Polygraph.proof A W := by
  have preserved := CryptoLogic.Polygraph.FiniteCoherence.witnesses_path
    (Track.ofPath (routeRight expression)) (Polygraph.interpretation G time F) A W
  simpa only [expression, Diagram.denote_quote] using preserved

end PRG

namespace EncryptThenMAC
open Foundation.Symmetric.EncryptThenMAC
open scoped ENNReal
def expression := Diagram.quoteComposition Polygraph.expandedProof
def comparison := routeComparison expression

theorem interpretations (M : Foundation.Logic.Model Logic.lower)
    (env : Environment M (Logic.context.map Logic.expansion.judgment)) :
    (Diagram.denoteComposition (wrapped expression)).eval M env =
      Polygraph.expandedProof.eval M env := by
  have preserved := (CryptoLogic.Polygraph.FiniteCoherence.interpretPath
    (Track.ofPath (routeRight expression))).eval_eq M env
  simpa only [expression, Diagram.denote_quote] using preserved

theorem loss (ε δ : ℝ≥0∞) :
    (Diagram.denoteComposition (wrapped expression)).eval Polygraph.lowerLoss
      (Fin.cases ε (fun _ => δ)) 0 = ε + δ := by
  have first := congrFun (interpretations Polygraph.lowerLoss (Fin.cases ε (fun _ => δ))) 0
  have second := congrFun (Polygraph.expansionPath.eval_eq Polygraph.lowerLoss
    (Fin.cases ε (fun _ => δ))) 0
  exact first.trans (second.symm.trans (Polygraph.proof_loss ε δ))

universe v
variable {K : CryptoLogic.General.CodeSystem} {auth enc mac : K.Machine}

theorem codes (cE : CryptoLogic.General.Compiler K auth enc)
    (cM : CryptoLogic.General.Compiler K auth mac) (code : K.Code auth) :
    (Diagram.denoteComposition (wrapped expression)).eval (Operational.lowerCode cE cM 2)
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
    (Diagram.denoteComposition (wrapped expression)).eval (Operational.lowerWitnesses R length) env =
      Polygraph.expandedProof.eval (Operational.lowerWitnesses R length) env :=
  interpretations _ env

end EncryptThenMAC

#guard_msgs (drop info) in
#check_failure (pentagon : Finite.Cell4 (Track.ofPath Coherence.upper) (Track.ofPath Coherence.upper))

end Foundation.Logic.Polygraph.Examples.FiniteCoherence
