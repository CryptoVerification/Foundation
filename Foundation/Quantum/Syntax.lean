import Foundation.Logic.Translation
import Foundation.Quantum.Space

/-! An equational object logic reconstructed from the diagram calculations in
Heunen, especially 3.3.9. The thesis does not specify this proof calculus.
No rule accepts an arbitrary semantic truth. Inputs and outputs are linear
wire interfaces; the meta-context contains reusable equations, not states. -/
namespace Foundation.Quantum
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

inductive Term : Space → Space → Type where
  | variable (a b : Space) (label : Nat) : Term a b
  | mix : Term .bit .bit
  | ident (a) : Term a a
  | seq {a b c} : Term a b → Term b c → Term a c
  | tensor {a b c d} : Term a b → Term c d → Term (.tensor a c) (.tensor b d)
  | dagger {a b} : Term a b → Term b a
  | conjugate {a b} : Term a b → Term a b
  | name {a b} : Term a b → Term .unit (.tensor a b)
  | copy (a) : Term a (.tensor a a)
  | erase (a) : Term a .unit
  | cup (a) : Term .unit (.tensor a a)
  | cap (a) : Term (.tensor a a) .unit
  | swap (a b) : Term (.tensor a b) (.tensor b a)
  | assoc (a b c) : Term (.tensor (.tensor a b) c) (.tensor a (.tensor b c))
  | unleft (a) : Term (.tensor .unit a) a
  | unright (a) : Term (.tensor a .unit) a

namespace Term
abbrev leftErase (a) := seq (tensor (erase a) (ident a)) (unleft a)
abbrev rightErase (a) := seq (tensor (ident a) (erase a)) (unright a)
abbrev correlated {a b} (m : Term a b) := seq (cup a) (tensor (conjugate m) m)
abbrev alice {a b} (m : Term a b) := seq (correlated m) (leftErase b)
abbrev bob {a b} (m : Term a b) := seq (correlated m) (rightErase b)
end Term

structure Equation where
  source : Space
  target : Space
  lhs : Term source target
  rhs : Term source target

abbrev equation {a b} (f g : Term a b) : Equation := ⟨a, b, f, g⟩

/-- Named, syntactic equation schemes. Their validity is proved in Semantics. -/
inductive Law where
  | refl {a b} (f : Term a b)
  | idLeft {a b} (f : Term a b)
  | idRight {a b} (f : Term a b)
  | assoc {a b c d} (f : Term a b) (g : Term b c) (h : Term c d)
  | daggerDagger {a b} (f : Term a b)
  | daggerSeq {a b c} (f : Term a b) (g : Term b c)
  | tensorSeq {a b c d e z} (f : Term a b) (g : Term b c) (h : Term d e) (k : Term e z)
  | correlated {a b} (m : Term a b)
  | nameId (a : Space)
  | cupCopy (a : Space)
  | leftCounit (a : Space)
  | rightCounit (a : Space)
  | special (a : Space)
  | coassoc (a : Space)
  | cocomm (a : Space)
  | frobenius (a : Space)
  | snakeLeft (a : Space)
  | snakeRight (a : Space)
  | mixEpi

namespace Law
open Term

def claim : Law → Equation
  | .refl f => equation f f
  | .idLeft f => equation (seq (ident _) f) f
  | .idRight f => equation (seq f (ident _)) f
  | .assoc f g h => equation (seq (seq f g) h) (seq f (seq g h))
  | .daggerDagger f => equation (dagger (dagger f)) f
  | .daggerSeq f g => equation (dagger (seq f g)) (seq (dagger g) (dagger f))
  | .tensorSeq f g h k => equation (tensor (seq f g) (seq h k))
      (seq (tensor f h) (tensor g k))
  | .correlated m => equation (Term.correlated m) (name (seq (dagger m) m))
  | .nameId a => equation (name (ident a)) (cup a)
  | .cupCopy a => equation (cup a) (seq (dagger (erase a)) (copy a))
  | .leftCounit a => equation (seq (copy a) (leftErase a)) (ident a)
  | .rightCounit a => equation (seq (copy a) (rightErase a)) (ident a)
  | .special a => equation (seq (copy a) (dagger (copy a))) (ident a)
  | .coassoc a => equation (seq (seq (copy a) (tensor (copy a) (ident a))) (Term.assoc a a a))
      (seq (copy a) (tensor (ident a) (copy a)))
  | .cocomm a => equation (seq (copy a) (swap a a)) (copy a)
  | .frobenius a => equation (seq (dagger (copy a)) (copy a))
      (seq (seq (tensor (ident a) (copy a)) (dagger (Term.assoc a a a)))
        (tensor (dagger (copy a)) (ident a)))
  | .snakeLeft a => equation
      (seq (seq (seq (dagger (unright a)) (tensor (ident a) (cup a)))
        (dagger (Term.assoc a a a))) (seq (tensor (cap a) (ident a)) (unleft a))) (ident a)
  | .snakeRight a => equation
      (seq (seq (seq (dagger (unleft a)) (tensor (cup a) (ident a)))
        (Term.assoc a a a)) (seq (tensor (ident a) (cap a)) (unright a))) (ident a)
  | .mixEpi => equation (seq (dagger mix) mix) (ident .bit)
end Law

inductive Rule where
  | law : Law → Rule
  | symm {a b} (f g : Term a b)
  | trans {a b} (f g h : Term a b)
  | seqCong {a b c} (f f' : Term a b) (g g' : Term b c)
  | tensorCong {a b c d} (f f' : Term a b) (g g' : Term c d)
  | daggerCong {a b} (f f' : Term a b)
  | conjugateCong {a b} (f f' : Term a b)
  | nameCong {a b} (f f' : Term a b)

abbrev presentation : Presentation where
  Judgment := Equation
  Rule := Rule
  arity := fun
    | .law _ => 0
    | .trans .. | .seqCong .. | .tensorCong .. => 2
    | _ => 1
  premise := fun
    | .law _ => Fin.elim0
    | .symm f g => fun _ => equation f g
    | .trans f g h => Fin.cases (equation f g) (fun _ => equation g h)
    | .seqCong f f' g g' => Fin.cases (equation f f') (fun _ => equation g g')
    | .tensorCong f f' g g' => Fin.cases (equation f f') (fun _ => equation g g')
    | .daggerCong f f' | .conjugateCong f f' | .nameCong f f' => fun _ => equation f f'
  conclusion := fun
    | .law law => law.claim
    | .symm f g => equation g f
    | .trans f _ h => equation f h
    | .seqCong f f' g g' => equation (.seq f g) (.seq f' g')
    | .tensorCong f f' g g' => equation (.tensor f g) (.tensor f' g')
    | .daggerCong f f' => equation (.dagger f) (.dagger f')
    | .conjugateCong f f' => equation (.conjugate f) (.conjugate f')
    | .nameCong f f' => equation (.name f) (.name f')

abbrev Proof (Γ : Context presentation) {a b} (f g : Term a b) :=
  Derivation presentation Γ (equation f g)

namespace Proof
variable {Γ : Context presentation} {a b c : Space}

def law (l : Law) : Derivation presentation Γ l.claim := Derivation.apply (T := presentation) (Rule.law l) (fun i => Fin.elim0 i)

def refl (f : Term a b) : Proof Γ f f := law (.refl f)
def symm {f g : Term a b} (p : Proof Γ f g) : Proof Γ g f :=
  Derivation.apply (T := presentation) (Rule.symm f g) (fun _ => p)
def trans {f g h : Term a b} (p : Proof Γ f g) (q : Proof Γ g h) : Proof Γ f h :=
  Derivation.apply (T := presentation) (Rule.trans f g h) (Fin.cases p (fun _ => q))
def seqCong {f f' : Term a b} {g g' : Term b c}
    (p : Proof Γ f f') (q : Proof Γ g g') : Proof Γ (.seq f g) (.seq f' g') :=
  Derivation.apply (T := presentation) (Rule.seqCong f f' g g') (Fin.cases p (fun _ => q))
def nameCong {f f' : Term a b} (p : Proof Γ f f') : Proof Γ (.name f) (.name f') :=
  Derivation.apply (T := presentation) (Rule.nameCong f f') (fun _ => p)

/-- The actual syntactic derivation of the naming step in Heunen 3.3.9. -/
def measuredCup (m : Term a b) (h : Proof Γ (.seq (.dagger m) m) (.ident b)) :
    Proof Γ (Term.correlated m) (.seq (.dagger (.erase b)) (.copy b)) :=
  trans (law (.correlated m))
    (trans (nameCong h) (trans (law (.nameId b)) (law (.cupCopy b))))

/-- Heunen 3.3.9 as a finite derivation, with the measurement equation explicit. -/
def qkd (m : Term a b) (h : Proof Γ (.seq (.dagger m) m) (.ident b)) :
    Proof Γ (Term.alice m) (Term.bob m) := by
  let s := measuredCup m h
  let l : Proof Γ (Term.alice m) (.dagger (.erase b)) :=
    trans (seqCong s (refl _))
      (trans (law (.assoc _ _ _))
        (trans (seqCong (refl _) (law (.leftCounit b))) (law (.idRight _))))
  let r : Proof Γ (Term.bob m) (.dagger (.erase b)) :=
    trans (seqCong s (refl _))
      (trans (law (.assoc _ _ _))
        (trans (seqCong (refl _) (law (.rightCounit b))) (law (.idRight _))))
  exact trans l (symm r)
end Proof

abbrev measurementContext {a b} (m : Term a b) : Context presentation :=
  .singleton (equation (.seq (.dagger m) m) (.ident b))

def qkdConditional {a b} (m : Term a b) :
    Proof (measurementContext m) (Term.alice m) (Term.bob m) :=
  Proof.qkd m (.hypothesis 0)

/-- A concrete closed proof replaces the measurement hypothesis by a named gate law. -/
def qkdMix : Proof (Context.empty presentation) (Term.alice .mix) (Term.bob .mix) :=
  (qkdConditional .mix).substitute (fun _ => Proof.law .mixEpi)

end Foundation.Quantum
