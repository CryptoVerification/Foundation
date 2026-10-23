import Foundation.Logic.Polygraph.StructuralCartesianRewriting

/-! Explicit product-law derivations of the old eleven roots. Wire arguments
are opaque parameters; no whole-wire normalizer or semantic equality oracle
is used. These are first-level macro expansions, not higher coherence. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.BoundedOld
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def post {a b c : Shape Atom} {p q : Wire a b} (proof : Cell p q) (r : Wire b c) : Cell (.seq p r) (.seq q r) :=
  .seq proof (.refl r)

def pre {a b c : Shape Atom} (p : Wire a b) {q r : Wire b c} (proof : Cell q r) : Cell (.seq p q) (.seq p r) :=
  .seq (.refl p) proof

def ext {a b c : Shape Atom} {p q : Wire a (.pair b c)}
    (left : Cell (.seq p (fst b c)) (.seq q (fst b c)))
    (right : Cell (.seq p (snd b c)) (.seq q (snd b c))) : Cell p q :=
  (Cell.root (.eta p)).symm.trans ((Cell.fork left right).trans (Cell.root (.eta q)))

def etaId (a b : Shape Atom) : Cell (fork (fst a b) (snd a b)) (.identity (.pair a b)) :=
  (Cell.fork (Cell.root (.leftId (fst a b))).symm (Cell.root (.leftId (snd a b))).symm).trans
    (Cell.root (.eta (.identity (.pair a b))))

def tensorFst {a b c d : Shape Atom} (p : Wire a b) (q : Wire c d) :
    Cell (.seq (.tensor p q) (fst b d)) (.seq (fst a c) p) :=
  (post (Cell.root (.tensorExpand p q)) _).trans (Cell.root (.betaFst _ _))

def tensorSnd {a b c d : Shape Atom} (p : Wire a b) (q : Wire c d) :
    Cell (.seq (.tensor p q) (snd b d)) (.seq (snd a c) q) :=
  (post (Cell.root (.tensorExpand p q)) _).trans (Cell.root (.betaSnd _ _))

def copyFst (a : Shape Atom) : Cell (.seq (.copy a) (fst a a)) (.identity a) :=
  (post (Cell.root (.copyExpand a)) _).trans (Cell.root (.betaFst _ _))

def copySnd (a : Shape Atom) : Cell (.seq (.copy a) (snd a a)) (.identity a) :=
  (post (Cell.root (.copyExpand a)) _).trans (Cell.root (.betaSnd _ _))

/-- Compose a pair through a projection and a further opaque arrow. -/
def forkThenFst {a b c d : Shape Atom} (p : Wire a b) (q : Wire a c) (r : Wire b d) :
    Cell (.seq (fork p q) (.seq (fst b c) r)) (.seq p r) :=
  (Cell.root (.assoc _ _ _)).symm.trans (post (Cell.root (.betaFst p q)) r)

def forkThenSnd {a b c d : Shape Atom} (p : Wire a b) (q : Wire a c) (r : Wire c d) :
    Cell (.seq (fork p q) (.seq (snd b c) r)) (.seq q r) :=
  (Cell.root (.assoc _ _ _)).symm.trans (post (Cell.root (.betaSnd p q)) r)

/-- Rebracket an explicitly paired value without inspecting any argument. -/
def forkAssoc {x a b c : Shape Atom} (p : Wire x a) (q : Wire x b) (r : Wire x c) :
    Cell (.seq (fork (fork p q) r) (.assoc a b c)) (fork p (fork q r)) :=
  (pre _ (Cell.root (.assocExpand a b c))).trans
    ((Cell.root (.forkAfter _ _ _)).trans
      (Cell.fork
        ((forkThenFst (fork p q) r (fst a b)).trans (Cell.root (.betaFst p q)))
        ((Cell.root (.forkAfter _ _ _)).trans
          (Cell.fork
            ((forkThenFst (fork p q) r (snd a b)).trans (Cell.root (.betaSnd p q)))
            (Cell.root (.betaSnd (fork p q) r))))))

def forkUnassoc {x a b c : Shape Atom} (p : Wire x a) (q : Wire x b) (r : Wire x c) :
    Cell (.seq (fork p (fork q r)) (.unassoc a b c)) (fork (fork p q) r) :=
  (pre _ (Cell.root (.unassocExpand a b c))).trans
    ((Cell.root (.forkAfter _ _ _)).trans
      (Cell.fork
        ((Cell.root (.forkAfter _ _ _)).trans
          (Cell.fork (Cell.root (.betaFst p (fork q r)))
            ((forkThenSnd p (fork q r) (fst b c)).trans (Cell.root (.betaFst q r)))))
        ((forkThenSnd p (fork q r) (snd b c)).trans (Cell.root (.betaSnd q r)))))

def tensorIdentity (a b : Shape Atom) : Cell (.tensor (.identity a) (.identity b)) (.identity (.pair a b)) :=
  ext ((tensorFst _ _).trans ((Cell.root (.rightId _)).trans (Cell.root (.leftId _)).symm))
    ((tensorSnd _ _).trans ((Cell.root (.rightId _)).trans (Cell.root (.leftId _)).symm))

/-- Projection calculation for the interchange square. -/
def interchangeFst {a b c a' b' c' : Shape Atom} (p : Wire a b) (q : Wire b c) (p' : Wire a' b') (q' : Wire b' c') :
    Cell (.seq (.seq (.tensor p p') (.tensor q q')) (fst c c')) (.seq (fst a a') (.seq p q)) :=
  (Cell.root (.assoc _ _ _)).trans
    ((pre _ (tensorFst q q')).trans
      ((Cell.root (.assoc _ _ _)).symm.trans
        ((post (tensorFst p p') q).trans (Cell.root (.assoc _ _ _)))))

def interchangeSnd {a b c a' b' c' : Shape Atom} (p : Wire a b) (q : Wire b c) (p' : Wire a' b') (q' : Wire b' c') :
    Cell (.seq (.seq (.tensor p p') (.tensor q q')) (snd c c')) (.seq (snd a a') (.seq p' q')) :=
  (Cell.root (.assoc _ _ _)).trans
    ((pre _ (tensorSnd q q')).trans
      ((Cell.root (.assoc _ _ _)).symm.trans
        ((post (tensorSnd p p') q').trans (Cell.root (.assoc _ _ _)))))

def interchange {a b c a' b' c' : Shape Atom} (p : Wire a b) (q : Wire b c) (p' : Wire a' b') (q' : Wire b' c') :
    Cell (.seq (.tensor p p') (.tensor q q')) (.tensor (.seq p q) (.seq p' q')) :=
  ext ((interchangeFst p q p' q').trans (tensorFst _ _).symm)
    ((interchangeSnd p q p' q').trans (tensorSnd _ _).symm)

def copyAssoc (a : Shape Atom) :
    Cell (.seq (.seq (.copy a) (.tensor (.copy a) (.identity a))) (.assoc a a a))
      (.seq (.copy a) (.tensor (.identity a) (.copy a))) :=
  (post (Cell.fork (Cell.root (.copyExpand a)) (.refl _)) _).trans
    ((forkAssoc (.identity a) (.identity a) (.identity a)).trans
      (Cell.fork (.refl _) (Cell.root (.copyExpand a))).symm)

def copySwap (a : Shape Atom) : Cell (.seq (.copy a) (.swap a a)) (.copy a) :=
  (pre _ (Cell.root (.swapExpand a a))).trans
    ((Cell.root (.forkAfter _ _ _)).trans
      ((Cell.fork (copySnd a) (copyFst a)).trans (Cell.root (.copyExpand a)).symm))

def copyDiscardLeft (a : Shape Atom) :
    Cell (.seq (.seq (.copy a) (.tensor (.discard a) (.identity a))) (.leftUnit a)) (.identity a) :=
  (pre _ (Cell.root (.leftUnitExpand a))).trans (Cell.root (.betaSnd _ _))

def copyDiscardRight (a : Shape Atom) :
    Cell (.seq (.seq (.copy a) (.tensor (.identity a) (.discard a))) (.rightUnit a)) (.identity a) :=
  (pre _ (Cell.root (.rightUnitExpand a))).trans (Cell.root (.betaFst _ _))

def assocUnassoc (a b c : Shape Atom) :
    Cell (.seq (.assoc a b c) (.unassoc a b c)) (.identity (.pair (.pair a b) c)) :=
  (post (Cell.root (.assocExpand a b c)) _).trans
    ((forkUnassoc _ _ _).trans
      ((Cell.fork (Cell.root (.eta (fst (.pair a b) c))) (.refl _)).trans (etaId _ _)))

def unassocAssoc (a b c : Shape Atom) :
    Cell (.seq (.unassoc a b c) (.assoc a b c)) (.identity (.pair a (.pair b c))) :=
  (post (Cell.root (.unassocExpand a b c)) _).trans
    ((forkAssoc _ _ _).trans
      ((Cell.fork (.refl _) (Cell.root (.eta (snd a (.pair b c))))).trans (etaId _ _)))

def expandRoot {a b : Shape Atom} {p q : Wire a b} (root : Rewrite.Root p q) : Cell p q :=
  match root with
  | .seqAssoc p q r => .root (.assoc p q r)
  | .leftUnit p => .root (.leftId p)
  | .rightUnit p => .root (.rightId p)
  | .tensorIdentity a b => tensorIdentity a b
  | .interchange p q p' q' => interchange p q p' q'
  | .copyAssoc a => copyAssoc a
  | .copySwap a => copySwap a
  | .copyDiscardLeft a => copyDiscardLeft a
  | .copyDiscardRight a => copyDiscardRight a
  | .assocUnassoc a b c => assocUnassoc a b c
  | .unassocAssoc a b c => unassocAssoc a b c

def constructors : {a b : Shape Atom} → {p q : Wire a b} → Cell p q → Nat
  | _, _, _, _, .refl _ | _, _, _, _, .root _ => 1
  | _, _, _, _, .symm child => 1 + constructors child
  | _, _, _, _, .trans first second | _, _, _, _, .seq first second | _, _, _, _, .tensor first second =>
      1 + constructors first + constructors second

def roots : {a b : Shape Atom} → {p q : Wire a b} → Cell p q → Nat
  | _, _, _, _, .refl _ => 0
  | _, _, _, _, .root _ => 1
  | _, _, _, _, .symm child => roots child
  | _, _, _, _, .trans first second | _, _, _, _, .seq first second | _, _, _, _, .tensor first second => roots first + roots second

/-- Tables are indexed by the existing eleven root codes. -/
def constructorProfile (tag : Fin 11) : Nat :=
  match tag.val with
  | 0 | 1 | 2 => 1
  | 3 => 28
  | 4 => 66
  | 5 => 46
  | 6 => 22
  | 7 | 8 => 5
  | _ => 51

def rootProfile (tag : Fin 11) : Nat :=
  match tag.val with
  | 0 | 1 | 2 => 1
  | 3 => 10
  | 4 => 20
  | 5 => 12
  | 6 => 7
  | 7 | 8 => 2
  | _ => 15

theorem constructorProfile_exact {a b : Shape Atom} {p q : Wire a b} (root : Rewrite.Root p q) :
    constructors (expandRoot root) = constructorProfile root.code := by cases root <;> rfl

theorem rootProfile_exact {a b : Shape Atom} {p q : Wire a b} (root : Rewrite.Root p q) :
    roots (expandRoot root) = rootProfile root.code := by cases root <;> rfl

theorem constructors_bounded {a b : Shape Atom} {p q : Wire a b} (root : Rewrite.Root p q) :
    constructors (expandRoot root) ≤ 66 := by
  rw [constructorProfile_exact]
  cases root <;> simp [Rewrite.Root.code, constructorProfile]

theorem roots_bounded {a b : Shape Atom} {p q : Wire a b} (root : Rewrite.Root p q) :
    roots (expandRoot root) ≤ 20 := by
  rw [rootProfile_exact]
  cases root <;> simp [Rewrite.Root.code, rootProfile]

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.BoundedOld
