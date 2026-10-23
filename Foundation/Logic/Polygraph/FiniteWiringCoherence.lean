import Foundation.Logic.Polygraph.FiniteWiring

/-! A normalization-relative higher completion of the eight-rule wiring
calculus. Eight root-square forms and three constructor
naturality forms suffice. Generators refer to the FIXED recursive normalizer,
never arbitrary supplied paths. They can expand with their term parameters:
this is NOT a bounded critical-overlap presentation or a size bound. -/
namespace Foundation.Logic.Polygraph.FiniteWiring.Higher

def normalAt {n m : Nat} (routing : Fin m → Fin n) (circuit : Circuit n m)
    (same : circuit.routing = routing) : Cell circuit (normal routing) := same ▸ normalize circuit

inductive Root : {n m : Nat} → Circuit n m → Circuit n m → Type where
  | seqAssoc {n m k l} (first : Circuit n m) (second : Circuit m k) (third : Circuit k l) :
      Root (.seq (.seq first second) third) (.seq first (.seq second third))
  | seqLeftUnit {n m} (circuit : Circuit n m) : Root (.seq (.identity n) circuit) circuit
  | seqRightUnit {n m} (circuit : Circuit n m) : Root (.seq circuit (.identity m)) circuit
  | beta {n m} (children : Fin m → Circuit n 1) (index : Fin m) :
      Root (.seq (.tuple children) (.select index)) (children index)
  | eta {n m} (circuit : Circuit n m) : Root (.tuple (fun index => .seq circuit (.select index))) circuit
  | singleton {n} (children : Fin 1 → Circuit n 1) : Root (.tuple children) (children 0)
  | seqTuple {n m k} (first : Circuit n m) (children : Fin k → Circuit m 1) :
      Root (.seq first (.tuple children)) (.tuple (fun index => .seq first (children index)))
  | tensorExpand {n m n' m'} (first : Circuit n m) (second : Circuit n' m') :
      Root (.tensor first second) (expanded first second)

def Root.cell : {n m : Nat} → {first second : Circuit n m} → Root first second → Cell first second
  | _, _, _, _, .seqAssoc first second third => .seqAssoc first second third
  | _, _, _, _, .seqLeftUnit circuit => .seqLeftUnit circuit
  | _, _, _, _, .seqRightUnit circuit => .seqRightUnit circuit
  | _, _, _, _, .beta children index => .beta children index
  | _, _, _, _, .eta circuit => .eta circuit
  | _, _, _, _, .singleton children => .singleton children
  | _, _, _, _, .seqTuple first children => .seqTuple first children
  | _, _, _, _, .tensorExpand first second => .tensorExpand first second

def tensorRouting {n m n' m' : Nat} (first : Fin m → Fin n) (second : Fin m' → Fin n') :
    Fin (m + m') → Fin (n + n') :=
  Fin.addCases (fun index => Fin.castAdd n' (first index)) (fun index => Fin.natAdd n (second index))

def tupleRouting {n m : Nat} (routes : Fin m → Fin 1 → Fin n) : Fin m → Fin n := fun index => routes index 0

theorem seqRouting {n m k : Nat} {first : Circuit n m} {second : Circuit m k}
    {one : Fin m → Fin n} {two : Fin k → Fin m} (hOne : first.routing = one) (hTwo : second.routing = two) :
    (Circuit.seq first second).routing = one ∘ two := by
  funext index
  change first.routing (second.routing index) = one (two index)
  rw [hOne, hTwo]

theorem tensorRouting_eq {n m n' m' : Nat} {first : Circuit n m} {second : Circuit n' m'}
    {one : Fin m → Fin n} {two : Fin m' → Fin n'} (hOne : first.routing = one) (hTwo : second.routing = two) :
    (Circuit.tensor first second).routing = tensorRouting one two := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro i; simp only [Circuit.routing, tensorRouting, Fin.addCases_left, hOne]
  · intro i; simp only [Circuit.routing, tensorRouting, Fin.addCases_right, hTwo]

theorem tupleRouting_eq {n m : Nat} {children : Fin m → Circuit n 1} {routes : Fin m → Fin 1 → Fin n}
    (same : ∀ index, (children index).routing = routes index) :
    (Circuit.tuple children).routing = tupleRouting routes := by
  funext index
  exact congrFun (same index) 0

/-- Eleven schematic forms after expanding the eight cases of Root. No
constructor is indexed by an arbitrary Cell/step or by an arbitrary loop. -/
inductive Generator : {n m : Nat} → {first second : Circuit n m} → Cell first second → Cell first second → Type where
  | root {n m} {first second : Circuit n m} (step : Root first second)
      (routing : Fin m → Fin n) (same : first.routing = routing) :
      Generator (.trans step.cell (normalAt routing second (step.cell.routing_eq.symm.trans same)))
        (normalAt routing first same)
  | seqNormal {n m k} (one : Fin m → Fin n) (two : Fin k → Fin m)
      (first : Circuit n m) (second : Circuit m k) (hOne : first.routing = one) (hTwo : second.routing = two) :
      Generator (.trans (.seq (normalAt one first hOne) (normalAt two second hTwo))
        (normalAt (one ∘ two) (.seq (normal one) (normal two)) rfl))
        (normalAt (one ∘ two) (.seq first second) (seqRouting hOne hTwo))
  | tensorNormal {n m n' m'} (one : Fin m → Fin n) (two : Fin m' → Fin n')
      (first : Circuit n m) (second : Circuit n' m') (hOne : first.routing = one) (hTwo : second.routing = two) :
      Generator (.trans (.tensor (normalAt one first hOne) (normalAt two second hTwo))
        (normalAt (tensorRouting one two) (.tensor (normal one) (normal two)) rfl))
        (normalAt (tensorRouting one two) (.tensor first second) (tensorRouting_eq hOne hTwo))
  | tupleNormal {n m} (routes : Fin m → Fin 1 → Fin n) (children : Fin m → Circuit n 1)
      (same : ∀ index, (children index).routing = routes index) :
      Generator (.trans (.tuple (fun index => normalAt (routes index) (children index) (same index)))
        (normalAt (tupleRouting routes) (.tuple (fun index => normal (routes index))) rfl))
        (normalAt (tupleRouting routes) (.tuple children) (tupleRouting_eq same))

def Root.code : {n m : Nat} → {first second : Circuit n m} → Root first second → Fin 8
  | _, _, _, _, .seqAssoc _ _ _ => 0
  | _, _, _, _, .seqLeftUnit _ => 1
  | _, _, _, _, .seqRightUnit _ => 2
  | _, _, _, _, .beta _ _ => 3
  | _, _, _, _, .eta _ => 4
  | _, _, _, _, .singleton _ => 5
  | _, _, _, _, .seqTuple _ _ => 6
  | _, _, _, _, .tensorExpand _ _ => 7

def Generator.code : {n m : Nat} → {first second : Circuit n m} →
    {one two : Cell first second} → Generator one two → Fin 11
  | _, _, _, _, _, _, .root step _ _ => Fin.castAdd 3 step.code
  | _, _, _, _, _, _, .seqNormal _ _ _ _ _ _ => 8
  | _, _, _, _, _, _, .tensorNormal _ _ _ _ _ _ => 9
  | _, _, _, _, _, _, .tupleNormal _ _ _ => 10

/-- Structural proof-groupoid and congruence functor laws. They do not
identify arbitrary primitive diagrams by equality of their interpretation. -/
inductive Law : {n m : Nat} → {first second : Circuit n m} → Cell first second → Cell first second → Type where
  | assoc {n m} {a b c d : Circuit n m} (p : Cell a b) (q : Cell b c) (r : Cell c d) :
      Law (.trans (.trans p q) r) (.trans p (.trans q r))
  | leftUnit {n m} {a b : Circuit n m} (p : Cell a b) : Law (.trans (.refl a) p) p
  | rightUnit {n m} {a b : Circuit n m} (p : Cell a b) : Law (.trans p (.refl b)) p
  | leftInv {n m} {a b : Circuit n m} (p : Cell a b) : Law (.trans (.symm p) p) (.refl b)
  | rightInv {n m} {a b : Circuit n m} (p : Cell a b) : Law (.trans p (.symm p)) (.refl a)
  | seqComp {n m k} {a b c : Circuit n m} {d e f : Circuit m k}
      (p : Cell a b) (q : Cell b c) (r : Cell d e) (s : Cell e f) :
      Law (.trans (.seq p r) (.seq q s)) (.seq (.trans p q) (.trans r s))
  | tensorComp {n m n' m'} {a b c : Circuit n m} {d e f : Circuit n' m'}
      (p : Cell a b) (q : Cell b c) (r : Cell d e) (s : Cell e f) :
      Law (.trans (.tensor p r) (.tensor q s)) (.tensor (.trans p q) (.trans r s))
  | tupleComp {n m} {a b c : Fin m → Circuit n 1} (p : ∀ index, Cell (a index) (b index))
      (q : ∀ index, Cell (b index) (c index)) :
      Law (.trans (.tuple p) (.tuple q)) (.tuple (fun index => .trans (p index) (q index)))

def Law.code : {n m : Nat} → {first second : Circuit n m} →
    {one two : Cell first second} → Law one two → Fin 8
  | _, _, _, _, _, _, .assoc _ _ _ => 0
  | _, _, _, _, _, _, .leftUnit _ => 1
  | _, _, _, _, _, _, .rightUnit _ => 2
  | _, _, _, _, _, _, .leftInv _ => 3
  | _, _, _, _, _, _, .rightInv _ => 4
  | _, _, _, _, _, _, .seqComp _ _ _ _ => 5
  | _, _, _, _, _, _, .tensorComp _ _ _ _ => 6
  | _, _, _, _, _, _, .tupleComp _ _ => 7

inductive Four : {n m : Nat} → {first second : Circuit n m} → Cell first second → Cell first second → Type where
  | refl {n m} {first second : Circuit n m} (cell : Cell first second) : Four cell cell
  | generator {n m} {first second : Circuit n m} {one two : Cell first second} : Generator one two → Four one two
  | law {n m} {first second : Circuit n m} {one two : Cell first second} : Law one two → Four one two
  | symm {n m} {first second : Circuit n m} {one two : Cell first second} : Four one two → Four two one
  | trans {n m} {first second : Circuit n m} {one two three : Cell first second} :
      Four one two → Four two three → Four one three
  | comp {n m} {a b c : Circuit n m} {p p' : Cell a b} {q q' : Cell b c} :
      Four p p' → Four q q' → Four (.trans p q) (.trans p' q')
  | inverse {n m} {a b : Circuit n m} {p q : Cell a b} : Four p q → Four (.symm p) (.symm q)
  | seq {n m k} {a b : Circuit n m} {c d : Circuit m k} {p p' : Cell a b} {q q' : Cell c d} :
      Four p p' → Four q q' → Four (.seq p q) (.seq p' q')
  | tensor {n m n' m'} {a b : Circuit n m} {c d : Circuit n' m'} {p p' : Cell a b} {q q' : Cell c d} :
      Four p p' → Four q q' → Four (.tensor p q) (.tensor p' q')
  | tuple {n m} {first second : Fin m → Circuit n 1} {p q : ∀ index, Cell (first index) (second index)} :
      (∀ index, Four (p index) (q index)) → Four (.tuple p) (.tuple q)

namespace Four

def assoc {n m} {a b c d : Circuit n m} (p : Cell a b) (q : Cell b c) (r : Cell c d) :
    Four (.trans (.trans p q) r) (.trans p (.trans q r)) := .law (.assoc p q r)
def leftUnit {n m} {a b : Circuit n m} (p : Cell a b) : Four (.trans (.refl a) p) p := .law (.leftUnit p)
def rightUnit {n m} {a b : Circuit n m} (p : Cell a b) : Four (.trans p (.refl b)) p := .law (.rightUnit p)
def leftInv {n m} {a b : Circuit n m} (p : Cell a b) : Four (.trans (.symm p) p) (.refl b) := .law (.leftInv p)
def rightInv {n m} {a b : Circuit n m} (p : Cell a b) : Four (.trans p (.symm p)) (.refl a) := .law (.rightInv p)

end Four

/-- Contract a sequential context using only its constructor square,
functoriality, and the supplied recursively constructed child contractions. -/
def seqContract {n m k} {a b : Circuit n m} {c d : Circuit m k} (p : Cell a b) (q : Cell c d)
    (one : Four (.trans p (normalAt a.routing b p.routing_eq.symm)) (normalAt a.routing a rfl))
    (two : Four (.trans q (normalAt c.routing d q.routing_eq.symm)) (normalAt c.routing c rfl)) :
    Four (.trans (.seq p q) (normalAt (a.routing ∘ c.routing) (.seq b d)
      (seqRouting p.routing_eq.symm q.routing_eq.symm)))
      (normalAt (a.routing ∘ c.routing) (.seq a c) rfl) :=
  (Four.comp (.refl (.seq p q))
    (Four.generator (.seqNormal a.routing c.routing b d p.routing_eq.symm q.routing_eq.symm)).symm).trans
  ((Four.assoc (.seq p q) _ _).symm.trans
    ((Four.comp (.law (.seqComp p _ q _)) (.refl _)).trans
      ((Four.comp (.seq one two) (.refl _)).trans
        (.generator (.seqNormal a.routing c.routing a c rfl rfl)))))

def tensorContract {n m n' m'} {a b : Circuit n m} {c d : Circuit n' m'} (p : Cell a b) (q : Cell c d)
    (one : Four (.trans p (normalAt a.routing b p.routing_eq.symm)) (normalAt a.routing a rfl))
    (two : Four (.trans q (normalAt c.routing d q.routing_eq.symm)) (normalAt c.routing c rfl)) :
    Four (.trans (.tensor p q) (normalAt (tensorRouting a.routing c.routing) (.tensor b d)
      (tensorRouting_eq p.routing_eq.symm q.routing_eq.symm)))
      (normalAt (tensorRouting a.routing c.routing) (.tensor a c) rfl) :=
  (Four.comp (.refl (.tensor p q))
    (Four.generator (.tensorNormal a.routing c.routing b d p.routing_eq.symm q.routing_eq.symm)).symm).trans
  ((Four.assoc (.tensor p q) _ _).symm.trans
    ((Four.comp (.law (.tensorComp p _ q _)) (.refl _)).trans
      ((Four.comp (.tensor one two) (.refl _)).trans
        (.generator (.tensorNormal a.routing c.routing a c rfl rfl)))))

def tupleContract {n m} {first second : Fin m → Circuit n 1} (cells : ∀ index, Cell (first index) (second index))
    (children : ∀ index, Four (.trans (cells index)
      (normalAt (first index).routing (second index) (cells index).routing_eq.symm))
      (normalAt (first index).routing (first index) rfl)) :
    Four (.trans (.tuple cells) (normalAt (tupleRouting (fun index => (first index).routing)) (.tuple second)
      (tupleRouting_eq (fun index => (cells index).routing_eq.symm))))
      (normalAt (tupleRouting (fun index => (first index).routing)) (.tuple first) rfl) :=
  (Four.comp (.refl (.tuple cells))
    (Four.generator (.tupleNormal (fun index => (first index).routing) second (fun index => (cells index).routing_eq.symm))).symm).trans
  ((Four.assoc (.tuple cells) _ _).symm.trans
    ((Four.comp (.law (.tupleComp cells _)) (.refl _)).trans
      ((Four.comp (.tuple children) (.refl _)).trans
        (.generator (.tupleNormal (fun index => (first index).routing) first (fun _ => rfl))))))

/-- All Cell constructors, including simultaneous tuple/seq/tensor
congruences, are handled recursively. Root squares are not indexed by Cell. -/
def contract : {n m : Nat} → {first second : Circuit n m} → (cell : Cell first second) →
    (routing : Fin m → Fin n) → (one : first.routing = routing) → (two : second.routing = routing) →
    Four (.trans cell (normalAt routing second two)) (normalAt routing first one)
  | _, _, _, _, .refl _, _, _, _ => .leftUnit _
  | _, _, _, _, .symm cell, routing, one, two =>
      (Four.comp (.refl (.symm cell)) (contract cell routing two one).symm).trans
        ((Four.assoc (.symm cell) cell _).symm.trans
          ((Four.comp (.leftInv cell) (.refl _)).trans (.leftUnit _)))
  | _, _, _, _, .trans first second, routing, one, two =>
      (Four.assoc first second _).trans
        ((Four.comp (.refl first) (contract second routing (first.routing_eq.symm.trans one) two)).trans
          (contract first routing one (first.routing_eq.symm.trans one)))
  | _, _, _, _, .seq first second, routing, one, two => by
      cases one
      exact seqContract first second (contract first _ rfl first.routing_eq.symm) (contract second _ rfl second.routing_eq.symm)
  | _, _, _, _, .tensor first second, routing, one, two => by
      cases one
      exact tensorContract first second (contract first _ rfl first.routing_eq.symm) (contract second _ rfl second.routing_eq.symm)
  | _, _, _, _, .tuple cells, routing, one, two => by
      cases one
      exact tupleContract cells (fun index => contract (cells index) _ rfl (cells index).routing_eq.symm)
  | _, _, _, _, .seqAssoc first second third, routing, one, _ => .generator (.root (.seqAssoc first second third) routing one)
  | _, _, _, _, .seqLeftUnit circuit, routing, one, _ => .generator (.root (.seqLeftUnit circuit) routing one)
  | _, _, _, _, .seqRightUnit circuit, routing, one, _ => .generator (.root (.seqRightUnit circuit) routing one)
  | _, _, _, _, .beta children index, routing, one, _ => .generator (.root (.beta children index) routing one)
  | _, _, _, _, .eta circuit, routing, one, _ => .generator (.root (.eta circuit) routing one)
  | _, _, _, _, .singleton children, routing, one, _ => .generator (.root (.singleton children) routing one)
  | _, _, _, _, .seqTuple circuit children, routing, one, _ => .generator (.root (.seqTuple circuit children) routing one)
  | _, _, _, _, .tensorExpand first second, routing, one, _ => .generator (.root (.tensorExpand first second) routing one)

def factor {n m} {first second : Circuit n m} (cell : Cell first second)
    (routing : Fin m → Fin n) (one : first.routing = routing) (two : second.routing = routing) :
    Four cell (.trans (normalAt routing first one) (.symm (normalAt routing second two))) :=
  (Four.rightUnit cell).symm.trans
    ((Four.comp (.refl cell) (Four.rightInv (normalAt routing second two)).symm).trans
      ((Four.assoc cell _ _).symm.trans
        (Four.comp (contract cell routing one two) (.refl _))))

/-- An explicit higher diagram between every parallel pair. This is data in
Type, not proof irrelevance or a generator for arbitrary parallel paths. -/
def coherent {n m} {first second : Circuit n m} (one two : Cell first second) : Four one two :=
  (factor one first.routing rfl one.routing_eq.symm).trans
    (factor two first.routing rfl one.routing_eq.symm).symm

/-- Normal loops need no additional generator; they are a derived case. -/
def normalLoop {n m} (routing : Fin m → Fin n) :
    Four (normalAt routing (normal routing) rfl) (.refl (normal routing)) := coherent _ _

def seqIdentity {n m k} (first : Circuit n m) (second : Circuit m k) :
    Four (.seq (.refl first) (.refl second)) (.refl (.seq first second)) := coherent _ _

def tensorIdentity {n m n' m'} (first : Circuit n m) (second : Circuit n' m') :
    Four (.tensor (.refl first) (.refl second)) (.refl (.tensor first second)) := coherent _ _

def tupleIdentity {n m} (children : Fin m → Circuit n 1) :
    Four (.tuple (fun index => .refl (children index))) (.refl (.tuple children)) := coherent _ _

/-- Horizontal interchange is already derivable from structural functor laws
and groupoid units; no normalization-square generator is needed here. -/
def tensorInterchange {n m n' m'} {a b : Circuit n m} {c d : Circuit n' m'}
    (one : Cell a b) (two : Cell c d) :
    Four (.trans (.tensor one (.refl c)) (.tensor (.refl b) two))
      (.trans (.tensor (.refl a) two) (.tensor one (.refl d))) :=
  ((Four.law (.tensorComp one (.refl b) (.refl c) two)).trans
    (Four.tensor (.rightUnit one) (.leftUnit two))).trans
  ((Four.law (.tensorComp (.refl a) one two (.refl d))).trans
    (Four.tensor (.leftUnit one) (.rightUnit two))).symm

/-- Count normalization-relative generator occurrences, NOT the primitive
cells inside their potentially large boundary paths or shared-DAG size. -/
def Four.generatorCount : {n m : Nat} → {first second : Circuit n m} →
    {one two : Cell first second} → Four one two → Nat
  | _, _, _, _, _, _, .refl _ => 0
  | _, _, _, _, _, _, .generator _ => 1
  | _, _, _, _, _, _, .law _ => 0
  | _, _, _, _, _, _, .symm proof => proof.generatorCount
  | _, _, _, _, _, _, .trans first second => first.generatorCount + second.generatorCount
  | _, _, _, _, _, _, .comp first second => first.generatorCount + second.generatorCount
  | _, _, _, _, _, _, .inverse proof => proof.generatorCount
  | _, _, _, _, _, _, .seq first second => first.generatorCount + second.generatorCount
  | _, _, _, _, _, _, .tensor first second => first.generatorCount + second.generatorCount
  | _, _, _, _, _, _, .tuple proofs => (List.ofFn (fun index => (proofs index).generatorCount)).sum

def Four.lawCount : {n m : Nat} → {first second : Circuit n m} →
    {one two : Cell first second} → Four one two → Nat
  | _, _, _, _, _, _, .refl _ => 0
  | _, _, _, _, _, _, .generator _ => 0
  | _, _, _, _, _, _, .law _ => 1
  | _, _, _, _, _, _, .symm proof => proof.lawCount
  | _, _, _, _, _, _, .trans first second => first.lawCount + second.lawCount
  | _, _, _, _, _, _, .comp first second => first.lawCount + second.lawCount
  | _, _, _, _, _, _, .inverse proof => proof.lawCount
  | _, _, _, _, _, _, .seq first second => first.lawCount + second.lawCount
  | _, _, _, _, _, _, .tensor first second => first.lawCount + second.lawCount
  | _, _, _, _, _, _, .tuple proofs => (List.ofFn (fun index => (proofs index).lawCount)).sum

end Foundation.Logic.Polygraph.FiniteWiring.Higher
