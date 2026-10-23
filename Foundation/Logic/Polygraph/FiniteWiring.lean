import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi

/-! Primitive finite-product wiring, with an explicit finite equational basis.
Only routing is represented: no opaque operation boxes or stochastic kernels.
The eight root schemata are ordinary local product/monoidal equations. A
recursive normalizer constructs their pasting; reconstruction of a whole
circuit is NOT a primitive rule. Completeness below concerns paths of equations,
not higher coherence between those paths. -/
namespace Foundation.Logic.Polygraph.FiniteWiring

inductive Circuit : Nat → Nat → Type where
  | identity (n) : Circuit n n
  | select {n} (index : Fin n) : Circuit n 1
  | tuple {n m} : (Fin m → Circuit n 1) → Circuit n m
  | seq {n m k} : Circuit n m → Circuit m k → Circuit n k
  | tensor {n m n' m'} : Circuit n m → Circuit n' m' → Circuit (n + n') (m + m')

def Circuit.routing : {n m : Nat} → Circuit n m → Fin m → Fin n
  | _, _, .identity _, index => index
  | _, _, .select index, _ => index
  | _, _, .tuple children, index => (children index).routing 0
  | _, _, .seq first second, index => first.routing (second.routing index)
  | _, _, .tensor (n := n) (n' := n') first second, index =>
      Fin.addCases (fun i => Fin.castAdd n' (first.routing i)) (fun i => Fin.natAdd n (second.routing i)) index

def normal {n m : Nat} (routing : Fin m → Fin n) : Circuit n m := .tuple (fun index => .select (routing index))
def left (n n' : Nat) : Circuit (n + n') n := normal (Fin.castAdd n')
def right (n n' : Nat) : Circuit (n + n') n' := normal (Fin.natAdd n)

def expanded {n m n' m' : Nat} (first : Circuit n m) (second : Circuit n' m') : Circuit (n + n') (m + m') :=
  .tuple (Fin.addCases
    (fun index => .seq (.seq (left n n') first) (.select index))
    (fun index => .seq (.seq (right n n') second) (.select index)))

inductive Cell : {n m : Nat} → Circuit n m → Circuit n m → Type where
  | refl {n m} (circuit : Circuit n m) : Cell circuit circuit
  | symm {n m} {first second : Circuit n m} : Cell first second → Cell second first
  | trans {n m} {first second third : Circuit n m} : Cell first second → Cell second third → Cell first third
  | seq {n m k} {first first' : Circuit n m} {second second' : Circuit m k} :
      Cell first first' → Cell second second' → Cell (.seq first second) (.seq first' second')
  | tuple {n m} {first second : Fin m → Circuit n 1} :
      (∀ index, Cell (first index) (second index)) → Cell (.tuple first) (.tuple second)
  | tensor {n m n' m'} {first first' : Circuit n m} {second second' : Circuit n' m'} :
      Cell first first' → Cell second second' → Cell (.tensor first second) (.tensor first' second')
  | seqAssoc {n m k l} (first : Circuit n m) (second : Circuit m k) (third : Circuit k l) :
      Cell (.seq (.seq first second) third) (.seq first (.seq second third))
  | seqLeftUnit {n m} (circuit : Circuit n m) : Cell (.seq (.identity n) circuit) circuit
  | seqRightUnit {n m} (circuit : Circuit n m) : Cell (.seq circuit (.identity m)) circuit
  | beta {n m} (children : Fin m → Circuit n 1) (index : Fin m) :
      Cell (.seq (.tuple children) (.select index)) (children index)
  | eta {n m} (circuit : Circuit n m) :
      Cell (.tuple (fun index => .seq circuit (.select index))) circuit
  | singleton {n} (children : Fin 1 → Circuit n 1) : Cell (.tuple children) (children 0)
  | seqTuple {n m k} (first : Circuit n m) (children : Fin k → Circuit m 1) :
      Cell (.seq first (.tuple children)) (.tuple (fun index => .seq first (children index)))
  | tensorExpand {n m n' m'} (first : Circuit n m) (second : Circuit n' m') :
      Cell (.tensor first second) (expanded first second)

/-- Count root-equation occurrences in the expanded witness tree. This is
not a kernel-byte count, a shared-DAG count, or a minimal proof-size metric. -/
def Cell.steps : {n m : Nat} → {first second : Circuit n m} → Cell first second → Nat
  | _, _, _, _, .refl _ => 0
  | _, _, _, _, .symm cell => cell.steps
  | _, _, _, _, .trans first second => first.steps + second.steps
  | _, _, _, _, .seq first second => first.steps + second.steps
  | _, _, _, _, .tuple cells => (List.ofFn (fun index => (cells index).steps)).sum
  | _, _, _, _, .tensor first second => first.steps + second.steps
  | _, _, _, _, _ => 1

theorem Cell.routing_eq {n m : Nat} {first second : Circuit n m} (cell : Cell first second) :
    first.routing = second.routing := by
  induction cell with
  | refl => rfl
  | symm cell ih => exact ih.symm
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond
  | seq first second ihFirst ihSecond => funext index; simp only [Circuit.routing, ihFirst, ihSecond]
  | tuple cells ih => funext index; exact congrFun (ih index) 0
  | tensor first second ihFirst ihSecond =>
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro i; simp only [Circuit.routing, Fin.addCases_left, ihFirst]
    · intro i; simp only [Circuit.routing, Fin.addCases_right, ihSecond]
  | seqAssoc => rfl
  | seqLeftUnit => rfl
  | seqRightUnit => rfl
  | beta children index =>
    funext i
    have same : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  | eta => rfl
  | singleton children =>
    funext i
    have same : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  | seqTuple => rfl
  | tensorExpand first second =>
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro i; simp only [Circuit.routing, expanded, Fin.addCases_left, left, normal]
    · intro i; simp only [Circuit.routing, expanded, Fin.addCases_right, right, normal]

def identityNormal (n : Nat) : Cell (.identity n) (normal (id : Fin n → Fin n)) :=
  (Cell.eta (.identity n)).symm.trans (.tuple (fun index => .seqLeftUnit (.select index)))

def seqNormal {n m k : Nat} (first : Fin m → Fin n) (second : Fin k → Fin m) :
    Cell (.seq (normal first) (normal second)) (normal (first ∘ second)) :=
  (Cell.seqTuple (normal first) (fun index => .select (second index))).trans
    (.tuple (fun index => .beta (fun middle => .select (first middle)) (second index)))

def tensorNormal {n m n' m' : Nat} (first : Circuit n m) (second : Circuit n' m')
    (one : Cell first (normal first.routing)) (two : Cell second (normal second.routing)) :
    Cell (.tensor first second) (normal (Circuit.routing (.tensor first second))) := by
  apply Cell.trans (.tensorExpand first second)
  apply Cell.tuple
  intro index
  refine Fin.addCases ?_ ?_ index
  · intro i
    simp only [Circuit.routing, Fin.addCases_left]
    exact (Cell.seq (.seq (.refl (left n n')) one) (.refl (.select i))).trans
      ((Cell.seq (seqNormal (Fin.castAdd n') first.routing) (.refl (.select i))).trans
        (.beta (fun middle => .select (Fin.castAdd n' (first.routing middle))) i))
  · intro i
    simp only [Circuit.routing, Fin.addCases_right]
    exact (Cell.seq (.seq (.refl (right n n')) two) (.refl (.select i))).trans
      ((Cell.seq (seqNormal (Fin.natAdd n) second.routing) (.refl (.select i))).trans
        (.beta (fun middle => .select (Fin.natAdd n (second.routing middle))) i))

/-- The proof-producing normalizer is recursive on the actual constructors.
Its result consists solely of the eight root schemata and context closure. -/
def normalize : {n m : Nat} → (circuit : Circuit n m) → Cell circuit (normal circuit.routing)
  | _, _, .identity n => identityNormal n
  | _, _, .select index => (Cell.singleton (fun _ => .select index)).symm
  | _, _, .tuple children => .tuple (fun index =>
      (normalize (children index)).trans (.singleton (fun i => .select ((children index).routing i))))
  | _, _, .seq first second =>
      (Cell.seq (normalize first) (normalize second)).trans (seqNormal first.routing second.routing)
  | _, _, .tensor first second => tensorNormal first second (normalize first) (normalize second)

/-- Equality of normal routing functions chooses endpoint casts only; it is
not a primitive cell. All substantive proof steps come from normalize. -/
def connect {n m : Nat} (first second : Circuit n m) (same : first.routing = second.routing) : Cell first second := by
  have converted : Cell first (normal second.routing) := by
    rw [← same]
    exact normalize first
  exact converted.trans (normalize second).symm

theorem complete {n m : Nat} (first second : Circuit n m) :
    Nonempty (Cell first second) ↔ first.routing = second.routing := by
  constructor
  · rintro ⟨cell⟩
    exact cell.routing_eq
  · intro same
    exact ⟨connect first second same⟩

def synthesize {n m : Nat} (first second : Circuit n m) : Option (Cell first second) :=
  if same : first.routing = second.routing then some (connect first second same) else none

theorem synthesize_complete {n m : Nat} (first second : Circuit n m) :
    (synthesize first second).isSome = true ↔ Nonempty (Cell first second) := by
  rw [complete]
  unfold synthesize
  split <;> simp_all

def Circuit.eval {A : Type} : {n m : Nat} → Circuit n m → (Fin n → A) → Fin m → A
  | _, _, .identity _, environment, index => environment index
  | _, _, .select selected, environment, _ => environment selected
  | _, _, .tuple children, environment, index => (children index).eval environment 0
  | _, _, .seq first second, environment, index => second.eval (first.eval environment) index
  | _, _, .tensor (n := n) (n' := n') first second, environment, index =>
      Fin.addCases (first.eval (fun i => environment (Fin.castAdd n' i)))
        (second.eval (fun i => environment (Fin.natAdd n i))) index

theorem Circuit.eval_routing {A : Type} {n m : Nat} (circuit : Circuit n m) (environment : Fin n → A) (index : Fin m) :
    circuit.eval environment index = environment (circuit.routing index) := by
  induction circuit with
  | identity => rfl
  | select => rfl
  | tuple children ih => exact ih index environment 0
  | seq first second one two =>
    rw [Circuit.eval, two, one]
    rfl
  | tensor first second one two =>
    refine Fin.addCases ?_ ?_ index
    · intro i; simp only [Circuit.eval, Circuit.routing, Fin.addCases_left, one]
    · intro i; simp only [Circuit.eval, Circuit.routing, Fin.addCases_right, two]

theorem Cell.sound {A : Type} {n m : Nat} {first second : Circuit n m} (cell : Cell first second)
    (environment : Fin n → A) : first.eval environment = second.eval environment := by
  funext index
  rw [Circuit.eval_routing, Circuit.eval_routing, cell.routing_eq]

theorem all_models_iff {n m : Nat} (first second : Circuit n m) :
    (∀ (A : Type) (environment : Fin n → A), first.eval environment = second.eval environment) ↔
      Nonempty (Cell first second) := by
  constructor
  · intro equal
    apply (complete first second).mpr
    funext index
    have observed := congrFun (equal (Fin n) id) index
    simpa only [Circuit.eval_routing, id_eq] using observed
  · rintro ⟨cell⟩ A environment
    exact cell.sound environment

end Foundation.Logic.Polygraph.FiniteWiring
