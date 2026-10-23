import Foundation.Crypto.Semantics.Probability.Facts
import Mathlib.Data.Finset.Lattice.Union

/-! Backwards observation dependencies for a finite diagram of probabilistic
state updates. Read/write interfaces are enforced by the action types: actions
receive only declared reads and return only declared writes. The checker does
not infer interfaces of opaque host functions. This is an ordinary slicing
baseline, not a higher-dimensional or proof-size separation theorem. -/
namespace CryptoOracle.StatefulDiagram
set_option backward.isDefEq.respectTransparency false
open Foundation.Probability
variable {Slot Op Value : Type} [DecidableEq Slot]

abbrev Store (Slot Value : Type) := Slot → Value

def view (scope : Finset Slot) (store : Store Slot Value) : scope → Value := fun slot => store slot

def write (scope : Finset Slot) (store : Store Slot Value) (values : scope → Value) : Store Slot Value :=
  fun slot => if member : slot ∈ scope then values ⟨slot, member⟩ else store slot

structure Interface (Slot : Type) where
  reads : Finset Slot
  writes : Finset Slot

/-- A world supplies one probabilistic local update for each operation. -/
abbrev Kernels (signature : Op → Interface Slot) (Value : Type) :=
  ∀ op, ((signature op).reads → Value) → PMF ((signature op).writes → Value)

noncomputable def step (signature : Op → Interface Slot) (world : Kernels signature Value)
    (op : Op) (store : Store Slot Value) : PMF (Store Slot Value) :=
  (world op (view (signature op).reads store)).map (write (signature op).writes store)

noncomputable def execute (signature : Op → Interface Slot) (world : Kernels signature Value) :
    List Op → Store Slot Value → PMF (Store Slot Value)
  | [], store => PMF.pure store
  | op :: rest, store => (step signature world op store).bind (execute signature world rest)

/-- Exact for the interface abstraction; not a claim of semantic minimality. -/
def neededBefore (signature : Op → Interface Slot) (op : Op) (needed : Finset Slot) : Finset Slot :=
  if Disjoint (signature op).writes needed then needed
  else (needed \ (signature op).writes) ∪ (signature op).reads

def dependencies (signature : Op → Interface Slot) : List Op → Finset Slot → Finset Slot
  | [], needed => needed
  | op :: rest, needed => neededBefore signature op (dependencies signature rest needed)

/-- Nodes with no path to the requested observation generate no local law. -/
def required [DecidableEq Op] (signature : Op → Interface Slot) : List Op → Finset Slot → Finset Op
  | [], _ => ∅
  | op :: rest, needed =>
      let tail := required signature rest needed
      let before := dependencies signature rest needed
      if Disjoint (signature op).writes before then tail else insert op tail

/-- A projected update depends only on the backwards-generated inputs. -/
theorem step_view (signature : Op → Interface Slot) (left right : Kernels signature Value)
    (op : Op) (needed : Finset Slot) (one two : Store Slot Value)
    (sameInputs : view (neededBefore signature op needed) one = view (neededBefore signature op needed) two)
    (sameAction : ¬ Disjoint (signature op).writes needed → left op = right op) :
    (step signature left op one).map (view needed) = (step signature right op two).map (view needed) := by
  classical
  by_cases irrelevant : Disjoint (signature op).writes needed
  · have same : view needed one = view needed two := by
      have needed_eq : neededBefore signature op needed = needed := if_pos irrelevant
      rw [needed_eq] at sameInputs
      exact sameInputs
    have unchanged (store : Store Slot Value) (values : (signature op).writes → Value) :
        view needed (write (signature op).writes store values) = view needed store := by
      funext slot
      have outside : (slot : Slot) ∉ (signature op).writes :=
        fun member => Finset.disjoint_left.mp irrelevant member slot.property
      simp only [view, write, dif_neg outside]
    simp only [step, PMF.map_comp, Function.comp_def, unchanged, same]
    change PMF.map (Function.const _ (view needed two)) _ = PMF.map (Function.const _ (view needed two)) _
    rw [PMF.map_const, PMF.map_const]
  · have readsSame : view (signature op).reads one = view (signature op).reads two := by
      funext slot
      exact congrFun sameInputs ⟨slot, by simp only [neededBefore, if_neg irrelevant]; exact Finset.mem_union_right _ slot.property⟩
    rw [step, step, sameAction irrelevant, readsSame, PMF.map_comp, PMF.map_comp]
    congr 1
    funext values
    funext slot
    change write (signature op).writes one values slot = write (signature op).writes two values slot
    by_cases member : (slot : Slot) ∈ (signature op).writes
    · simp only [write, dif_pos member]
    · simp only [write, dif_neg member]
      exact congrFun sameInputs ⟨slot, by
        simp only [neededBefore, if_neg irrelevant]
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨slot.property, member⟩)⟩

theorem view_write (scope : Finset Slot) (base : Store Slot Value) (values : scope → Value) :
    view scope (write scope base values) = values := by
  funext slot
  simp only [view, write, dif_pos slot.property]

/-- Generated local equality obligations suffice for the requested marginal,
even with arbitrary correlation in the input state and adaptive data values.
The operation list is fixed; actions may sample and depend on previous writes. -/
theorem execute_view [DecidableEq Op] (signature : Op → Interface Slot)
    (left right : Kernels signature Value) (diagram : List Op) (needed : Finset Slot)
    (one two : Store Slot Value)
    (sameInputs : view (dependencies signature diagram needed) one = view (dependencies signature diagram needed) two)
    (agree : ∀ op ∈ required signature diagram needed, left op = right op) :
    (execute signature left diagram one).map (view needed) =
      (execute signature right diagram two).map (view needed) := by
  induction diagram generalizing left right needed one two with
  | nil =>
      change view needed one = view needed two at sameInputs
      simpa only [execute, PMF.pure_map] using congrArg PMF.pure sameInputs
  | cons op rest ih =>
      let before := dependencies signature rest needed
      have tailAgree : ∀ node ∈ required signature rest needed, left node = right node := by
        intro node member
        apply agree node
        by_cases irrelevant : Disjoint (signature op).writes before
        · simpa only [required, before, if_pos irrelevant] using member
        · simp only [required]
          rw [if_neg irrelevant]
          exact Finset.mem_insert_of_mem member
      have actionAgree : ¬ Disjoint (signature op).writes before → left op = right op := by
        intro relevant
        apply agree op
        simp only [required]
        rw [if_neg relevant]
        exact Finset.mem_insert_self _ _
      have stepSame := step_view signature left right op before one two sameInputs actionAgree
      let continuation := fun values : before → Value =>
        (execute signature right rest (write before one values)).map (view needed)
      simp only [execute, PMF.map_bind]
      calc
        _ = (step signature left op one).bind (fun store => continuation (view before store)) := by
          congr 1
          funext store
          apply ih left right needed store (write before one (view before store))
          · exact (view_write before one _).symm
          · exact tailAgree
        _ = ((step signature left op one).map (view before)).bind continuation := by simp only [PMF.bind_map, Function.comp_def]
        _ = ((step signature right op two).map (view before)).bind continuation := by rw [stepSame]
        _ = (step signature right op two).bind (fun store => continuation (view before store)) := by simp only [PMF.bind_map, Function.comp_def]
        _ = _ := by
          congr 1
          funext store
          apply ih right right needed (write before one (view before store)) store
          · exact view_write before one _
          · intro node member; rfl

/-- Only changed operations that influence the observation need fresh laws. -/
def obligations [DecidableEq Op] (signature : Op → Interface Slot) (diagram : List Op)
    (needed : Finset Slot) (changed : Finset Op) : Finset Op := required signature diagram needed ∩ changed

theorem obligations_subset_changed [DecidableEq Op] (signature : Op → Interface Slot) (diagram : List Op)
    (needed : Finset Slot) (changed : Finset Op) : obligations signature diagram needed changed ⊆ changed :=
  Finset.inter_subset_right

/-- Runtime criterion for reuse with no fresh local equality proof. -/
def checkReuse [DecidableEq Op] (signature : Op → Interface Slot) (diagram : List Op)
    (needed : Finset Slot) (changed : Finset Op) : Bool := decide (obligations signature diagram needed changed = ∅)

/-- The extracted conditions, combined with the unchanged-operation proofs,
produce a complete observed-game equality. No semantic minimality is claimed. -/
theorem repair_sound [DecidableEq Op] (signature : Op → Interface Slot)
    (left right : Kernels signature Value) (diagram : List Op) (needed : Finset Slot)
    (changed : Finset Op) (store : Store Slot Value)
    (unchanged : ∀ op ∉ changed, left op = right op)
    (repaired : ∀ op ∈ obligations signature diagram needed changed, left op = right op) :
    (execute signature left diagram store).map (view needed) =
      (execute signature right diagram store).map (view needed) := by
  apply execute_view signature left right diagram needed store store rfl
  intro op member
  by_cases edited : op ∈ changed
  · exact repaired op (Finset.mem_inter.mpr ⟨member, edited⟩)
  · exact unchanged op edited

theorem checkReuse_sound [DecidableEq Op] (signature : Op → Interface Slot)
    (left right : Kernels signature Value) (diagram : List Op) (needed : Finset Slot)
    (changed : Finset Op) (store : Store Slot Value)
    (unchanged : ∀ op ∉ changed, left op = right op)
    (accepted : checkReuse signature diagram needed changed = true) :
    (execute signature left diagram store).map (view needed) =
      (execute signature right diagram store).map (view needed) := by
  apply repair_sound signature left right diagram needed changed store unchanged
  intro op member
  have empty : obligations signature diagram needed changed = ∅ := by
    exact of_decide_eq_true accepted
  rw [empty] at member
  simp only [Finset.notMem_empty] at member

/-- Lift the repaired marginal to any common, arbitrarily correlated initial
store law. No independence between registers is assumed. -/
theorem repair_mixture_sound [DecidableEq Op] (signature : Op → Interface Slot)
    (left right : Kernels signature Value) (diagram : List Op) (needed : Finset Slot)
    (changed : Finset Op) (initial : PMF (Store Slot Value))
    (unchanged : ∀ op ∉ changed, left op = right op)
    (repaired : ∀ op ∈ obligations signature diagram needed changed, left op = right op) :
    (initial.bind (execute signature left diagram)).map (view needed) =
      (initial.bind (execute signature right diagram)).map (view needed) := by
  simp only [PMF.map_bind]
  congr 1
  funext store
  exact repair_sound signature left right diagram needed changed store unchanged repaired

end CryptoOracle.StatefulDiagram
