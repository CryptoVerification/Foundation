import Foundation.Crypto.Semantics.Oracle.StatefulDiagramAnalysisTransport

/-! Dependency support for reusing an OLD equivalence proof after kernel edits.
A semantic proof is an explicitly supplied imported lemma, not a new primitive
polygraph equation or an equality decision procedure. Its conservative support
is computed from BOTH endpoint analyses. Uniform checked exchanges need no
kernel-equality assumptions. -/
namespace CryptoOracle.StatefulDiagram
open Foundation.Probability
variable {Slot Op Value : Type} [DecidableEq Slot] [DecidableEq Op]

def equivalenceSupport (signature : Op → Interface Slot) (one two : List Op) (needed : Finset Slot) : Finset Op :=
  required signature one needed ∪ required signature two needed

theorem equivalence_transport (signature : Op → Interface Slot) (old updated : Kernels signature Value)
    (one two : List Op) (needed : Finset Slot)
    (same : ∀ store, (execute signature old one store).map (view needed) = (execute signature old two store).map (view needed))
    (agree : ∀ op ∈ equivalenceSupport signature one two needed, old op = updated op)
    (store : Store Slot Value) :
    (execute signature updated one store).map (view needed) = (execute signature updated two store).map (view needed) := by
  calc
    _ = (execute signature old one store).map (view needed) :=
      (execute_view signature old updated one needed store store rfl
        (fun op member => agree op (Finset.mem_union_left _ member))).symm
    _ = (execute signature old two store).map (view needed) := same store
    _ = _ := execute_view signature old updated two needed store store rfl
      (fun op member => agree op (Finset.mem_union_right _ member))

/-- Executable proof metadata, independent of the probabilistic kernels. -/
inductive ReusePlan (signature : Op → Interface Slot) (needed : Finset Slot) : List Op → List Op → Type where
  | checked {one two} (path : Exchange signature one two) : ReusePlan signature needed one two
  | imported (one two : List Op) : ReusePlan signature needed one two
  | symm {one two} : ReusePlan signature needed one two → ReusePlan signature needed two one
  | trans {one two three} : ReusePlan signature needed one two → ReusePlan signature needed two three →
      ReusePlan signature needed one three

def ReusePlan.support (signature : Op → Interface Slot) (needed : Finset Slot) :
    {one two : List Op} → ReusePlan signature needed one two → Finset Op
  | _, _, .checked _ => ∅
  | _, _, .imported one two => equivalenceSupport signature one two needed
  | _, _, .symm child => child.support signature needed
  | _, _, .trans first second => first.support signature needed ∪ second.support signature needed

def ReusePlan.Valid (signature : Op → Interface Slot) (needed : Finset Slot) (old : Kernels signature Value) :
    {one two : List Op} → ReusePlan signature needed one two → Prop
  | _, _, .checked _ => True
  | one, two, .imported _ _ => ∀ store,
      (execute signature old one store).map (view needed) = (execute signature old two store).map (view needed)
  | _, _, .symm child => child.Valid signature needed old
  | _, _, .trans first second => first.Valid signature needed old ∧ second.Valid signature needed old

/-- Imported semantic lemmas are explicit leaves, outside the primitive
exchange language. Runtime checking reads only plan, never evaluates a PMF. -/
structure ReuseCertificate (signature : Op → Interface Slot) (old : Kernels signature Value) (needed : Finset Slot)
    (one two : List Op) where
  plan : ReusePlan signature needed one two
  valid : plan.Valid signature needed old

def ReuseCertificate.checked {signature : Op → Interface Slot} {old : Kernels signature Value} {needed : Finset Slot}
    {one two : List Op} (path : Exchange signature one two) : ReuseCertificate signature old needed one two :=
  ⟨.checked path, True.intro⟩

def ReuseCertificate.imported {signature : Op → Interface Slot} {old : Kernels signature Value} {needed : Finset Slot}
    {one two : List Op} (law : ∀ store,
      (execute signature old one store).map (view needed) = (execute signature old two store).map (view needed)) :
    ReuseCertificate signature old needed one two := ⟨.imported one two, law⟩

def ReuseCertificate.symm {signature : Op → Interface Slot} {old : Kernels signature Value} {needed : Finset Slot}
    {one two : List Op} (certificate : ReuseCertificate signature old needed one two) :
    ReuseCertificate signature old needed two one := ⟨.symm certificate.plan, certificate.valid⟩

def ReuseCertificate.trans {signature : Op → Interface Slot} {old : Kernels signature Value} {needed : Finset Slot}
    {one two three : List Op} (first : ReuseCertificate signature old needed one two)
    (second : ReuseCertificate signature old needed two three) : ReuseCertificate signature old needed one three :=
  ⟨.trans first.plan second.plan, ⟨first.valid, second.valid⟩⟩

def ReuseCertificate.support (signature : Op → Interface Slot) (old : Kernels signature Value) (needed : Finset Slot)
    {one two : List Op} (certificate : ReuseCertificate signature old needed one two) : Finset Op :=
  certificate.plan.support signature needed

theorem ReusePlan.sound (signature : Op → Interface Slot) (needed : Finset Slot) {one two : List Op}
    (plan : ReusePlan signature needed one two) (old updated : Kernels signature Value)
    (valid : plan.Valid signature needed old)
    (agree : ∀ op ∈ plan.support signature needed, old op = updated op) (store : Store Slot Value) :
    (execute signature updated one store).map (view needed) = (execute signature updated two store).map (view needed) := by
  induction plan with
  | checked path => exact congrArg (PMF.map (view needed)) (path.sound signature updated store)
  | imported one two => exact equivalence_transport signature old updated one two needed valid agree store
  | symm child ih => exact (ih valid agree).symm
  | trans first second ihFirst ihSecond =>
      exact (ihFirst valid.1 (fun op member => agree op (Finset.mem_union_left _ member))).trans
        (ihSecond valid.2 (fun op member => agree op (Finset.mem_union_right _ member)))

theorem ReuseCertificate.sound (signature : Op → Interface Slot) (old : Kernels signature Value) (needed : Finset Slot)
    {one two : List Op} (certificate : ReuseCertificate signature old needed one two)
    (updated : Kernels signature Value)
    (agree : ∀ op ∈ certificate.support signature old needed, old op = updated op) (store : Store Slot Value) :
    (execute signature updated one store).map (view needed) = (execute signature updated two store).map (view needed) :=
  certificate.plan.sound signature needed old updated certificate.valid agree store

def ReusePlan.fresh (signature : Op → Interface Slot) (needed : Finset Slot) {one two : List Op}
    (plan : ReusePlan signature needed one two) (changed : Finset Op) : Finset Op :=
  plan.support signature needed ∩ changed

def ReusePlan.check (signature : Op → Interface Slot) (needed : Finset Slot) {one two : List Op}
    (plan : ReusePlan signature needed one two) (changed : Finset Op) : Bool :=
  decide (plan.fresh signature needed changed = ∅)

def ReuseCertificate.fresh (signature : Op → Interface Slot) (old : Kernels signature Value) (needed : Finset Slot)
    {one two : List Op} (certificate : ReuseCertificate signature old needed one two) (changed : Finset Op) : Finset Op :=
  certificate.plan.fresh signature needed changed

def ReuseCertificate.check (signature : Op → Interface Slot) (old : Kernels signature Value) (needed : Finset Slot)
    {one two : List Op} (certificate : ReuseCertificate signature old needed one two) (changed : Finset Op) : Bool :=
  certificate.plan.check signature needed changed

theorem ReuseCertificate.repair_sound (signature : Op → Interface Slot) (old : Kernels signature Value) (needed : Finset Slot)
    {one two : List Op} (certificate : ReuseCertificate signature old needed one two)
    (updated : Kernels signature Value) (changed : Finset Op)
    (unchanged : ∀ op ∉ changed, old op = updated op)
    (repaired : ∀ op ∈ certificate.fresh signature old needed changed, old op = updated op)
    (store : Store Slot Value) :
    (execute signature updated one store).map (view needed) = (execute signature updated two store).map (view needed) := by
  apply certificate.sound signature old needed updated
  intro op member
  by_cases edited : op ∈ changed
  · exact repaired op (Finset.mem_inter.mpr ⟨member, edited⟩)
  · exact unchanged op edited

theorem ReuseCertificate.check_sound (signature : Op → Interface Slot) (old : Kernels signature Value) (needed : Finset Slot)
    {one two : List Op} (certificate : ReuseCertificate signature old needed one two)
    (updated : Kernels signature Value) (changed : Finset Op)
    (unchanged : ∀ op ∉ changed, old op = updated op)
    (accepted : certificate.check signature old needed changed = true) (store : Store Slot Value) :
    (execute signature updated one store).map (view needed) = (execute signature updated two store).map (view needed) := by
  apply certificate.repair_sound signature old needed updated changed unchanged
  intro op member
  have empty : certificate.fresh signature old needed changed = ∅ := of_decide_eq_true accepted
  rw [empty] at member
  simp only [Finset.notMem_empty] at member

end CryptoOracle.StatefulDiagram
