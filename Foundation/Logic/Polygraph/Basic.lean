import Foundation.Logic.Translation

/-! Typed, bracketed expressions for finite-input inference diagrams. Structural
maps refer to logical assumptions, not to executions or private states. These
expressions have not been quotiented by the laws of a strict 2-category. -/
namespace Foundation.Logic.Polygraph

universe j r
set_option linter.checkUnivs false

namespace Context

abbrev append {T : Presentation.{j, r}} (Γ Δ : Logic.Context T) : Logic.Context T where
  length := Γ.length + Δ.length
  claim := Fin.addCases Γ.claim Δ.claim

theorem append_left {T : Presentation.{j, r}} (Γ Δ : Logic.Context T) (i : Fin Γ.length) :
    (append Γ Δ).claim (Fin.castAdd Δ.length i) = Γ.claim i := by
  simp

theorem append_right {T : Presentation.{j, r}} (Γ Δ : Logic.Context T) (i : Fin Δ.length) :
    (append Γ Δ).claim (Fin.natAdd Γ.length i) = Δ.claim i := by
  simp

end Context

/-- Each output assumption chooses an input of the same judgment. Repeated
indices express logical contraction; omitted inputs express weakening. -/
structure Wiring {T : Presentation.{j, r}} (Γ Δ : Logic.Context T) where
  index : Fin Δ.length → Fin Γ.length
  agrees : ∀ i, Γ.claim (index i) = Δ.claim i

namespace Wiring

variable {T : Presentation.{j, r}}

def identity (Γ : Logic.Context T) : Wiring Γ Γ := ⟨id, fun _ => rfl⟩

def select (Γ : Logic.Context T) (i : Fin Γ.length) :
    Wiring Γ (Logic.Context.singleton (Γ.claim i)) := ⟨fun _ => i, fun _ => rfl⟩

def discard (Γ : Logic.Context T) : Wiring Γ (Logic.Context.empty T) :=
  ⟨Fin.elim0, fun i => Fin.elim0 i⟩

def left (Γ Δ : Logic.Context T) : Wiring (Context.append Γ Δ) Γ :=
  ⟨Fin.castAdd Δ.length, Context.append_left Γ Δ⟩

def right (Γ Δ : Logic.Context T) : Wiring (Context.append Γ Δ) Δ :=
  ⟨Fin.natAdd Γ.length, Context.append_right Γ Δ⟩

end Wiring

/-- Raw diagram expressions. `tuple` shares a logical context among its
outputs. `tensor` instead supplies disjoint input blocks to its two operands. -/
inductive Diagram (T : Presentation.{j, r}) : Logic.Context T → Logic.Context T →
    Type (max j r) where
  | identity (Γ) : Diagram T Γ Γ
  | generator (rule : T.Rule) :
      Diagram T (T.ruleContext rule) (Logic.Context.singleton (T.conclusion rule))
  | wiring {Γ Δ} : Wiring Γ Δ → Diagram T Γ Δ
  | seq {Γ Δ Θ} : Diagram T Γ Δ → Diagram T Δ Θ → Diagram T Γ Θ
  | tensor {Γ Δ Γ' Δ'} : Diagram T Γ Δ → Diagram T Γ' Δ' →
      Diagram T (Context.append Γ Γ') (Context.append Δ Δ')
  | tuple {Γ Δ} : (∀ i, Diagram T Γ (Logic.Context.singleton (Δ.claim i))) →
      Diagram T Γ Δ

end Foundation.Logic.Polygraph
