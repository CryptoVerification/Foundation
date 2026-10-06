import Foundation.Crypto.Meta.General.Metatheory

/-! Canonical typed chains of registered compiler primitives. Normalization
acts on finite compiler syntax, without expanding primitive machine code.
The semantic proof tree, resource witnesses, and loss expression are retained. -/
namespace CryptoLogic.General

universe u v a b
set_option backward.isDefEq.respectTransparency false

/-- A sequential list whose intermediate machine types must agree. -/
inductive CompilerChain (K : CodeSystem) : K.Machine → K.Machine → Type where
  | nil (m) : CompilerChain K m m
  | cons {m n k} : K.Primitive m n → CompilerChain K n k → CompilerChain K m k

namespace CompilerChain

variable {K : CodeSystem}

def append {m n k} : CompilerChain K m n → CompilerChain K n k → CompilerChain K m k
  | .nil _, second => second
  | .cons p tail, second => .cons p (tail.append second)

def run {m n} : CompilerChain K m n → K.Code m → K.Code n
  | .nil _, code => code
  | .cons p tail, code => tail.run (K.runPrimitive p code)

def length {m n} : CompilerChain K m n → Nat
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

/-- Single primitives have no extra terminal identity; longer chains are
right associated and contain no identity composition nodes. -/
def toCompiler {m n} : CompilerChain K m n → Compiler K m n
  | .nil m => .identity m
  | .cons p (.nil _) => .primitive p
  | .cons p (.cons q tail) => .comp (.primitive p) (toCompiler (.cons q tail))

theorem run_append {m n k} (first : CompilerChain K m n) (second : CompilerChain K n k)
    (code : K.Code m) : (first.append second).run code = second.run (first.run code) := by
  induction first with
  | nil m => rfl
  | cons p tail ih => exact ih second (K.runPrimitive p code)

@[simp] theorem append_nil {m n} (chain : CompilerChain K m n) :
    chain.append (.nil n) = chain := by
  induction chain with
  | nil m => rfl
  | cons p tail ih => exact congrArg (cons p) ih

theorem append_assoc {m n k l} (first : CompilerChain K m n)
    (second : CompilerChain K n k) (third : CompilerChain K k l) :
    (first.append second).append third = first.append (second.append third) := by
  induction first with
  | nil m => rfl
  | cons p tail ih => exact congrArg (cons p) (ih second)

theorem run_toCompiler {m n} (chain : CompilerChain K m n) (code : K.Code m) :
    chain.toCompiler.run code = chain.run code := by
  induction chain with
  | nil m => rfl
  | cons p tail ih =>
      cases tail with
      | nil n => rfl
      | cons q rest => exact ih (K.runPrimitive p code)

end CompilerChain

namespace Compiler

variable {K : CodeSystem}

def chain {m n} : Compiler K m n → CompilerChain K m n
  | .identity m => .nil m
  | .primitive p => .cons p (.nil _)
  | .comp first second => first.chain.append second.chain

theorem chain_run {m n} (compiler : Compiler K m n) (code : K.Code m) :
    compiler.chain.run code = compiler.run code := by
  induction compiler with
  | identity m => rfl
  | primitive p => rfl
  | comp first second hf hs =>
      rw [chain, CompilerChain.run_append, hf, hs]
      rfl

@[simp] theorem chain_toCompiler {m n} (path : CompilerChain K m n) :
    path.toCompiler.chain = path := by
  induction path with
  | nil m => rfl
  | cons p tail ih =>
      cases tail with
      | nil n => rfl
      | cons q rest =>
          change (CompilerChain.cons p (.nil _)).append (CompilerChain.cons q rest).toCompiler.chain = _
          rw [ih]
          rfl

def normalize {m n} (compiler : Compiler K m n) : Compiler K m n := compiler.chain.toCompiler

@[simp] theorem normalize_run {m n} (compiler : Compiler K m n) (code : K.Code m) :
    compiler.normalize.run code = compiler.run code := by
  rw [normalize, CompilerChain.run_toCompiler, chain_run]

/-- A fixed point after one pass, as syntax, not just as execution behavior. -/
@[simp] theorem normalize_idempotent {m n} (compiler : Compiler K m n) :
    compiler.normalize.normalize = compiler.normalize := by
  simp only [normalize, chain_toCompiler]

@[simp] theorem normalize_comp_identity {m n} (compiler : Compiler K m n) :
    (compiler.comp (.identity n)).normalize = compiler.normalize := by
  simp only [normalize, chain, CompilerChain.append_nil]

@[simp] theorem normalize_identity_comp {m n} (compiler : Compiler K m n) :
    ((Compiler.identity m).comp compiler).normalize = compiler.normalize := rfl

theorem normalize_comp_assoc {m n k l} (first : Compiler K m n)
    (second : Compiler K n k) (third : Compiler K k l) :
    ((first.comp second).comp third).normalize = (first.comp (second.comp third)).normalize := by
  simp only [normalize, chain, CompilerChain.append_assoc]

end Compiler

namespace CertifiedTransform

variable {K : CodeSystem} {m n : K.Machine}
  {X : SecurityObject.{u, v} K m} {Y : SecurityObject.{u, v} K n}

def normalize (T : CertifiedTransform X Y) : CertifiedTransform X Y where
  transform := T.transform
  compiler := T.compiler.normalize
  mapWitness := T.mapWitness
  code_eq := by intro F A W; rw [Compiler.normalize_run]; exact T.code_eq F A W

theorem normalize_witness (T : CertifiedTransform X Y) (F A W) :
    T.normalize.mapWitness F A W = T.mapWitness F A W := rfl

end CertifiedTransform

variable {K : CodeSystem} {L : Language.{a, b} K} {S : Signature.{u, v} L}

namespace Derivation

variable {Γ : Context S}

/-- Normalize the cached compilers. Keep the original typed plan and proof,
so no alternative loss or resource certificate is selected. -/
@[macro_inline] def normalize {X F} (d : Derivation S Γ X F) : Derivation S Γ X F where
  plan := d.plan
  compilers := d.compilers.map fun (i, ⟨n, c⟩) => (i, ⟨n, c.normalize⟩)
  emitted_eq := by
    intro code
    rw [List.map_map]
    calc
      _ = d.compilers.map (fun (i, ⟨n, c⟩) => (i, ⟨n, c.run code⟩)) := by
        apply List.map_congr_left
        intro entry _
        rcases entry with ⟨i, n, c⟩
        simp only [Function.comp_def, Compiler.normalize_run]
      _ = _ := d.emitted_eq code
  typed := d.typed

theorem normalize_run {X F} (d : Derivation S Γ X F) (code : K.Code (L.machine X)) :
    d.normalize.run code = d.run code := by
  rw [d.normalize.run_eq, d.run_eq]
  rfl

/-- Normalization can be performed before or after substitution without
changing execution. The final caches are normalized after all substitutions. -/
theorem normalize_substitute_run {Δ : Context S} {X F} (d : Derivation S Γ X F)
    (replacement : ∀ i, Derivation S Δ (Γ.claim i).object (Γ.claim i).family)
    (code : K.Code (L.machine X)) :
    (d.substitute replacement).normalize.run code =
      (d.normalize.substitute (fun i => (replacement i).normalize)).run code := by
  rw [normalize_run, (d.substitute replacement).run_eq,
    (d.normalize.substitute (fun i => (replacement i).normalize)).run_eq]
  rfl

/-- The same checked tree is retained, not merely one with equal code. -/
theorem normalize_loss {X F} (d : Derivation S Γ X F) : d.normalize.loss = d.loss := rfl

theorem normalize_runWitnesses {X F} (d : Derivation S Γ X F) (A)
    (W : (S.interpret X).Witness F A) :
    d.normalize.runWitnesses A W = d.runWitnesses A W := rfl

@[simp] theorem normalize_idempotent {X F} (d : Derivation S Γ X F) :
    d.normalize.normalize = d.normalize := by
  cases d
  simp only [normalize, List.map_map, Function.comp_def, Compiler.normalize_idempotent]

def Analysis.normalize {X F} {d : Derivation S Γ X F} (analysis : Analysis d) :
    Analysis d.normalize := ⟨analysis.tree, analysis.plan_eq⟩

theorem Analysis.normalize_loss {X F} {d : Derivation S Γ X F} (analysis : Analysis d) :
    analysis.normalize.loss = analysis.loss := rfl

theorem Analysis.normalize_runWitnesses {X F} {d : Derivation S Γ X F}
    (analysis : Analysis d) (A) (W : (S.interpret X).Witness F A) :
    analysis.normalize.runWitnesses A W = analysis.runWitnesses A W := rfl

end Derivation
end CryptoLogic.General
