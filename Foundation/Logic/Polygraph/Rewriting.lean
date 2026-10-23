import Mathlib.Logic.Relation

/-! Proof-relevant directed rewriting and its free reversible paths.
All paths live in Type: two rewrites with equal boundaries need not coincide.
The later four-dimensional presentation specifies which paths are identified. -/
namespace Foundation.Logic.Polygraph

universe u v

inductive RewritePath {A : Type u} (R : A → A → Type v) : A → A → Type (max u v) where
  | refl (a) : RewritePath R a a
  | cons {a b c} : R a b → RewritePath R b c → RewritePath R a c

namespace RewritePath
variable {A : Type u} {R : A → A → Type v} {a b c : A}

def single (s : R a b) : RewritePath R a b := .cons s (.refl b)

def length : {a b : A} → RewritePath R a b → Nat
  | _, _, .refl _ => 0
  | _, _, .cons _ p => 1 + length p

def comp : {a b c : A} → RewritePath R a b → RewritePath R b c → RewritePath R a c
  | _, _, _, .refl _, q => q
  | _, _, _, .cons s p, q => .cons s (comp p q)

def map {B : Type*} {S : B → B → Type*} (f : A → B)
    (h : ∀ {x y}, R x y → S (f x) (f y)) :
    {a b : A} → RewritePath R a b → RewritePath S (f a) (f b)
  | _, _, .refl _ => .refl _
  | _, _, .cons s p => .cons (h s) (p.map f h)

end RewritePath

/-- The raw free groupoid syntax of three-dimensional paths. -/
inductive Track {A : Type u} (R : A → A → Type v) : A → A → Type (max u v) where
  | refl (a) : Track R a a
  | step {a b} : R a b → Track R a b
  | comp {a b c} : Track R a b → Track R b c → Track R a c
  | inv {a b} : Track R a b → Track R b a

namespace Track
variable {A : Type u} {R : A → A → Type v} {a b c : A}

def ofPath : {a b : A} → RewritePath R a b → Track R a b
  | _, _, .refl _ => .refl _
  | _, _, .cons s p => .comp (.step s) (ofPath p)

def ofEq {a b : A} (h : a = b) : Track R a b := h ▸ .refl a

def map {B : Type*} {S : B → B → Type*} (f : A → B)
    (h : ∀ {x y}, R x y → S (f x) (f y)) :
    {a b : A} → Track R a b → Track S (f a) (f b)
  | _, _, .refl _ => .refl _
  | _, _, .step s => .step (h s)
  | _, _, .comp p q => .comp (map f h p) (map f h q)
  | _, _, .inv p => .inv (map f h p)

/-- Interpretation of paths requires a certificate for each actual rewrite. -/
theorem sound (h : ∀ {x y}, R x y → x = y) : {a b : A} → Track R a b → a = b
  | _, _, .refl _ => rfl
  | _, _, .step s => h s
  | _, _, .comp p q => (sound h p).trans (sound h q)
  | _, _, .inv p => (sound h p).symm

end Track
end Foundation.Logic.Polygraph
