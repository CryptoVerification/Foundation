import Foundation.Logic.Polygraph.Higher
import Lean
/-! Kernel-checked pasting automation: association/unit normalization and
application of one supplied Four cell at a consecutive path segment. No
semantic equality, new generator or untrusted proof result is accepted. -/
namespace Foundation.Logic.Polygraph.FourAssociation
universe u v w
variable {A : Type u} {R : A → A → Type v}

def reflCell (G : {a b : A} → Track R a b → Track R a b → Type w) {a b} (p : Track R a b) := Four.refl (G := G) p
def compCell (G : {a b : A} → Track R a b → Track R a b → Type w) {a b c}
    {p p' : Track R a b} {q q' : Track R b c} (one : Four G p p') (two : Four G q q') := Four.comp one two
def transCell (G : {a b : A} → Track R a b → Track R a b → Type w) {a b}
    {p q r : Track R a b} (one : Four G p q) (two : Four G q r) := one.trans two
def symmCell (G : {a b : A} → Track R a b → Track R a b → Type w) {a b}
    {p q : Track R a b} (one : Four G p q) := one.symm
def assocCell (G : {a b : A} → Track R a b → Track R a b → Type w) {a b c d}
    (p : Track R a b) (q : Track R b c) (r : Track R c d) := Four.assoc (G := G) p q r
def leftCell (G : {a b : A} → Track R a b → Track R a b → Type w) {a b} (p : Track R a b) := Four.leftUnit (G := G) p
def rightCell (G : {a b : A} → Track R a b → Track R a b → Type w) {a b} (p : Track R a b) := Four.rightUnit (G := G) p

open Lean Meta Elab Tactic
private def compParts (p : Expr) : MetaM (Option (Expr × Expr)) := do
  let p ← whnf p
  if p.isAppOf ``Track.comp then
    let args := p.getAppArgs
    return some (args[args.size-2]!, args[args.size-1]!)
  return none

private partial def append (g p q : Expr) : MetaM (Expr × Expr) := do
  let p ← whnf p
  let q ← whnf q
  if p.isAppOf ``Track.refl then
    return (q, ← mkAppM ``leftCell #[g,q])
  if q.isAppOf ``Track.refl then
    return (p, ← mkAppM ``rightCell #[g,p])
  if let some (one,two) ← compParts p then
    let (rest, proof) ← append g two q
    let result ← mkAppM ``Track.comp #[one,rest]
    let reassoc ← mkAppM ``assocCell #[g,one,two,q]
    let congr ← mkAppM ``compCell #[g, ← mkAppM ``reflCell #[g,one],proof]
    return (result, ← mkAppM ``transCell #[g,reassoc,congr])
  let result ← mkAppM ``Track.comp #[p,q]
  return (result, ← mkAppM ``reflCell #[g,result])

private partial def normalize (g p : Expr) : MetaM (Expr × Expr) := do
  if let some (one,two) ← compParts p then
    let (first,pf) ← normalize g one
    let (second,ps) ← normalize g two
    let congr ← mkAppM ``compCell #[g,pf,ps]
    let (result,join) ← append g first second
    return (result, ← mkAppM ``transCell #[g,congr,join])
  return (p, ← mkAppM ``reflCell #[g,p])

private def associationProof (g p q : Expr) : MetaM Expr := do
  let (left,lp) ← normalize g p
  let (right,rp) ← normalize g q
  unless ← isDefEq left right do throwError "Paths differ beyond association and units"
  mkAppM ``transCell #[g,lp,← mkAppM ``symmCell #[g,rp]]

elab "four_assoc" : tactic => do
  let goal ← getMainGoal
  let target ← whnf (← goal.getType)
  unless target.isAppOfArity ``Four 7 do throwError "Expected a Four-cell goal"
  let args := target.getAppArgs
  goal.assign (← associationProof args[2]! args[5]! args[6]!)
  replaceMainGoal []

private partial def fragments (p : Expr) : MetaM (Array Expr) := do
  let p ← whnf p
  if let some (one,two) ← compParts p then return (← fragments one) ++ (← fragments two)
  if p.isAppOf ``Track.refl then return #[]
  return #[p]

private def compose (items : Array Expr) : MetaM Expr := do
  if items.isEmpty then throwError "Expected nonempty path fragments"
  let mut result := items.back!
  for offset in [:items.size-1] do
    result ← mkAppM ``Track.comp #[items[items.size-2-offset]!,result]
  return result

/-- Paste one supplied higher cell into a consecutive path segment.
Only association and units are filled automatically. -/
elab "four_rewrite " witness:term : tactic => do
  let goal ← getMainGoal
  let target ← whnf (← goal.getType)
  unless target.isAppOfArity ``Four 7 do throwError "Expected a Four-cell goal"
  let args := target.getAppArgs
  let g := args[2]!
  let witness ← Term.elabTerm witness none
  let kind ← whnf (← inferType witness)
  unless kind.isAppOfArity ``Four 7 do throwError "Expected an actual Four-cell witness"
  let parts := kind.getAppArgs
  unless ← isDefEq g parts[2]! do throwError "The witness has a different higher basis"
  let (before,bp) ← normalize g parts[5]!
  let (_,ap) ← normalize g parts[6]!
  let normalizedWitness ← mkAppM ``transCell #[g,← mkAppM ``symmCell #[g,bp],
    ← mkAppM ``transCell #[g,witness,ap]]
  let atoms ← fragments args[5]!
  let pattern ← fragments before
  if pattern.isEmpty || atoms.size < pattern.size then throwError "No nonempty matching segment"
  let mut found : Option Nat := none
  for start in [:atoms.size-pattern.size+1] do
    let mut matchOk := true
    for offset in [:pattern.size] do
      unless ← isDefEq atoms[start+offset]! pattern[offset]! do
        matchOk := false
        break
    if matchOk then
      found := some start
      break
  let some start := found | throwError "No matching segment"
  let mut pasted := normalizedWitness
  let afterAtoms := atoms.extract (start+pattern.size) atoms.size
  unless afterAtoms.isEmpty do
    pasted ← mkAppM ``compCell #[g,pasted,← mkAppM ``reflCell #[g,← compose afterAtoms]]
  let beforeAtoms := atoms.extract 0 start
  unless beforeAtoms.isEmpty do
    pasted ← mkAppM ``compCell #[g,← mkAppM ``reflCell #[g,← compose beforeAtoms],pasted]
  let pastedType ← whnf (← inferType pasted)
  let endpoints := pastedType.getAppArgs
  let first ← associationProof g args[5]! endpoints[5]!
  let last ← associationProof g endpoints[6]! args[6]!
  goal.assign (← mkAppM ``transCell #[g,first,← mkAppM ``transCell #[g,pasted,last]])
  replaceMainGoal []

end Foundation.Logic.Polygraph.FourAssociation
