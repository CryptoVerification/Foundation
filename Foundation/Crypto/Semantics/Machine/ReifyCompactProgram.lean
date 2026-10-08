import Foundation.Crypto.Semantics.Machine.CompactProgram
import Foundation.Crypto.Semantics.Machine.Compiler
import Lean

/-! Proof-producing elaboration of shared program views. This runs while checking
Lean source, never in the represented bit machine. Only kernel-checked view
combinators are emitted; unsupported program operations fail explicitly. -/

open Lean Meta Elab Tactic

namespace Machine.CompactProgram.Reifier

structure State where
  programs : Std.HashMap Expr Expr := {}
  values : Std.HashMap Expr (Expr × Expr) := {}
  nodes : Nat := 0

abbrev M := StateRefT State MetaM

private def unfold (e : Expr) : MetaM Expr := do
  if let some body ← reduceRecMatcher? e then return body
  match e with
  | .letE _ _ value body _ => return body.instantiate1 value
  | .mdata _ body => return body
  | .app _ _ =>
    if e.getAppFn.isLambda then return e.headBeta
    if let some body ← unfoldDefinition? e (ignoreTransparency := true) then return body
    throwError "compact_program: unsupported expression {e}"
  | _ =>
    if let some body ← unfoldDefinition? e (ignoreTransparency := true) then
      return body
    throwError "compact_program: unsupported expression {e}"

private def saveProgram (original value : Expr) : M Expr := do
  let value ← instantiateMVars value
  let mut result := value
  if !original.hasFVar && !value.hasFVar &&
      !original.hasMVar && !value.hasMVar then
    let name ← mkFreshUserName `Machine.CompactProgram.generated
    let type ← mkAppM ``CompactProgram #[original]
    let declaration := Declaration.defnDecl {
      name := name
      levelParams := []
      type := type
      value := value
      hints := .regular 0
      safety := .safe
    }
    addDecl declaration
    compileDecl declaration
    result := mkConst name
    modify fun s => { s with nodes := s.nodes + 1 }
  modify fun s => { s with programs := s.programs.insert original result }
  return result

mutual
  partial def program (original : Expr) : M Expr := do
    if let some cached := (← get).programs[original]? then return cached
    let e := original.consumeMData
    let args := e.getAppArgs
    let name := e.getAppFn.constName?
    let result ← match name with
    | some ``List.nil => mkAppM ``CompactProgram.literal #[e]
    | some ``List.cons =>
      let (instruction, correct) ← value args[args.size - 2]!
      let rest ← program args.back!
      mkAppOptM ``CompactProgram.cons #[some args[args.size - 2]!, some args.back!, some instruction, some correct, some rest]
    | some ``List.append | some ``HAppend.hAppend =>
      let first ← program args[args.size - 2]!
      let second ← program args.back!
      mkAppOptM ``CompactProgram.append #[some args[args.size - 2]!, some args.back!, some first, some second]
    | some ``List.replicate =>
      let (count, countEq) ← value args[args.size - 2]!
      let (instruction, instructionEq) ← value args.back!
      mkAppOptM ``CompactProgram.replicate #[some args[args.size - 2]!, some args.back!, some count, some countEq, some instruction, some instructionEq]
    | some ``List.map =>
      let (function, correct) ← value args[args.size - 2]!
      let source ← program args.back!
      mkAppOptM ``CompactProgram.map #[some args.back!, some source, some args[args.size - 2]!, some function, some correct]
    | some ``Program.asSubroutine =>
      let source ← program args[0]!
      let (base, baseEq) ← value args[1]!
      let (returnPc, returnEq) ← value args[2]!
      mkAppOptM ``CompactProgram.subroutine #[some args[0]!, some source, some args[1]!, some args[2]!, some base, some returnPc, some baseEq, some returnEq]
    | some ``GuardedCompiler.compile =>
      let source ← program args[0]!
      mkAppOptM ``CompactProgram.guarded #[some args[0]!, some source]
    | some ``ProgramCompiler.run =>
      let compiler ← whnf args[0]!
      let cargs := compiler.getAppArgs
      let source := args[1]!
      let rewritten ← match compiler.getAppFn.constName? with
      | some ``ProgramCompiler.identity => pure source
      | some ``ProgramCompiler.constant => pure cargs[0]!
      | some ``ProgramCompiler.prefix => mkAppM ``List.append #[cargs[0]!, source]
      | some ``ProgramCompiler.suffix => mkAppM ``List.append #[source, cargs[0]!]
      | some ``ProgramCompiler.twoCalls =>
        mkAppM ``Program.withTwoSubroutines #[cargs[0]!, cargs[1]!, cargs[2]!, source]
      | some ``ProgramCompiler.guarded => mkAppM ``GuardedCompiler.rawCompile #[source]
      | some ``ProgramCompiler.chooseChallenge =>
        mkAppM ``GuardedCompiler.chooseChallengeGuessCompile #[source, cargs[0]!, cargs[1]!, source]
      | some ``ProgramCompiler.comp =>
        let first ← mkAppM ``ProgramCompiler.run #[cargs[0]!, source]
        mkAppM ``ProgramCompiler.run #[cargs[1]!, first]
      | _ => throwError "compact_program: compiler must have known finite syntax"
      let view ← program rewritten
      let proof ← mkEqRefl rewritten
      mkAppOptM ``CompactProgram.reindex #[some rewritten, some original, some view, some proof]
    | _ =>
      if let some name := e.getAppFn.constName? then
        if let some theoremName ← getUnfoldEqnFor? name (nonRec := true) then
          let equation := mkAppN (mkConst theoremName e.getAppFn.constLevels!) args
          let some (_, _, body) := (← inferType equation).eq?
            | throwError "compact_program: unexpected unfolding theorem for {name}"
          let view ← program body
          let proof ← mkEqSymm equation
          mkAppOptM ``CompactProgram.reindex #[some body, some original, some view, some proof]
        else if let some body ← reduceRecMatcher? e then
          let view ← program body
          let proof ← mkEqRefl body
          mkAppOptM ``CompactProgram.reindex #[some body, some original, some view, some proof]
        else
          throwError "compact_program: no checked unfolding theorem for {name}"
      else
        let body ← unfold e
        let view ← program body
        let proof ← mkEqRefl body
        mkAppOptM ``CompactProgram.reindex #[some body, some original, some view, some proof]
    saveProgram original result

  /-- Replace program lengths in addresses by certified cached lengths. -/
  partial def value (original : Expr) : M (Expr × Expr) := do
    if let some cached := (← get).values[original]? then return cached
    let e := original.consumeMData
    let result ← if e.isAppOf ``List.length then do
      let view ← program e.getAppArgs.back!
      let length ← pure (mkApp2 (mkConst ``CompactProgram.length) e.getAppArgs.back! view)
      let correct ← pure (mkApp2 (mkConst ``CompactProgram.length_eq) e.getAppArgs.back! view)
      pure (length, correct)
    else if e.isRawNatLit || e.isFVar then do
      pure (e, ← mkEqRefl e)
    else if e.isLambda then do
      lambdaTelescope e fun xs body => do
        let (newBody, correct) ← value body
        let newLambda ← mkLambdaFVars xs newBody
        let mut proof := correct
        for x in xs.reverse do
          proof ← mkLambdaFVars #[x] proof
          proof ← mkAppM ``funext #[proof]
        pure (newLambda, proof)
    else if e.isLet then do
      unfoldValue original
    else if (← isDefEq (← inferType e) (mkConst ``Nat)) &&
        !([``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod,
          ``Nat.min, ``Nat.max, ``Nat.pow, ``Nat.succ, ``HAdd.hAdd,
          ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod,
          ``Min.min, ``Max.max, ``HPow.hPow, ``OfNat.ofNat, ``ite].contains
            (e.getAppFn.constName?.getD Name.anonymous)) then do
      unfoldValue original
    else do
      let args := e.getAppArgs
      let types ← args.mapM fun arg => do inferType arg
      let hasProgram ← types.anyM fun type => isDefEq type (mkConst ``Program)
      if hasProgram then
        unfoldValue original
      else if e.isApp then do
        let mut rebuilt := e.getAppFn
        let mut correct ← mkEqRefl rebuilt
        for arg in args do
          let type ← inferType arg
          let rewrite ← isDefEq type (mkConst ``Nat)
            <||> isDefEq type (mkConst ``Instruction)
          let (newArg, argEq) ← if rewrite then value arg else pure (arg, ← mkEqRefl arg)
          correct ← mkCongr correct argEq
          rebuilt := mkApp rebuilt newArg
        pure (rebuilt, correct)
      else if (← isDefEq (← inferType e) (mkConst ``Nat)) then
        unfoldValue original
      else
        pure (e, ← mkEqRefl e)
    modify fun s => { s with values := s.values.insert original result }
    return result

  partial def unfoldValue (original : Expr) : M (Expr × Expr) := do
    if let some name := original.getAppFn.constName? then
      if let some theoremName ← getUnfoldEqnFor? name (nonRec := true) then
        let equation := mkAppN (mkConst theoremName original.getAppFn.constLevels!) original.getAppArgs
        let some (_, _, body) := (← inferType equation).eq?
          | throwError "compact_program: unexpected value equation for {name}"
        let (result, proof) ← value body
        return (result, ← mkEqTrans proof (← mkEqSymm equation))
    let body ← unfold original
    let (result, proof) ← value body
    let equality ← mkEqRefl body
    let equality ← mkExpectedTypeHint equality (← mkEq body original)
    return (result, ← mkEqTrans proof equality)
end

end Machine.CompactProgram.Reifier

/-- Construct a certified shared view, using any supplied local CompactProgram
witnesses as leaves. Closed nodes are compiled once and shared by references. -/
private def runCompactProgram (seeds : Array Syntax := #[]) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOf ``Machine.CompactProgram do
      throwError "compact_program expects a CompactProgram goal"
    let mut state : Machine.CompactProgram.Reifier.State := {}
    for decl in ← getLCtx do
      if !decl.isAuxDecl && decl.type.isAppOf ``Machine.CompactProgram then
        state := { state with programs := state.programs.insert decl.type.getAppArgs.back! decl.toExpr }
    for seed in seeds do
      let witness ← Term.elabTerm seed none
      let type ← instantiateMVars (← inferType witness)
      unless type.isAppOf ``Machine.CompactProgram do
        throwError "compact_program: supplied witness is not a CompactProgram"
      state := { state with programs := state.programs.insert type.getAppArgs.back! witness }
    let (result, _) ← (Machine.CompactProgram.Reifier.program target.getAppArgs.back!).run state
    goal.assign result
    replaceMainGoal []

elab "compact_program" : tactic => runCompactProgram
elab "compact_program" "[" seeds:term,* "]" : tactic =>
  runCompactProgram seeds.getElems
