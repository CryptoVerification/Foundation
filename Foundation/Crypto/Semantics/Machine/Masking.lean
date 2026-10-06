import Foundation.Crypto.Semantics.Machine.Adversary

/-! Finite reduction code for challenge distinguishers. The masking controller
copies the public security parameter, XORs one pair of challenge/message cells
per transition, and loads one input cell per transition before starting the
unchanged native attack code. Each controller operation accesses only a fixed
number of cells. There are no executable Lean continuations in this syntax. -/
namespace Machine.Masking

open Foundation.Probability

inductive Code where
  | native : Program → Code
  | masked : Bool → Program → Code
  deriving DecidableEq, Repr, Encodable

def Code.program : Code → Program
  | .native p | .masked _ p => p

/-- A compiler produces two finite programs, one for each public message. -/
def compile (side : Bool) (program : Program) : Code := .masked side program

inductive Configuration where
  | prefix : List Bool → List Bool → List Bool → List Bool → Configuration
  | masking : List Bool → List Bool → List Bool → Configuration
  | loading : List Bool → Tape → Configuration
  | running : Machine.Configuration → Configuration
  deriving DecidableEq, Repr

/-- Constant-size cell insertion, including the empty-tape boundary. -/
def prepend (bit : Bool) (tape : Tape) : Tape :=
  match tape.current, tape.right with
  | none, [] => { current := some bit }
  | _, _ => { current := some bit, right := tape.current :: tape.right }

@[simp] theorem prepend_ofBits (bit : Bool) (bits : List Bool) :
    prepend bit (Tape.ofBits bits) = Tape.ofBits (bit :: bits) := by
  cases bits <;> rfl

def xorList : List Bool → List Bool → List Bool
  | x :: xs, y :: ys => Bool.xor x y :: xorList xs ys
  | _, _ => []

/-- The supplied public messages and challenge are experiment inputs. Their
subsequent copying, masking, and loading are charged controller transitions. -/
def initial (code : Code) (header left right challenge : List Bool) : Configuration :=
  match code with
  | .native _ => .running (Machine.Configuration.initial (header ++ challenge))
  | .masked side _ => .prefix header (if side then right else left) challenge []

def nextController : Configuration → Configuration
  | .prefix (bit :: rest) mask challenge acc => .prefix rest mask challenge (bit :: acc)
  | .prefix [] mask challenge acc => .masking mask challenge acc
  | .masking (bit :: rest) (pad :: pads) acc =>
      .masking rest pads (Bool.xor bit pad :: acc)
  | .masking _ _ acc => .loading acc {}
  | .loading (bit :: rest) tape => .loading rest (prepend bit tape)
  | .loading [] tape => .running { inputTape := tape }
  | .running machine => .running machine

noncomputable def step (code : Code) : Configuration → ProbComp Configuration
  | .running machine => (stepPMF code.program machine).map Configuration.running
  | config => PMF.pure (nextController config)

noncomputable def eval (code : Code) (start : Configuration) : Nat → ProbComp Configuration
  | 0 => PMF.pure start
  | fuel + 1 => (eval code start fuel).bind (step code)

def complete : Configuration → Prop
  | .running machine => machine.halted = true
  | _ => False

def result : Configuration → Option Bool
  | .running machine => if machine.halted then some (machine.outputTape.current.getD false) else none
  | _ => none

def HaltsWithin (code : Code) (start : Configuration) (time : Nat) : Prop :=
  ∀ finish ∈ (eval code start time).support, complete finish

noncomputable def output (code : Code) (start : Configuration) (time : Nat) :
    ProbComp (Option Bool) := (eval code start time).map result

/-- A compositional budget for the very same physical configuration. -/
theorem eval_add (code : Code) (start : Configuration) (first second : Nat) :
    eval code start (first + second) =
      (eval code start first).bind (fun middle => eval code middle second) := by
  induction second with
  | zero => simp [eval]
  | succ second ih => rw [Nat.add_succ, eval, ih, PMF.bind_bind]; rfl

theorem eval_one (code : Code) (start : Configuration) :
    eval code start 1 = step code start := by simp [eval]

theorem eval_head (code : Code) (start : Configuration) (rest : Nat) :
    eval code start (rest + 1) = (step code start).bind (fun next => eval code next rest) := by
  rw [show rest + 1 = 1 + rest by omega, eval_add, eval_one]

/-- Prefix copying is a separate linear cost. -/
theorem prefix_eval (code : Code) (header mask challenge acc : List Bool) :
    eval code (.prefix header mask challenge acc) (header.length + 1) =
      PMF.pure (.masking mask challenge (header.reverse ++ acc)) := by
  induction header generalizing acc with
  | nil => simp [eval, step, nextController]
  | cons bit rest ih =>
      rw [List.length_cons, eval_head]
      simp only [step, nextController, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Only equal-length masks are admitted by the cryptographic interface. -/
theorem masking_eval (code : Code) (mask challenge acc : List Bool)
    (equalLength : mask.length = challenge.length) :
    eval code (.masking mask challenge acc) (mask.length + 1) =
      PMF.pure (.loading ((xorList mask challenge).reverse ++ acc) {}) := by
  induction mask generalizing challenge acc with
  | nil =>
      have : challenge = [] := List.length_eq_zero_iff.mp equalLength.symm
      subst challenge
      simp [eval, step, nextController, xorList]
  | cons bit rest ih =>
      cases challenge with
      | nil => simp at equalLength
      | cons pad pads =>
          rw [List.length_cons, eval_head]
          simp only [step, nextController, PMF.pure_bind]
          rw [ih pads (Bool.xor bit pad :: acc) (by simpa using equalLength)]
          simp [xorList, List.reverse_cons, List.append_assoc]

theorem loading_eval (code : Code) (acc rest : List Bool) :
    eval code (.loading acc (Tape.ofBits rest)) (acc.length + 1) =
      PMF.pure (.running (Machine.Configuration.initial (acc.reverse ++ rest))) := by
  induction acc generalizing rest with
  | nil => simp [eval, step, nextController, Machine.Configuration.initial]
  | cons bit tail ih =>
      rw [List.length_cons, eval_head]
      simp only [step, nextController, PMF.pure_bind, prepend_ofBits]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem length_xorList (mask challenge : List Bool) (h : mask.length = challenge.length) :
    (xorList mask challenge).length = mask.length := by
  induction mask generalizing challenge with
  | nil => simp [xorList]
  | cons bit rest ih =>
      cases challenge with
      | nil => simp at h
      | cons pad pads => simp [xorList, ih pads (by simpa using h)]

/-- All local preparation and cell loading is charged, including dispatch. -/
def overhead (headerLength messageLength : Nat) : Nat := 2 * (headerLength + messageLength) + 3

theorem masked_prepare (side : Bool) (p : Program) (header left right challenge : List Bool)
    (hl : left.length = challenge.length) (hr : right.length = challenge.length) :
    eval (.masked side p) (initial (.masked side p) header left right challenge)
      (overhead header.length challenge.length) =
    PMF.pure (.running (Machine.Configuration.initial
      (header ++ xorList (if side then right else left) challenge))) := by
  have hm : (if side then right else left).length = challenge.length := by
    cases side <;> assumption
  let mask := if side then right else left
  have hsize : overhead header.length challenge.length =
      (header.length + 1) + (mask.length + 1) +
        (((xorList mask challenge).reverse ++ header.reverse).length + 1) := by
    have hml : mask.length = challenge.length := hm
    have hx := length_xorList mask challenge hm
    simp only [List.length_append, List.length_reverse]
    dsimp only [overhead]
    omega
  rw [hsize, eval_add, eval_add]
  change ((eval _ (.prefix header mask challenge []) _).bind _).bind _ = _
  rw [prefix_eval]
  simp only [List.append_nil, PMF.pure_bind]
  rw [masking_eval _ _ _ _ hm, PMF.pure_bind]
  change eval _ (.loading _ (Tape.ofBits [])) _ = _
  rw [loading_eval]
  simp [List.reverse_append]

/-- After preparation the caller's original native probabilistic code is
executed unchanged, retaining every branch of its fresh random bits. -/
theorem running_eval (code : Code) (machine : Machine.Configuration) (time : Nat) :
    eval code (.running machine) time =
      (evalConfigWithin code.program machine time).map Configuration.running := by
  induction time with
  | zero => simp [eval, evalConfigWithin, PMF.pure_map]
  | succ time ih =>
      rw [eval, ih, PMF.bind_map]
      simp only [Function.comp_def, step]
      rw [← PMF.map_bind]
      rfl

/-- Exact simulation, not merely equal final guessing probabilities. -/
theorem masked_eval (side : Bool) (p : Program) (header left right challenge : List Bool)
    (hl : left.length = challenge.length) (hr : right.length = challenge.length) (time : Nat) :
    eval (.masked side p) (initial (.masked side p) header left right challenge)
      (overhead header.length challenge.length + time) =
    eval (.native p) (initial (.native p) header left right
      (xorList (if side then right else left) challenge)) time := by
  rw [eval_add, masked_prepare side p header left right challenge hl hr, PMF.pure_bind]
  rw [running_eval]
  change _ = eval (.native p) (.running _) time
  rw [running_eval]
  rfl

/-- Executable native path using explicit test coin choices. -/
def nativeNext (program : Program) (machine : Machine.Configuration) (coin : Bool) :
    Machine.Configuration :=
  match Machine.next program machine with
  | none => machine
  | some (.inl next) => next
  | some (.inr (zero, one)) => if coin then one else zero

def simulateStep (code : Code) (coin : Bool) : Configuration → Configuration
  | .running machine => .running (nativeNext code.program machine coin)
  | config => nextController config

/-- The executable interpreter shares the probabilistic operational semantics. -/
theorem simulateStep_mem_support (code : Code) (coin : Bool) (config : Configuration) :
    simulateStep code coin config ∈ (step code config).support := by
  cases config with
  | «prefix» header mask challenge acc => simp [simulateStep, step]
  | masking mask challenge acc => simp [simulateStep, step]
  | loading acc tape => simp [simulateStep, step]
  | running machine =>
    change Configuration.running (nativeNext code.program machine coin) ∈
      ((stepPMF code.program machine).map Configuration.running).support
    rw [PMF.mem_support_map_iff]
    refine ⟨nativeNext code.program machine coin, ?_, rfl⟩
    cases hn : Machine.next code.program machine with
    | none => simp [nativeNext, stepPMF, hn]
    | some next =>
        cases next with
        | inl next => simp [nativeNext, stepPMF, hn]
        | inr pair =>
            simp only [nativeNext, stepPMF, hn, PMF.mem_support_map_iff]
            exact ⟨coin, PMF.mem_support_uniformOfFintype coin, rfl⟩

/-- Tail-recursive path test; completion stops the clock without padding. -/
def simulateLoop (code : Code) (coin : Bool) :
    Nat → Configuration → Nat → Configuration × Nat
  | 0, config, used => (config, used)
  | fuel + 1, config, used =>
      if (result config).isSome then (config, used) else
        simulateLoop code coin fuel (simulateStep code coin config) (used + 1)

def simulate (code : Code) (coin : Bool) (fuel : Nat) (start : Configuration) :
    Configuration × Nat := simulateLoop code coin fuel start 0

/-- Completed native configurations absorb padding. -/
theorem step_complete (code : Code) (config : Configuration) (h : complete config) :
    step code config = PMF.pure config := by
  cases config <;> try contradiction
  case running machine =>
    simp only [complete] at h
    simp [step, stepPMF, Machine.next, h, PMF.pure_map]

/-- A valid stopping bound cannot communicate advice by later padding. -/
theorem eval_stable (code : Code) (start : Configuration) (time extra : Nat)
    (h : HaltsWithin code start time) : eval code start (time + extra) = eval code start time := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ, eval, ih, ← PMF.bindOnSupport_eq_bind]
      calc
        _ = (eval code start time).bindOnSupport (fun c _ => PMF.pure c) := by
          congr 1
          funext c hc
          exact step_complete code c (h c hc)
        _ = _ := PMF.bindOnSupport_pure _

end Machine.Masking
