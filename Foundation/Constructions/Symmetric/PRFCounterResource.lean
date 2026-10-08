import Foundation.Constructions.Symmetric.PRFCounterPrivacy
import Foundation.Crypto.Semantics.Oracle.CounterWhole
import Foundation.Crypto.Logic.General.Execution

/-! Resource classes for adaptive counter encryption and PRF distinguishers.
Every family has one fixed finite code. Public capacity cells are limited by
the query allowance, even when the function domain is exponentially larger.
The source certificate concerns only source encryption-oracle execution;
target stopping, CPU bounds and PRF query counts are derived operationally. -/
namespace Foundation.Symmetric.PRFCounter.Resource
open Foundation.Probability CryptoOracle CryptoLogic.General
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Kind where
  | source | target
  deriving DecidableEq, Repr, Encodable

def Code : Kind → Type
  | .source => Interactive.Code
  | .target => CryptoOracle.CounterMasking.Code

inductive Primitive : Kind → Kind → Type where
  | wrap (side : Bool) : Primitive .source .target

def Primitive.encode {m n} : Primitive m n → Bool
  | .wrap side => side

def Primitive.decode (m n : Kind) (side : Bool) : Option (Primitive m n) :=
  match m, n with
  | .source, .target => some (.wrap side)
  | _, _ => none

instance (m n : Kind) : Encodable (Primitive m n) :=
  Encodable.ofLeftInjection Primitive.encode (Primitive.decode m n) (by intro p; cases p; rfl)

def system : CodeSystem where
  Machine := Kind
  Code := Code
  machineEncodable := inferInstance
  Primitive := Primitive
  codeEncodable := fun m => by cases m <;> dsimp [Code] <;> exact inferInstance
  primitiveEncodable := fun _ _ => inferInstance
  runPrimitive := fun p code => match p with | .wrap side => CryptoOracle.CounterMasking.compile side code

/-- Challenger decoding does not execute inside the CPU controller. The
emitted code uses canonical unary counters; malformed packets get zero pads. -/
def padTable {capacity length : Nat} (table : Fin capacity → Bits length)
    (request : List Bool) : List Bool :=
  let index := (request.takeWhile id).length
  if h : index < capacity then
    if request = List.replicate index true ++ [false] then (table ⟨index, h⟩).toList
    else List.replicate length false
  else List.replicate length false

@[simp] theorem padTable_length {capacity length : Nat}
    (table : Fin capacity → Bits length) (request : List Bool) :
    (padTable table request).length = length := by
  dsimp only [padTable]
  split
  · split <;> simp
  · simp


private theorem takeWhile_unary (index : Nat) :
    (List.replicate index true ++ [false]).takeWhile id = List.replicate index true := by
  induction index with
  | zero => rfl
  | succ index ih => simp [List.replicate_succ, ih]

@[simp] theorem padTable_unary {capacity length : Nat}
    (table : Fin capacity → Bits length) (index : Fin capacity) :
    padTable table (List.replicate index.val true ++ [false]) = (table index).toList := by
  simp [padTable, index.isLt]

def capacityInput (S : Scheme) (q : Nat → Nat) (n : Nat) : List Bool :=
  List.replicate (min (q n) (S.capacity n)) true

@[simp] theorem capacityInput_length_le (S : Scheme) (q : Nat → Nat) (n : Nat) :
    (capacityInput S q n).length ≤ q n := by simp [capacityInput]

def start (S : Scheme) (q : Nat → Nat) (n : Nat) : CryptoOracle.CounterMasking.Configuration :=
  CryptoOracle.CounterMasking.initial (Machine.encodeSecurityParameter n) (capacityInput S q n)

def reductionTime (S : Scheme) (time : Nat → Nat) (n : Nat) : Nat :=
  CryptoOracle.CounterMasking.Whole.budget (S.length n) (time n)

/-- Whole native execution against each fixed function table and both
message-selection worlds. Target properties are absent from this record. -/
structure SourceExecution (S : Scheme) (time q : Nat → Nat) (code : Interactive.Code) : Prop where
  timePoly : PolynomiallyBounded time
  lengthPoly : PolynomiallyBounded S.length
  queriesPoly : PolynomiallyBounded q
  safe : ∀ n side (table : Fin (S.capacity n) → Bits (S.length n)), CryptoOracle.CounterMasking.Whole.Safe (CryptoOracle.CounterMasking.compile side code) (padTable table)
    (S.length n) (time n) (start S q n)
  queries : ∀ n side (table : Fin (S.capacity n) → Bits (S.length n)) out,
    out ∈ (CryptoOracle.CounterMasking.Whole.sourceRun (CryptoOracle.CounterMasking.compile side code) (padTable table) (time n) (start S q n)).support →
    out.source.reverseTrace.length ≤ q n

structure SourceRealization (S : Scheme) (time q : Nat → Nat)
    (A : ∀ n, Attack (S.length n)) (code : Interactive.Code) : Prop where
  law : ∀ n side (table : Fin (S.capacity n) → Bits (S.length n)),
    (CryptoOracle.CounterMasking.Whole.sourceRun (CryptoOracle.CounterMasking.compile side code) (padTable table) (time n) (start S q n)).map CryptoOracle.CounterMasking.result =
      (runTable (A n) side table).map some
  typedQueries : ∀ n, (A n).BoundedQueries (q n)

structure TargetExecution (S : Scheme) (time q : Nat → Nat) (code : CryptoOracle.CounterMasking.Code) : Prop where
  timePoly : PolynomiallyBounded time
  queriesPoly : PolynomiallyBounded q
  inputPoly : PolynomiallyBounded (fun n => (Machine.encodeSecurityParameter n).length +
    (capacityInput S q n).length)
  halts : ∀ n (table : Fin (S.capacity n) → Bits (S.length n)), CryptoOracle.CounterMasking.HaltsWithin code (CryptoOracle.CounterMasking.Whole.bitOracle (padTable table)) (start S q n) (time n)
  queries : ∀ n (table : Fin (S.capacity n) → Bits (S.length n)) out,
    out ∈ (CryptoOracle.CounterMasking.eval code (CryptoOracle.CounterMasking.Whole.bitOracle (padTable table)) (start S q n) (time n)).support →
      out.reverseTrace.length ≤ q n

structure TargetRealization (S : Scheme) (time q : Nat → Nat)
    (A : ∀ n, PRF.Attack S.toPRF n) (code : CryptoOracle.CounterMasking.Code) : Prop where
  law : ∀ n (table : Fin (S.capacity n) → Bits (S.length n)),
    (CryptoOracle.CounterMasking.eval code (CryptoOracle.CounterMasking.Whole.bitOracle (padTable table)) (start S q n) (time n)).map CryptoOracle.CounterMasking.result =
      (PRF.runTable (A n) table).map some
  typedQueries : ∀ n, (A n).BoundedQueries (q n)

noncomputable def sourceObject (S : Scheme) (time q : Nat → Nat) :
    SecurityObject system .source where
  goal := PRFCounter.goal S
  execution := {
    Resources := Unit
    ExecutesWithin := fun _ code _ => SourceExecution S time q code
    Realizes := fun _ A code _ => SourceRealization S time q A code }
  adversaries := ⟨fun _ A => ∃ code, SourceExecution S time q code ∧ SourceRealization S time q A code⟩
  represented := by
    intro F A h
    obtain ⟨code, exec, real⟩ := h
    exact ⟨code, (), exec, real⟩

noncomputable def targetObject (S : Scheme) (time q : Nat → Nat) :
    SecurityObject system .target where
  goal := PRF.goal S.toPRF
  execution := {
    Resources := Unit
    ExecutesWithin := fun _ code _ => TargetExecution S time q code
    Realizes := fun _ A code _ => TargetRealization S time q A code }
  adversaries := ⟨fun _ A => ∃ code, TargetExecution S time q code ∧ TargetRealization S time q A code⟩
  represented := by
    intro F A h
    obtain ⟨code, exec, real⟩ := h
    exact ⟨code, (), exec, real⟩

theorem compiled_execution (S : Scheme) (time q : Nat → Nat) (side : Bool)
    (code : Interactive.Code) (W : SourceExecution S time q code) :
    TargetExecution S (reductionTime S time) q (CryptoOracle.CounterMasking.compile side code) where
  timePoly := CryptoOracle.CounterMasking.Whole.budget_polynomial W.lengthPoly W.timePoly
  queriesPoly := W.queriesPoly
  inputPoly := by
    apply PolynomiallyBounded.mono _ ((PolynomiallyBounded.id.add
      (PolynomiallyBounded.const 1)).add W.queriesPoly)
    intro n
    simp only [Machine.encodeSecurityParameter, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    have h := capacityInput_length_le S q n
    omega
  halts := fun n table => CryptoOracle.CounterMasking.Whole.halts (CryptoOracle.CounterMasking.compile side code) (padTable table)
    (S.length n) (time n) _ _ (W.safe n side table)
  queries := fun n table => CryptoOracle.CounterMasking.Whole.queries (CryptoOracle.CounterMasking.compile side code) (padTable table)
    (S.length n) (time n) (q n) _ _ (W.safe n side table) (W.queries n side table)

theorem compiled_realization (S : Scheme) (time q : Nat → Nat) (side : Bool)
    (A : ∀ n, Attack (S.length n)) (code : Interactive.Code)
    (exec : SourceExecution S time q code) (real : SourceRealization S time q A code) :
    TargetRealization S (reductionTime S time) q
      (fun n => reduce side 0 (A n)) (CryptoOracle.CounterMasking.compile side code) where
  law := by
    intro n table
    have hw := CryptoOracle.CounterMasking.Whole.run_map (CryptoOracle.CounterMasking.compile side code)
      (padTable table) (S.length n) (time n) _ _ (exec.safe n side table) CryptoOracle.CounterMasking.result
    have hs := congrArg (fun p => p.map some) (simulation table side 0 (A n))
    exact hw.trans ((real.law n side table).trans hs.symm)
  typedQueries := fun n => PRFCounter.queries side 0 (A n) (q n) (real.typedQueries n)

noncomputable def transform (S : Scheme) (time q : Nat → Nat) (side : Bool) :
    CertifiedTransform (sourceObject S time q) (targetObject S (reductionTime S time) q) where
  transform := {
    mapInstance := fun I => I
    reduce := fun _ A => reduce side 0 A }
  compiler := .primitive (.wrap side)
  mapWitness := fun F A W => {
    code := CryptoOracle.CounterMasking.compile side W.code
    resources := ()
    executes := compiled_execution S time q side W.code W.executes
    realizes := compiled_realization S time q side A W.code W.executes W.realizes
    admissible := ⟨CryptoOracle.CounterMasking.compile side W.code, compiled_execution S time q side W.code W.executes,
      compiled_realization S time q side A W.code W.executes W.realizes⟩ }
  code_eq := by intros; rfl

end Foundation.Symmetric.PRFCounter.Resource
