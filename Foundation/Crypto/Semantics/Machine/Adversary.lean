import Foundation.Crypto.Semantics.Machine.Execution
import Foundation.Crypto.Semantics.Security.Bound

universe u v w

namespace Machine

open Foundation.Probability

/-- A finite code and a partial decoder for one type of cryptographic value.
The round-trip law makes the code injective. Effectivity and encoding cost are
separate obligations; this structure alone does not make an operation cheap. -/
structure FiniteBitEncoding (α : Type u) where
  encode : α → List Bool
  decode : List Bool → Option α
  decode_encode : ∀ x, decode (encode x) = some x

namespace FiniteBitEncoding

theorem encode_injective {α : Type u} (E : FiniteBitEncoding α) :
    Function.Injective E.encode := by
  intro x y h
  have := congrArg E.decode h
  simpa [E.decode_encode] using this

def bool : FiniteBitEncoding Bool where
  encode b := [b]
  decode
    | [b] => some b
    | _ => none
  decode_encode := by intro b; rfl

def bitstring : FiniteBitEncoding (List Bool) where
  encode := id
  decode := some
  decode_encode := by intro x; rfl

def unit : FiniteBitEncoding Unit where
  encode _ := []
  decode
    | [] => some ()
    | _ => none
  decode_encode := by intro x; cases x; rfl

end FiniteBitEncoding

/-- Unary security parameter, terminated by `false`. Its length is `n + 1`,
so it cannot hide an exponential-size security parameter in the input. -/
def encodeSecurityParameter (n : Nat) : List Bool :=
  List.replicate n true ++ [false]

/-- Delimit an arbitrary finite field by its unary length before appending it
to a machine input. This is input preparation, not a unit-cost instruction. -/
def frame (bits : List Bool) : List Bool :=
  List.replicate bits.length true ++ [false] ++ bits

set_option linter.checkUnivs false in
/-- A protocol adapter for one `CryptoGoal`. It supplies finite encodings of
the current instance and one current request/response, plus goal-specific
wiring from a probabilistic response oracle to the existing adversary type.
`assemble` never receives a machine program or an entire instance family;
machine output is supplied through the response oracle. A goal-specific
adapter must still justify that its wiring and finite encodings faithfully
represent the intended protocol; this structure alone does not certify their
computational cost. -/
structure MachineAdversaryInterface (P : CryptoGoal.{u}) where
  Request : ∀ (n : Nat), P.Instance n → Type v
  Response : ∀ (n : Nat) (_I : P.Instance n), Type w
  instanceEncoding : ∀ n, FiniteBitEncoding (P.Instance n)
  requestEncoding : ∀ n I, FiniteBitEncoding (Request n I)
  responseEncoding : ∀ n I, FiniteBitEncoding (Response n I)
  fallback : ∀ n I, Response n I
  assemble : ∀ n I,
    (Request n I → ProbComp (Response n I)) → P.Adversary n I

namespace MachineAdversaryInterface

/-- The machine sees only the current parameter, instance code, and current
protocol request. It never receives `F : InstanceFamily P` as an oracle. -/
def machineInput {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (n : Nat) (I : P.Instance n) (request : J.Request n I) : List Bool :=
  encodeSecurityParameter n ++
    frame ((J.instanceEncoding n).encode I) ++
    frame ((J.requestEncoding n I).encode request)

theorem machineInput_length {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (n : Nat) (I : P.Instance n) (request : J.Request n I) :
    (J.machineInput n I request).length =
      n + 3 + 2 * ((J.instanceEncoding n).encode I).length +
        2 * ((J.requestEncoding n I).encode request).length := by
  simp [machineInput, frame, encodeSecurityParameter]
  omega

/-- The framed request code is physically present in the machine input, so
its length cannot exceed the total input length. -/
theorem requestCode_length_le_machineInput {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (n : Nat) (I : P.Instance n) (request : J.Request n I) :
    ((J.requestEncoding n I).encode request).length ≤
      (J.machineInput n I request).length := by
  simp only [machineInput, frame, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- Execute one fixed machine code with a supplied fuel bound. Timeout or an
invalid output code maps to the explicit protocol fallback. Later resource
proofs must show that timeout does not occur for admissible programs. -/
noncomputable def responseWithin {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (p : Program) (budget : Nat → Nat)
    (n : Nat) (I : P.Instance n) (request : J.Request n I) :
    ProbComp (J.Response n I) :=
  let input := J.machineInput n I request
  (evalWithin p input (budget input.length)).map fun code =>
    (code.bind (J.responseEncoding n I).decode).getD (J.fallback n I)

/-- A decoded nonfallback response cannot contain more data than the code
emitted by the machine, when the decoder satisfies this explicit size law.
The machine's bit output itself is bounded by its transition count. -/
theorem responseWithin_size_le_of_mem_support {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (p : Program) (budget : Nat → Nat)
    (n : Nat) (I : P.Instance n) (request : J.Request n I)
    (size : J.Response n I → Nat)
    (hDecode : ∀ bits response,
      (J.responseEncoding n I).decode bits = some response →
        size response ≤ bits.length)
    (response : J.Response n I)
    (hSupport : response ∈ (J.responseWithin p budget n I request).support)
    (hNotFallback : response ≠ J.fallback n I) :
    size response ≤ budget (J.machineInput n I request).length + 1 := by
  unfold responseWithin at hSupport
  rw [PMF.mem_support_map_iff] at hSupport
  rcases hSupport with ⟨code, hCode, hResponse⟩
  cases code with
  | none =>
      simp at hResponse
      exact False.elim (hNotFallback hResponse.symm)
  | some bits =>
      cases hDecoded : (J.responseEncoding n I).decode bits with
      | none =>
          simp [hDecoded] at hResponse
          exact False.elim (hNotFallback hResponse.symm)
      | some value =>
          have hValue : value = response := by simpa [hDecoded] using hResponse
          subst value
          exact (hDecode bits response hDecoded).trans
            (evalWithin_output_length_le p (J.machineInput n I request)
              (budget (J.machineInput n I request).length) bits hCode)

/-- One `p : Program` outside the security-parameter function supplies the
entire adversary family. `budget` is an analysis witness, not machine code. -/
noncomputable def realizeFamily {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (F : InstanceFamily P) (p : Program) (budget : Nat → Nat) :
    AdversaryFamily P F :=
  fun n => J.assemble n (F n) (J.responseWithin p budget n (F n))

theorem responseWithin_append_halt {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (p : Program) (budget : Nat → Nat)
    (n : Nat) (I : P.Instance n) (request : J.Request n I) :
    J.responseWithin (p ++ [.halt]) budget n I request =
      J.responseWithin p budget n I request := by
  simp only [responseWithin, evalWithin_append_halt]

theorem realizeFamily_append_halt {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (F : InstanceFamily P) (p : Program) (budget : Nat → Nat) :
    J.realizeFamily F (p ++ [.halt]) budget = J.realizeFamily F p budget := by
  funext n
  unfold realizeFamily
  congr 1
  funext request
  exact J.responseWithin_append_halt p budget n (F n) request

def Realizes {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (F : InstanceFamily P) (p : Program) (budget : Nat → Nat)
    (A : AdversaryFamily P F) : Prop :=
  J.realizeFamily F p budget = A

/-- Two budgets that halt the same fixed code on every input induce the same
response oracle. No information can be passed through the choice of budget. -/
theorem responseWithin_eq_of_halts {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (p : Program) (budget₁ budget₂ : Nat → Nat)
    (n : Nat) (I : P.Instance n) (request : J.Request n I)
    (h₁ : ∀ input : List Bool,
      HaltsWithin p input (budget₁ input.length))
    (h₂ : ∀ input : List Bool,
      HaltsWithin p input (budget₂ input.length)) :
    J.responseWithin p budget₁ n I request =
      J.responseWithin p budget₂ n I request := by
  dsimp only [responseWithin]
  rw [evalWithin_eq_of_haltsWithin p (J.machineInput n I request)
    (budget₁ (J.machineInput n I request).length)
    (budget₂ (J.machineInput n I request).length)
    (h₁ _) (h₂ _)]

theorem realizeFamily_budget_eq_of_halts {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (F : InstanceFamily P) (p : Program)
    (budget₁ budget₂ : Nat → Nat)
    (h₁ : ∀ input : List Bool,
      HaltsWithin p input (budget₁ input.length))
    (h₂ : ∀ input : List Bool,
      HaltsWithin p input (budget₂ input.length)) :
    J.realizeFamily F p budget₁ = J.realizeFamily F p budget₂ := by
  funext n
  unfold realizeFamily
  congr 1
  funext request
  exact J.responseWithin_eq_of_halts p budget₁ budget₂ n (F n) request h₁ h₂

/-- An external bound on the *entire* machine input for a fixed instance
family. The limit is not yet required to be polynomial. An interface with
unbounded requests will not have such a witness without further restrictions
on which requests are valid or reachable. -/
structure InputSizeBound {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (F : InstanceFamily P) where
  limit : Nat → Nat
  length_le : ∀ n (request : J.Request n (F n)),
    (J.machineInput n (F n) request).length ≤ limit n

end MachineAdversaryInterface

end Machine
