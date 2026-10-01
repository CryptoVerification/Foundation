import Foundation.Constructions.ElGamal.MachineMultiplication
import Foundation.Machine.ChooseChallengeCompletion
import Foundation.Machine.ChooseChallengeRuntime
import Foundation.Machine.Compiler

namespace ElGamal.RepresentedChooseNormalizer

open Machine Machine.GuardedCompiler

variable
  {sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)}
  {X : Nat → Type 1} {embed : ∀ n, X n → ConcreteInstance sampling n}
  {M : RepresentedMachinePrimitives sampling X embed}

/-- Executable finite-code construction. The same source adversary code is
embedded for choose and guess. Only the fixed normalizer and multiplication
codes are supplied by the representation certificates; no family, current
instance, security parameter or group value is inspected by this compiler. -/
def simulatorCode (N : RepresentedChooseNormalizer M) (source : Program) : Program :=
  chooseChallengeGuessCompile source N.program M.multiplyProgram source

/-- The same fixed construction as finite executable compiler syntax.
Neither a family nor an instance-dependent semantic function is contained
in this compiler; its payload consists only of ordinary finite machine code. -/
def simulatorCompiler (N : RepresentedChooseNormalizer M) : ProgramCompiler :=
  .chooseChallenge N.program M.multiplyProgram

@[simp] theorem simulatorCompiler_run (N : RepresentedChooseNormalizer M) (source : Program) :
    N.simulatorCompiler.run source = N.simulatorCode source := rfl

theorem simulatorCode_length (N : RepresentedChooseNormalizer M) (source : Program) :
    (N.simulatorCode source).length =
      136 * source.length + 68 * N.program.length + 68 * M.multiplyProgram.length + 1764 := by
  rw [simulatorCode, chooseChallengeGuessCompile_length]
  omega

/-- The finite common branch bound of the actual simulator invocation.
This is a step-count specification, not code used to manufacture the reply.
Polynomial closure and universal malformed-input termination are proved
in `MachineSimulatorRuntime`; the definition itself is analysis data. -/
def simulatorTailBudget (N : RepresentedChooseNormalizer M) (source : Program) (q : Nat → Nat)
    (n : Nat) (x : X n) (first second last : (embed n x).params.Element) : Nat :=
  let I := (M.instanceCode n).encode x
  let E := M.elementCode n x
  let messages := fun c : Configuration => interpretChooseResponse E (embed n x).params.generator c.outputBits
  chooseChallengeTailBudget source q N.budget M.multiplyBudget q n I
    (E.encode first) (E.encode second) (E.encode last)
    (fun c => E.encode (messages c).1) (fun c => E.encode (messages c).2.1) (fun c => (messages c).2.2)
    (fun c bit => E.encode ((embed n x).params.mul (if bit then (messages c).2.1 else (messages c).1) last))

def simulatorBudget (N : RepresentedChooseNormalizer M) (source : Program) (q : Nat → Nat)
    (n : Nat) (x : X n) (first second last : (embed n x).params.Element) : Nat :=
  chooseTraceBudget q n ((M.instanceCode n).encode x) ((M.elementCode n x).encode first)
      (FiniteBitEncoding.delimit ((M.elementCode n x).encode second) ++ (M.elementCode n x).encode last) +
    (N.simulatorTailBudget source q n x first second last + 1)

private theorem delimited_head_tail (field rest : List Bool) :
    (FiniteBitEncoding.delimit field ++ rest).headD false ::
      (FiniteBitEncoding.delimit field ++ rest).tail = FiniteBitEncoding.delimit field ++ rest := by
  cases field <;> rfl

/-- The complete native simulator runs from the initial encoded DDH tuple.
Its choose distribution, fair challenge, genuine encoded group product,
guess distribution and final comparison agree with the specified protocol.
Malformed choose outputs are normalized by `N.correct`, with exactly the
existing adapter's fallback policy. This theorem constructs no external
abstract program transformation and invokes no free group instruction. -/
theorem nativeSimulator_eval (N : RepresentedChooseNormalizer M) (source : Program) (q : Nat → Nat)
    (hSource : ∀ input, HaltsWithin source input (q input.length))
    (n : Nat) (x : X n) (first second last : (embed n x).params.Element) :
    let I := (M.instanceCode n).encode x
    let E := M.elementCode n x
    let request := encodeSecurityParameter n ++ frame I ++ frame (false :: E.encode first)
    let messages := fun c : Configuration => interpretChooseResponse E (embed n x).params.generator c.outputBits
    let product := fun c (bit : Bool) => E.encode ((embed n x).params.mul
      (if bit then (messages c).2.1 else (messages c).1) last)
    (evalConfigWithin (N.simulatorCode source)
      (Configuration.initial (encodeSecurityParameter n ++ frame I ++
        frame (FiniteBitEncoding.delimit (E.encode first) ++ FiniteBitEncoding.delimit (E.encode second) ++ E.encode last)))
      (N.simulatorBudget source q n x first second last)).map (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin source (preparedSource request) (q request.length)).bind (fun c =>
        Foundation.Probability.sampleBit.bind (fun bit =>
          (evalConfigWithin source (preparedSource (guessFromProductRequest n I (E.encode second) (messages c).2.2 (product c bit)))
            (q (guessFromProductRequest n I (E.encode second) (messages c).2.2 (product c bit)).length)).map
              (fun d => (true, [taggedGuessValue d.outputBits == bit])))) := by
  dsimp only
  let I := (M.instanceCode n).encode x
  let E := M.elementCode n x
  let keyTail := FiniteBitEncoding.delimit (E.encode second) ++ E.encode last
  let tuple := FiniteBitEncoding.delimit (E.encode first) ++ FiniteBitEncoding.delimit (E.encode second) ++ E.encode last
  let messages := fun c : Configuration => interpretChooseResponse E (embed n x).params.generator c.outputBits
  have hRest : keyTail.headD false :: keyTail.tail = keyTail := delimited_head_tail _ _
  have hTuple : tuple.headD false :: tuple.tail = tuple := by
    dsimp only [tuple]
    rw [List.append_assoc]
    exact delimited_head_tail _ _
  have h := chooseChallengeGuessCompile_correct source N.program M.multiplyProgram source
    q N.budget M.multiplyBudget q n I (E.encode first) (E.encode second) (E.encode last)
    (keyTail.headD false) (tuple.headD false) keyTail.tail tuple.tail hRest hTuple
    (fun c => E.encode (messages c).1) (fun c => E.encode (messages c).2.1) (fun c => (messages c).2.2)
    (fun c bit => E.encode ((embed n x).params.mul (if bit then (messages c).2.1 else (messages c).1) last))
    (hSource _) N.halts (by
      intro c _hc
      simpa only [normalizeChooseResponse_eq_canonical] using N.correct n x c.outputBits)
    M.multiplyHalts (by
      intro c _hc bit
      cases bit <;> exact M.multiply_correct n x _ last) hSource
  simpa only [hRest, keyTail, simulatorCode, simulatorBudget, simulatorTailBudget, List.append_assoc] using h

/-- Universal halting over the source choose, normalizer, native challenge,
group multiplication and source guess branches on this encoded tuple.
This pointwise certificate supplies semantic evaluation fuel. The separate
`nativeSimulator_polynomialTime` theorem also covers malformed DDH requests. -/
theorem nativeSimulator_haltsWithin (N : RepresentedChooseNormalizer M) (source : Program) (q : Nat → Nat)
    (hSource : ∀ input, HaltsWithin source input (q input.length))
    (n : Nat) (x : X n) (first second last : (embed n x).params.Element) :
    HaltsWithin (N.simulatorCode source)
      (encodeSecurityParameter n ++ frame ((M.instanceCode n).encode x) ++
        frame (FiniteBitEncoding.delimit ((M.elementCode n x).encode first) ++
          FiniteBitEncoding.delimit ((M.elementCode n x).encode second) ++ (M.elementCode n x).encode last))
      (N.simulatorBudget source q n x first second last) := by
  intro c run
  have hm := (PMF.mem_support_map_iff (fun d : Configuration => (d.halted, d.outputBits)) _
    (c.halted, c.outputBits)).mpr ⟨c, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [N.nativeSimulator_eval source q hSource n x first second last, PMF.mem_support_bind_iff] at hm
  obtain ⟨chooseResult, _hc, hm⟩ := hm
  rw [PMF.mem_support_bind_iff] at hm
  obtain ⟨bit, _hb, hm⟩ := hm
  rw [PMF.mem_support_map_iff] at hm
  obtain ⟨guessResult, _hg, heq⟩ := hm
  exact (congrArg Prod.fst heq).symm

end ElGamal.RepresentedChooseNormalizer
