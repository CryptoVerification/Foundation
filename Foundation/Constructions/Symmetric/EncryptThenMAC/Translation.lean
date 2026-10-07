import Foundation.Constructions.Symmetric.EncryptThenMAC.Logic
import Foundation.Constructions.Symmetric.EncryptThenMAC.Operational

/-! The same pure two-assumption rule used for the semantic theorem also
preserves compiler output and complete execution witnesses. Code models need
only finite compiler syntax. Witness models additionally require a realized
backend; this does not assert realizability for arbitrary host functions. -/
namespace Foundation.Symmetric.EncryptThenMAC.Operational

open CryptoLogic.General Foundation.Logic
open scoped ENNReal
universe v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

variable {K : CodeSystem} {auth enc mac : K.Machine}
  {E : Encryption} {M : MAC E.Ciphertext}

/-- Privacy and integrity are observations of the same source attack code.
They use the source machine; they are not new execution primitives. -/
abbrev machine : Logic.Object → K.Machine
  | .encryption => enc
  | .mac => mac
  | .privacy | .integrity | .authenticated => auth

/-- Independently specified compiler interpretation of the three small rules. -/
def lowerCode (cE : Compiler K auth enc) (cM : Compiler K auth mac) (length : Nat) :
    Model Logic.lower where
  Carrier := fun claim => K.Code (machine claim.object) → List (Fin length × Sigma K.Code)
  operation := fun rule children code => match rule with
    | .privacy _ => children 0 (cE.run code)
    | .integrity _ => children 0 (cM.run code)
    | .combine _ _ => children 0 code ++ children 1 code

/-- A finite compiler plan extracted from the lower proof syntax. This
executable path does not evaluate a generic model or a semantic certificate. -/
def plan (cE : Compiler K auth enc) (cM : Compiler K auth mac)
    {Γ : Context Logic.lower} : {A : Logic.Claim} → Derivation Logic.lower Γ A →
      Plan K (fun i => machine (auth := auth) (enc := enc) (mac := mac) (Γ.claim i).object)
        (machine (auth := auth) (enc := enc) (mac := mac) A.object)
  | _, .hypothesis i => .hypothesis i _ rfl
  | _, .apply (Logic.Rule.privacy _) children => .unary cE (plan cE cM (children 0))
  | _, .apply (Logic.Rule.integrity _) children => .unary cM (plan cE cM (children 0))
  | _, .apply (Logic.Rule.combine _ _) children => .binary (.identity auth) (.identity auth)
      (plan cE cM (children 0)) (plan cE cM (children 1))

/-- The executable plan implements exactly the independent code model. -/
theorem plan_run (cE : Compiler K auth enc) (cM : Compiler K auth mac)
    {Γ : Context Logic.lower} {A : Logic.Claim} (d : Derivation Logic.lower Γ A) :
    (plan cE cM d).run = d.eval (lowerCode cE cM Γ.length)
      (fun i code => [(i, ⟨machine (Γ.claim i).object, code⟩)]) := by
  refine Derivation.rec
    (motive := fun A d => (plan cE cM d).run = d.eval (lowerCode cE cM Γ.length)
      (fun i code => [(i, ⟨machine (Γ.claim i).object, code⟩)]))
    (fun _ => rfl) (fun rule children ih => ?_) d
  cases rule with
  | privacy ε =>
      change (fun code => (plan cE cM (children 0)).run (cE.run code)) = _
      rw [ih 0]
      rfl
  | integrity ε =>
      change (fun code => (plan cE cM (children 0)).run (cM.run code)) = _
      rw [ih 0]
      rfl
  | combine ε δ =>
      change (fun code => (plan cE cM (children 0)).run code ++
        (plan cE cM (children 1)).run code) = _
      rw [ih 0, ih 1]
      rfl

/-- The high rule emits both compiled attacks directly, in premise order. -/
def higherCode (cE : Compiler K auth enc) (cM : Compiler K auth mac) (length : Nat) :
    Model Logic.higher where
  Carrier := fun claim => K.Code (machine claim.object) → List (Fin length × Sigma K.Code)
  operation := fun _ children code => children 0 (cE.run code) ++ children 1 (cM.run code)

def codePreservation (cE : Compiler K auth enc) (cM : Compiler K auth mac) (length : Nat) :
    Model.Hom (higherCode cE cM length) (Logic.expansion.pullback (lowerCode cE cM length)) where
  map := fun _ value => value
  preserves := by intro rule children; cases rule; rfl

/-- Code preservation for every high-level proof, every context, and every
premise continuation. No security interpretation is needed for generation. -/
theorem code_preserved (cE : Compiler K auth enc) (cM : Compiler K auth mac) (length : Nat)
    {Γ : Context Logic.higher} {A} (d : Derivation Logic.higher Γ A)
    (environment : ∀ i, (higherCode cE cM length).Carrier (Γ.claim i)) :
    (Logic.expansion.translate d).eval (lowerCode cE cM length) environment =
      d.eval (higherCode cE cM length) environment :=
  Translation.eval_preserving Logic.expansion (codePreservation cE cM length) environment d

/-- The fixed two-assumption derivation emits exactly the two registered
finite compiler outputs, retaining their distinct premise indices. -/
theorem proof_codes (cE : Compiler K auth enc) (cM : Compiler K auth mac)
    (code : K.Code auth) :
    (Logic.expansion.translate Logic.proof).eval (lowerCode cE cM 2)
      (fun i input => [(i, ⟨machine (Logic.context.claim i).object, input⟩)]) code =
        [(0, ⟨enc, cE.run code⟩), (1, ⟨mac, cM.run code⟩)] := rfl

/-- A small finite plan realizes the two-assumption rule's exact outputs. -/
theorem proof_plan (cE : Compiler K auth enc) (cM : Compiler K auth mac)
    (code : K.Code auth) :
    (plan cE cM (Logic.expansion.translate Logic.proof)).run code =
      [(0, ⟨enc, cE.run code⟩), (1, ⟨mac, cM.run code⟩)] := by
  rw [plan_run]
  exact proof_codes cE cM code

noncomputable abbrev object (X : Backend.{v} K auth (goal E M))
    (Y : Backend.{v} K enc (encryptionGoal E)) (Z : Backend.{v} K mac (macGoal E M)) :
    (o : Logic.Object) → SecurityObject K (machine (auth := auth) (enc := enc) (mac := mac) o)
  | .encryption => Y.object
  | .mac => Z.object
  | .privacy | .integrity | .authenticated => X.object

abbrev family (X : Backend.{v} K auth (goal E M))
    (Y : Backend.{v} K enc (encryptionGoal E)) (Z : Backend.{v} K mac (macGoal E M)) :
    (o : Logic.Object) → InstanceFamily (object X Y Z o).goal
  | .encryption | .mac | .privacy | .integrity | .authenticated => fun _ => ()

/-- An input retains its actual adversary and all execution evidence. -/
abbrev Input (X : Backend.{v} K auth (goal E M))
    (Y : Backend.{v} K enc (encryptionGoal E)) (Z : Backend.{v} K mac (macGoal E M))
    (o : Logic.Object) :=
  Σ A : AdversaryFamily (object X Y Z o).goal (family X Y Z o),
    (object X Y Z o).Witness (family X Y Z o) A

abbrev WitnessOutput (X : Backend.{v} K auth (goal E M))
    (Y : Backend.{v} K enc (encryptionGoal E)) (Z : Backend.{v} K mac (macGoal E M))
    (length : Nat) := Fin length × Σ o : Logic.Object, Input X Y Z o

variable {X : Backend.{v} K auth (goal E M)}
  {Y : Backend.{v} K enc (encryptionGoal E)} {Z : Backend.{v} K mac (macGoal E M)}
  {cE : Compiler K auth enc} {cM : Compiler K auth mac}

/-- The lower interpretation separately maps each execution witness, then
concatenates the certified outputs. No resource units are converted. -/
noncomputable def lowerWitnesses (R : Realization X Y Z cE cM) (length : Nat) : Model Logic.lower where
  Carrier := fun claim => Input X Y Z claim.object → List (WitnessOutput X Y Z length)
  operation := fun rule children input => match rule with
    | .privacy _ => children 0 ⟨fun n => privacyReduction E M n (input.1 n).1,
        R.encryptionWitness _ _ input.2⟩
    | .integrity _ => children 0 ⟨fun n => integrityReduction E M n (input.1 n).2,
        R.macWitness _ _ input.2⟩
    | .combine _ _ => children 0 input ++ children 1 input

/-- The high interpretation returns the two full certificates directly. -/
noncomputable def higherWitnesses (R : Realization X Y Z cE cM) (length : Nat) : Model Logic.higher where
  Carrier := fun claim => Input X Y Z claim.object → List (WitnessOutput X Y Z length)
  operation := fun _ children input =>
    children 0 ⟨fun n => privacyReduction E M n (input.1 n).1,
      R.encryptionWitness _ _ input.2⟩ ++
    children 1 ⟨fun n => integrityReduction E M n (input.1 n).2,
      R.macWitness _ _ input.2⟩

def witnessPreservation (R : Realization X Y Z cE cM) (length : Nat) :
    Model.Hom (higherWitnesses R length) (Logic.expansion.pullback (lowerWitnesses R length)) where
  map := fun _ value => value
  preserves := by intro rule children; cases rule; rfl

/-- Exact equality includes code, resources, stopping, realization, and
admissibility evidence, for arbitrary high derivations and continuations. -/
theorem witnesses_preserved (R : Realization X Y Z cE cM) (length : Nat)
    {Γ : Context Logic.higher} {A} (d : Derivation Logic.higher Γ A)
    (environment : ∀ i, (higherWitnesses R length).Carrier (Γ.claim i)) :
    (Logic.expansion.translate d).eval (lowerWitnesses R length) environment =
      d.eval (higherWitnesses R length) environment :=
  Translation.eval_preserving Logic.expansion (witnessPreservation R length) environment d

/-- Erasure reveals the exact finite program certified by an output. -/
def WitnessOutput.emitted (out : WitnessOutput X Y Z length) : Fin length × Sigma K.Code :=
  (out.1, ⟨machine out.2.1, out.2.2.2.code⟩)

/-- Every high derivation certifies precisely its independently generated
code, provided the premise continuations certify their own emitted code. -/
theorem higher_witnesses_emitted (R : Realization X Y Z cE cM) (length : Nat)
    {Γ : Context Logic.higher} {C} (d : Derivation Logic.higher Γ C)
    (witnessEnv : ∀ i, (higherWitnesses R length).Carrier (Γ.claim i))
    (codeEnv : ∀ i, (higherCode cE cM length).Carrier (Γ.claim i))
    (hypotheses : ∀ i input, (witnessEnv i input).map WitnessOutput.emitted =
      codeEnv i input.2.code) (input : Input X Y Z C.object) :
    (d.eval (higherWitnesses R length) witnessEnv input).map WitnessOutput.emitted =
      d.eval (higherCode cE cM length) codeEnv input.2.code := by
  induction d with
  | hypothesis i => exact hypotheses i input
  | apply rule children ih =>
      rcases rule with ⟨ε, δ⟩
      change ((children 0).eval (higherWitnesses R length) witnessEnv
        ⟨fun n => privacyReduction E M n (input.1 n).1, R.encryptionWitness _ _ input.2⟩ ++
        (children 1).eval (higherWitnesses R length) witnessEnv
          ⟨fun n => integrityReduction E M n (input.1 n).2, R.macWitness _ _ input.2⟩).map _ = _
      rw [List.map_append, ih 0, ih 1]
      simp only [R.encryptionCode, R.macCode]
      rfl

/-- Expansion preserves the link between full witnesses and finite code for
all high-level proofs, not only for the fixed two-premise example. -/
theorem translated_witnesses_emitted (R : Realization X Y Z cE cM) (length : Nat)
    {Γ : Context Logic.higher} {C} (d : Derivation Logic.higher Γ C)
    (witnessEnv : ∀ i, (higherWitnesses R length).Carrier (Γ.claim i))
    (codeEnv : ∀ i, (higherCode cE cM length).Carrier (Γ.claim i))
    (hypotheses : ∀ i input, (witnessEnv i input).map WitnessOutput.emitted =
      codeEnv i input.2.code) (input : Input X Y Z C.object) :
    ((Logic.expansion.translate d).eval (lowerWitnesses R length) witnessEnv input).map
      WitnessOutput.emitted =
      (Logic.expansion.translate d).eval (lowerCode cE cM length) codeEnv input.2.code := by
  rw [witnesses_preserved, code_preserved]
  exact higher_witnesses_emitted R length d witnessEnv codeEnv hypotheses input

/-- Extract the full target witnesses by evaluating the translated pure proof. -/
noncomputable def proofWitnesses (R : Realization X Y Z cE cM)
    (A : AdversaryFamily (goal E M) (fun _ => ())) (W : X.object.Witness (fun _ => ()) A) :
    List (WitnessOutput X Y Z 2) :=
  (Logic.expansion.translate Logic.proof).eval (lowerWitnesses R 2)
    (fun i input => [(i, ⟨(Logic.context.claim i).object, input⟩)]) ⟨A, W⟩

/-- The witness list retains both resources exactly as chosen by the actual
realization; it is not an existentially selected alternative certificate. -/
theorem proof_witnesses (R : Realization X Y Z cE cM)
    (A : AdversaryFamily (goal E M) (fun _ => ())) (W : X.object.Witness (fun _ => ()) A) :
    proofWitnesses R A W =
      [(0, ⟨.encryption, ⟨fun n => privacyReduction E M n (A n).1,
        R.encryptionWitness _ _ W⟩⟩),
       (1, ⟨.mac, ⟨fun n => integrityReduction E M n (A n).2,
        R.macWitness _ _ W⟩⟩)] := rfl

theorem proof_witnesses_emitted (R : Realization X Y Z cE cM)
    (A : AdversaryFamily (goal E M) (fun _ => ())) (W : X.object.Witness (fun _ => ()) A) :
    (proofWitnesses R A W).map WitnessOutput.emitted =
      (Logic.expansion.translate Logic.proof).eval (lowerCode cE cM 2)
        (fun i input => [(i, ⟨machine (Logic.context.claim i).object, input⟩)]) W.code := by
  rw [proof_witnesses, proof_codes]
  simp only [List.map_cons, List.map_nil, WitnessOutput.emitted,
    R.encryptionCode, R.macCode]

/-- Every code emitted by the executable plan has its complete execution
certificate in the same ordered output list. -/
theorem proof_witnesses_plan (R : Realization X Y Z cE cM)
    (A : AdversaryFamily (goal E M) (fun _ => ())) (W : X.object.Witness (fun _ => ()) A) :
    (proofWitnesses R A W).map WitnessOutput.emitted =
      (plan cE cM (Logic.expansion.translate Logic.proof)).run W.code := by
  rw [plan_run]
  exact proof_witnesses_emitted R A W

/-- Numeric loss interpretation, separate from code and CPU resources. -/
def lowerLoss (length : Nat) : Model Logic.lower where
  Carrier := fun _ => (Fin length → Nat → ℝ≥0∞) → Nat → ℝ≥0∞
  operation := fun rule children => match rule with
    | .privacy _ | .integrity _ => children 0
    | .combine _ _ => fun ε n => children 0 ε n + children 1 ε n

def higherLoss (length : Nat) : Model Logic.higher where
  Carrier := fun _ => (Fin length → Nat → ℝ≥0∞) → Nat → ℝ≥0∞
  operation := fun _ children ε n => children 0 ε n + children 1 ε n

def lossPreservation (length : Nat) : Model.Hom (higherLoss length)
    (Logic.expansion.pullback (lowerLoss length)) where
  map := fun _ value => value
  preserves := by intro rule children; cases rule; rfl

theorem loss_preserved (length : Nat) {Γ : Context Logic.higher} {A}
    (d : Derivation Logic.higher Γ A) (environment : ∀ i, (higherLoss length).Carrier (Γ.claim i)) :
    (Logic.expansion.translate d).eval (lowerLoss length) environment =
      d.eval (higherLoss length) environment :=
  Translation.eval_preserving Logic.expansion (lossPreservation length) environment d

theorem proof_loss (ε : Fin 2 → Nat → ℝ≥0∞) (n : Nat) :
    (Logic.expansion.translate Logic.proof).eval (lowerLoss 2) (fun i ε n => ε i n) ε n =
      ε 0 n + ε 1 n := rfl

/-- The semantic theorem now applies to the source backend's actual
adversary class, using admissibility obtained from execution witnesses. -/
theorem Realization.bounded (R : Realization X Y Z cE cM) (ε δ : Nat → ℝ≥0∞)
    (hE : BoundedByOnWithin (encryptionGoal E) Y.adversaries (fun _ => ()) ε)
    (hM : BoundedByOnWithin (macGoal E M) Z.adversaries (fun _ => ()) δ) :
    BoundedByOnWithin (goal E M) X.adversaries (fun _ => ()) (fun n => ε n + δ n) := by
  intro A hA n
  exact Logic.bounded E M Y.adversaries Z.adversaries ε δ hE hM A (R.admissibility A hA) n

/-- The compiler outputs both stop within their own backend resources.
The theorem does not identify CPU time with query counts. -/
theorem Realization.compiled_executes (R : Realization X Y Z cE cM)
    (A : AdversaryFamily (goal E M) (fun _ => ())) (W : X.object.Witness (fun _ => ()) A) :
    Y.execution.ExecutesWithin (fun _ => ()) (cE.run W.code)
      (R.encryptionWitness _ _ W).resources ∧
    Z.execution.ExecutesWithin (fun _ => ()) (cM.run W.code)
      (R.macWitness _ _ W).resources := by
  constructor
  · exact R.encryption_executes _ _ W
  · rw [← R.macCode]
    exact (R.macWitness _ _ W).executes

/-- Both exact finite outputs realize the semantic reductions used by the
translated safety proof; each retains its own certified resource value. -/
theorem Realization.compiled_realizes (R : Realization X Y Z cE cM)
    (A : AdversaryFamily (goal E M) (fun _ => ())) (W : X.object.Witness (fun _ => ()) A) :
    Y.execution.Realizes (fun _ => ()) (fun n => privacyReduction E M n (A n).1)
      (cE.run W.code) (R.encryptionWitness _ _ W).resources ∧
    Z.execution.Realizes (fun _ => ()) (fun n => integrityReduction E M n (A n).2)
      (cM.run W.code) (R.macWitness _ _ W).resources := by
  constructor
  · rw [← R.encryptionCode]
    exact (R.encryptionWitness _ _ W).realizes
  · rw [← R.macCode]
    exact (R.macWitness _ _ W).realizes

end Foundation.Symmetric.EncryptThenMAC.Operational
