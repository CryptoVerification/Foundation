import Foundation.Constructions.ElGamal.PrimeOrderArithmetic
import Foundation.Constructions.ElGamal.MachineNormalization
import Foundation.Crypto.Semantics.Machine.BinaryIsOne
import Foundation.Crypto.Semantics.Machine.BinaryPowerIsOne
import Foundation.Crypto.Semantics.Machine.DelimitedTripleWidthCheck
import Foundation.Crypto.Semantics.Machine.ChooseFirstWidthPrefix
import Foundation.Crypto.Semantics.Machine.ChooseTwoWidthsPrefix
import Foundation.Crypto.Semantics.Machine.DelimitedTapeComparison
import Foundation.Crypto.Semantics.Machine.ChooseSecondRangeCheck
import Foundation.Crypto.Semantics.Machine.ChooseTwoRanges
import Foundation.Crypto.Semantics.Machine.ChooseRangeValidation
import Foundation.Crypto.Semantics.Machine.ChooseRangeDecision
import Foundation.Crypto.Semantics.Machine.ChooseWidthDecision
import Foundation.Crypto.Semantics.Machine.ChooseAcceptedOutput
import Foundation.Crypto.Semantics.Machine.ChooseDefaultOutput
import Foundation.Crypto.Semantics.Machine.FramedChooseDefaultOutput

namespace ElGamal.PrimeOrderRepresentation

/-- A native two-tape scan compares a delimited candidate against the
modulus field of the actual represented instance. It retains the remaining
`q,g` bits and writes the range decision at the candidate delimiter. The
connection from the framed choose prefix to these head positions remains a
separate machine-code obligation. -/
theorem candidateRange_eval (n : Nat) (x : Domain n)
    (candidate tail : List Bool)
    (beforeInput beforeOutput : List (Option Bool))
    (hWidth : candidate.length = n + 3) :
    ∃ finish,
      Machine.evalConfigWithin Machine.DelimitedTapeComparison.program
        (Machine.DelimitedTapeComparison.state Ordering.eq beforeInput beforeOutput
          (Machine.FiniteBitEncoding.delimit candidate ++ tail)
          ((instanceCode n).encode x))
        (7 * candidate.length + 3) = PMF.pure finish ∧
      finish.halted = true ∧
      finish.inputTape.current =
        some (decide (Machine.Binary.value candidate < x.down.modulus)) := by
  let modulusCode := Machine.Binary.encode (n + 3) x.down.modulus
  let suffix := Machine.Binary.encode (n + 3) x.down.scalarOrder ++
    Machine.Binary.encode (n + 3) x.down.generator.val.val
  have hCode : ((instanceCode n).encode x) = modulusCode ++ suffix := by
    simp [instanceCode, PrimeOrderParameters.instanceCode, modulusCode, suffix,
      List.append_assoc]
  rw [hCode]
  obtain ⟨finish, hEval, hHalt, hStatus⟩ :=
    Machine.DelimitedTapeComparison.eval_lt beforeInput beforeOutput
      candidate modulusCode tail suffix (by simp [modulusCode, hWidth])
  refine ⟨finish, hEval, hHalt, ?_⟩
  simpa [modulusCode, Machine.Binary.value_encode x.down.modulus_lt] using hStatus

/-- On a correctly framed choose reply with two fixed-width fields, one
connected finite program performs the second field's range test against
the actual encoded modulus. This result uses the operational trace of the
parser, both width checks, the rewind, and the comparator. -/
theorem chooseSecondRange_runs (n : Nat) (x : Domain n)
    (first second state : List Bool)
    (hFirst : first.length = n + 3)
    (hSecond : second.length = n + 3) :
    let reply := Machine.canonicalMessageBits first second state
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame reply
    ∃ target used,
      Machine.RunsFor Machine.ChooseSecondRangeCheck.program
        (Machine.Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.current =
        some (decide (Machine.Binary.value second < x.down.modulus)) := by
  let modulusCode := Machine.Binary.encode (n + 3) x.down.modulus
  let suffix := Machine.Binary.encode (n + 3) x.down.scalarOrder ++
    Machine.Binary.encode (n + 3) x.down.generator.val.val
  have hCode : ((instanceCode n).encode x) = modulusCode ++ suffix := by
    simp [instanceCode, PrimeOrderParameters.instanceCode, modulusCode, suffix,
      List.append_assoc]
  have hInstance : (modulusCode ++ suffix).length = 3 * (n + 3) := by
    rw [← hCode, instanceCode_length]
  obtain ⟨target, used, run, hHalt, hStatus, _, _⟩ :=
    Machine.ChooseSecondRangeCheck.runs_second_range n (n + 3)
      modulusCode suffix first second state
      (by simp [modulusCode]) hInstance hFirst hSecond
  refine ⟨target, used, ?_, hHalt, ?_⟩
  · simpa [Machine.canonicalMessageBits, hCode] using run
  · simpa [modulusCode, Machine.Binary.value_encode x.down.modulus_lt]
      using hStatus

/-- The connected finite parser, two width checks, two tape rewinds, and
two numeric comparisons execute on the actual prime-order instance code.
The resulting tape contains both range decisions at the original response
delimiters. This is still short of subgroup validation and normalization. -/
theorem chooseTwoRanges_runs (n : Nat) (x : Domain n)
    (first second state : List Bool)
    (hFirst : first.length = n + 3)
    (hSecond : second.length = n + 3) :
    let modulusCode := Machine.Binary.encode (n + 3) x.down.modulus
    let suffix := Machine.Binary.encode (n + 3) x.down.scalarOrder ++
      Machine.Binary.encode (n + 3) x.down.generator.val.val
    let reply := Machine.canonicalMessageBits first second state
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame reply
    let before := some false :: List.replicate reply.length (some true) ++
      ((instanceCode n).encode x).reverse.map some ++
        some false :: List.replicate ((instanceCode n).encode x).length (some true) ++
          some false :: List.replicate n (some true)
    let compared := Machine.DelimitedTapeComparison.done
      (Machine.BinaryComparison.compare Ordering.eq (first.zip modulusCode))
      ((Machine.DelimitedTapeComparison.marked first).reverse.map some ++
        some false :: before)
      (modulusCode.reverse.map some)
      (Machine.DelimitedTapeComparison.marked second ++
        (Machine.BinaryComparison.compare Ordering.eq (second.zip modulusCode) == Ordering.lt)
          :: state) suffix
    ∃ target used,
      Machine.RunsFor Machine.ChooseTwoRanges.program
        (Machine.Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent compared.inputTape ∧
      target.outputTape.Equivalent compared.outputTape := by
  let modulusCode := Machine.Binary.encode (n + 3) x.down.modulus
  let suffix := Machine.Binary.encode (n + 3) x.down.scalarOrder ++
    Machine.Binary.encode (n + 3) x.down.generator.val.val
  have hCode : ((instanceCode n).encode x) = modulusCode ++ suffix := by
    simp [instanceCode, PrimeOrderParameters.instanceCode, modulusCode, suffix,
      List.append_assoc]
  have hInstance : (modulusCode ++ suffix).length = 3 * (n + 3) := by
    rw [← hCode, instanceCode_length]
  obtain ⟨target, used, run, hHalt, hInput, hOutput⟩ :=
    Machine.ChooseTwoRanges.runs_both_ranges_layout n (n + 3)
      modulusCode suffix first second state
      (by simp [modulusCode]) hInstance hFirst hSecond
  refine ⟨target, used, ?_, hHalt, ?_, ?_⟩
  · simpa [Machine.canonicalMessageBits, hCode] using run
  · simpa [Machine.canonicalMessageBits, hCode, List.map_reverse] using hInput
  · simpa [Machine.canonicalMessageBits, hCode, List.map_reverse] using hOutput

theorem chooseTwoRanges_decisions (n : Nat) (x : Domain n)
    (first second state : List Bool)
    (hFirst : first.length = n + 3)
    (hSecond : second.length = n + 3) :
    let reply := Machine.canonicalMessageBits first second state
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame reply
    ∃ target used,
      Machine.RunsFor Machine.ChooseTwoRanges.program
        (Machine.Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.current =
        some (decide (Machine.Binary.value first < x.down.modulus)) ∧
      target.inputTape.right.getD
        (Machine.DelimitedTapeComparison.marked second).length none =
        some (decide (Machine.Binary.value second < x.down.modulus)) := by
  let modulusCode := Machine.Binary.encode (n + 3) x.down.modulus
  let suffix := Machine.Binary.encode (n + 3) x.down.scalarOrder ++
    Machine.Binary.encode (n + 3) x.down.generator.val.val
  have hCode : ((instanceCode n).encode x) = modulusCode ++ suffix := by
    simp [instanceCode, PrimeOrderParameters.instanceCode, modulusCode, suffix,
      List.append_assoc]
  have hInstance : (modulusCode ++ suffix).length = 3 * (n + 3) := by
    rw [← hCode, instanceCode_length]
  obtain ⟨target, used, run, hHalt, hFirstDecision, hSecondDecision⟩ :=
    Machine.ChooseTwoRanges.runs_both_ranges_decisions n (n + 3)
      modulusCode suffix first second state
      (by simp [modulusCode]) hInstance hFirst hSecond
  refine ⟨target, used, ?_, hHalt, ?_, ?_⟩
  · simpa [Machine.canonicalMessageBits, hCode] using run
  · simpa [modulusCode, Machine.Binary.value_encode x.down.modulus_lt]
      using hFirstDecision
  · simpa [modulusCode, Machine.Binary.value_encode x.down.modulus_lt]
      using hSecondDecision

/-- The connected finite code combines both range decisions on the actual
prime-order request. The resulting status is a numerical-range condition;
subgroup membership is still required before accepting the reply. -/
theorem chooseRangeValidation_runs (n : Nat) (x : Domain n)
    (first second state : List Bool)
    (hFirst : first.length = n + 3)
    (hSecond : second.length = n + 3) :
    let reply := Machine.canonicalMessageBits first second state
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame reply
    ∃ target used,
      Machine.RunsFor Machine.ChooseRangeValidation.program
        (Machine.Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.outputTape.left.getD 0 none =
        some (decide (Machine.Binary.value first < x.down.modulus ∧
          Machine.Binary.value second < x.down.modulus)) := by
  let modulusCode := Machine.Binary.encode (n + 3) x.down.modulus
  let suffix := Machine.Binary.encode (n + 3) x.down.scalarOrder ++
    Machine.Binary.encode (n + 3) x.down.generator.val.val
  have hCode : ((instanceCode n).encode x) = modulusCode ++ suffix := by
    simp [instanceCode, PrimeOrderParameters.instanceCode, modulusCode, suffix,
      List.append_assoc]
  have hInstance : (modulusCode ++ suffix).length = 3 * (n + 3) := by
    rw [← hCode, instanceCode_length]
  obtain ⟨target, used, run, hHalt, hStatus⟩ :=
    Machine.ChooseRangeValidation.runs_matching_decisions n (n + 3)
      modulusCode suffix first second state
      (by simp [modulusCode]) hInstance hFirst hSecond
  refine ⟨target, used, ?_, hHalt, ?_⟩
  · simpa [Machine.canonicalMessageBits, hCode] using run
  · simpa [modulusCode, Machine.Binary.value_encode x.down.modulus_lt]
      using hStatus

/-- The serialized `p ++ q ++ g` instance has three physical cells for each
element-code bit. The native delimited-field checker can therefore use the
unseparated instance code itself as its width counter. This is a standalone
machine invocation, not yet the connected choose normalizer. -/
theorem instanceCounter_width_status (n : Nat) (x : Domain n)
    (field tail : List Bool) (beforeInput beforeOutput : List (Option Bool)) :
    (Machine.evalConfigWithin Machine.DelimitedTripleWidthCheck.program
      (Machine.DelimitedTripleWidthCheck.start beforeInput beforeOutput
        ((instanceCode n).encode x) field tail)
      (9 * (n + 3 + field.length + 1) + 6)).map
        (fun c => c.outputTape.current) =
      PMF.pure (some (decide (field.length = n + 3))) := by
  exact Machine.DelimitedTripleWidthCheck.eval_width_status
    beforeInput beforeOutput (n + 3) ((instanceCode n).encode x)
    field tail (instanceCode_length n x)

/-- The fixed native prefix reads the actual prime-order instance frame,
rewinds its three-field code, checks the choose tag, and validates the first
field's width on the same retained tapes. Numeric element validation and the
second field still require additional connected machine code. -/
theorem firstChooseWidthPrefix_runs (n : Nat) (x : Domain n)
    (first tail : List Bool) :
    let reply := false :: Machine.FiniteBitEncoding.delimit first ++ tail
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame reply
    ∃ finish used,
      Machine.RunsFor Machine.ChooseFirstWidthPrefix.program
        (Machine.Configuration.initial raw) finish used ∧
      finish.halted = true ∧
      finish.outputTape.current = some (decide (first.length = n + 3)) := by
  simpa using Machine.ChooseFirstWidthPrefix.runs_width_status
    n (n + 3) ((instanceCode n).encode x) first tail
    (instanceCode_length n x)

theorem firstChooseWidthPrefix_eval (n : Nat) (x : Domain n)
    (first tail : List Bool) :
    let reply := false :: Machine.FiniteBitEncoding.delimit first ++ tail
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame reply
    (Machine.evalConfigWithin Machine.ChooseFirstWidthPrefix.program
      (Machine.Configuration.initial raw)
      (Machine.ChooseFirstWidthPrefix.budget raw.length)).map
        (fun c => c.outputTape.current) =
      PMF.pure (some (decide (first.length = n + 3))) := by
  simpa using Machine.ChooseFirstWidthPrefix.eval_width_status
    n (n + 3) ((instanceCode n).encode x) first tail
    (instanceCode_length n x)

/-- The connected fixed code tests both delimited choose element widths on
the actual framed prime-order instance and response. Numeric residue and
subgroup tests are separate machine obligations. -/
theorem chooseTwoWidthsPrefix_eval (n : Nat) (x : Domain n)
    (first second state : List Bool) :
    let reply := Machine.canonicalMessageBits first second state
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame reply
    (Machine.evalConfigWithin Machine.ChooseTwoWidthsPrefix.program
      (Machine.Configuration.initial raw)
      (Machine.ChooseTwoWidthsPrefix.budget raw.length)).map
        (fun c => c.outputTape.current) =
      PMF.pure (some (decide
        (first.length = n + 3 ∧ second.length = n + 3))) := by
  simpa [Machine.canonicalMessageBits] using
    Machine.ChooseTwoWidthsPrefix.eval_width_status n (n + 3)
      ((instanceCode n).encode x) first second state
      (instanceCode_length n x)

private theorem prod_encode_decode {α β : Type}
    (E : Machine.FiniteBitEncoding α) (D : Machine.FiniteBitEncoding β)
    (hE : ∀ bits a, E.decode bits = some a → E.encode a = bits)
    (hD : ∀ bits b, D.decode bits = some b → D.encode b = bits)
    (bits : List Bool) (a : α × β)
    (h : (E.prod D).decode bits = some a) :
    (E.prod D).encode a = bits := by
  cases hSplit : Machine.FiniteBitEncoding.undelimit bits with
  | none => simp [Machine.FiniteBitEncoding.prod, hSplit] at h
  | some fields =>
      rcases fields with ⟨first, second⟩
      cases hFirst : E.decode first with
      | none => simp [Machine.FiniteBitEncoding.prod, hSplit, hFirst] at h
      | some x =>
          cases hSecond : D.decode second with
          | none => simp [Machine.FiniteBitEncoding.prod, hSplit, hFirst, hSecond] at h
          | some y =>
              have hPair : a = (x, y) := by
                simpa [Machine.FiniteBitEncoding.prod, hSplit, hFirst, hSecond]
                  using h.symm
              subst a
              change Machine.FiniteBitEncoding.delimit (E.encode x) ++ D.encode y = bits
              rw [hE first x hFirst, hD second y hSecond]
              exact Machine.FiniteBitEncoding.delimit_append_of_undelimit hSplit

private theorem bitstring_encode_decode (bits value : List Bool)
    (h : Machine.FiniteBitEncoding.bitstring.decode bits = some value) :
    Machine.FiniteBitEncoding.bitstring.encode value = bits := by
  simpa [Machine.FiniteBitEncoding.bitstring] using h.symm

/-- On a choose-stage reply whose two prime-order elements decode, the
abstract normalizer returns the original bitstring exactly. Native code may
therefore copy the accepted reply; validation is still a machine obligation. -/
theorem normalizeChooseResponse_eq_self_of_valid
    (n : Nat) (x : Domain n) (bits : List Bool)
    (m₀ m₁ : (embed n x).params.Element) (state : List Bool)
    (h : (responseCodeOfElement (elementCode n x)).decode bits =
      some (.inl (m₀, m₁, state))) :
    normalizeChooseResponse (elementCode n x) (embed n x).params.generator bits = bits := by
  let E := elementCode n x
  have hCanon : ∀ raw a, E.decode raw = some a → E.encode a = raw := by
    intro raw a ha
    exact x.down.elementCode_encode_decode raw a ha
  have hPair : ∀ raw (v : (embed n x).params.Element × List Bool),
      (E.prod Machine.FiniteBitEncoding.bitstring).decode raw = some v →
      (E.prod Machine.FiniteBitEncoding.bitstring).encode v = raw :=
    prod_encode_decode E Machine.FiniteBitEncoding.bitstring
      hCanon bitstring_encode_decode
  have hChoose : ∀ raw (v : (embed n x).params.Element ×
      (embed n x).params.Element × List Bool),
      (E.prod (E.prod Machine.FiniteBitEncoding.bitstring)).decode raw = some v →
      (E.prod (E.prod Machine.FiniteBitEncoding.bitstring)).encode v = raw :=
    prod_encode_decode E (E.prod Machine.FiniteBitEncoding.bitstring) hCanon hPair
  cases bits with
  | nil => simp [responseCodeOfElement, Machine.FiniteBitEncoding.sum] at h
  | cons tag rest =>
      cases tag with
      | true => simp [responseCodeOfElement, Machine.FiniteBitEncoding.sum] at h
      | false =>
          have hRaw : (E.prod (E.prod Machine.FiniteBitEncoding.bitstring)).decode rest =
              some (m₀, m₁, state) := by
            simpa [responseCodeOfElement, Machine.FiniteBitEncoding.sum, E] using h
          have hEncoded := hChoose rest (m₀, m₁, state) hRaw
          change false :: (E.prod (E.prod Machine.FiniteBitEncoding.bitstring)).encode
            (interpretChooseResponse E (embed n x).params.generator (false :: rest)) =
            false :: rest
          congr 1
          rw [show interpretChooseResponse E (embed n x).params.generator
              (false :: rest) = (m₀, m₁, state) by
            unfold interpretChooseResponse
            rw [h]]
          exact hEncoded

/-- A decoded choose reply has exactly the native two-delimiter layout.
This direction is useful when a bit-level parser's accepting branch is
connected to the mathematical response codec. -/
theorem validChooseResponse_layout
    (n : Nat) (x : Domain n) (bits : List Bool)
    (m₀ m₁ : (embed n x).params.Element) (state : List Bool)
    (h : (responseCodeOfElement (elementCode n x)).decode bits =
      some (.inl (m₀, m₁, state))) :
    bits = Machine.canonicalMessageBits
      ((elementCode n x).encode m₀)
      ((elementCode n x).encode m₁) state := by
  have hCopy := normalizeChooseResponse_eq_self_of_valid n x bits m₀ m₁ state h
  rw [normalizeChooseResponse_eq_canonical] at hCopy
  simp [interpretChooseResponse, h] at hCopy
  exact hCopy.symm

/-- Bit-level acceptance criterion for the choose reply. The two delimited
fields must have the prescribed width, lie in the nonzero residue range, and
pass the modular-power subgroup test. The trailing state is unrestricted.
This theorem identifies what native validation has to compute; it does not
implement the validation by machine instructions. -/
theorem validChooseResponse_iff_numeric
    (n : Nat) (x : Domain n) (bits : List Bool) :
    (∃ m₀ m₁ state,
      (responseCodeOfElement (elementCode n x)).decode bits =
        some (.inl (m₀, m₁, state))) ↔
    ∃ first second state,
      bits = Machine.canonicalMessageBits first second state ∧
      first.length = n + 3 ∧
      Machine.Binary.value first < x.down.modulus ∧
      Machine.Binary.value first ≠ 0 ∧
      Machine.Binary.value first ^ x.down.scalarOrder % x.down.modulus = 1 ∧
      second.length = n + 3 ∧
      Machine.Binary.value second < x.down.modulus ∧
      Machine.Binary.value second ≠ 0 ∧
      Machine.Binary.value second ^ x.down.scalarOrder % x.down.modulus = 1 := by
  constructor
  · rintro ⟨m₀, m₁, state, h⟩
    let first := (elementCode n x).encode m₀
    let second := (elementCode n x).encode m₁
    refine ⟨first, second, state,
      validChooseResponse_layout n x bits m₀ m₁ state h, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · exact (x.down.elementCode_valid_iff first).mp
        ⟨m₀, (elementCode n x).decode_encode m₀⟩ |>.1
    · exact ((x.down.elementCode_valid_iff first).mp
        ⟨m₀, (elementCode n x).decode_encode m₀⟩).2.1
    · exact ((x.down.elementCode_valid_iff first).mp
        ⟨m₀, (elementCode n x).decode_encode m₀⟩).2.2.1
    · exact ((x.down.elementCode_valid_iff first).mp
        ⟨m₀, (elementCode n x).decode_encode m₀⟩).2.2.2
    · exact (x.down.elementCode_valid_iff second).mp
        ⟨m₁, (elementCode n x).decode_encode m₁⟩ |>.1
    · exact ((x.down.elementCode_valid_iff second).mp
        ⟨m₁, (elementCode n x).decode_encode m₁⟩).2.1
    · exact ((x.down.elementCode_valid_iff second).mp
        ⟨m₁, (elementCode n x).decode_encode m₁⟩).2.2.1
    · exact ((x.down.elementCode_valid_iff second).mp
        ⟨m₁, (elementCode n x).decode_encode m₁⟩).2.2.2
  · rintro ⟨first, second, state, hLayout, hLen₀, hLt₀, hNe₀, hPow₀,
      hLen₁, hLt₁, hNe₁, hPow₁⟩
    obtain ⟨m₀, h₀⟩ := (x.down.elementCode_valid_iff first).mpr
      ⟨hLen₀, hLt₀, hNe₀, hPow₀⟩
    obtain ⟨m₁, h₁⟩ := (x.down.elementCode_valid_iff second).mpr
      ⟨hLen₁, hLt₁, hNe₁, hPow₁⟩
    change (elementCode n x).decode first = some m₀ at h₀
    change (elementCode n x).decode second = some m₁ at h₁
    refine ⟨m₀, m₁, state, ?_⟩
    rw [hLayout]
    simp [Machine.canonicalMessageBits, responseCodeOfElement,
      Machine.FiniteBitEncoding.sum, Machine.FiniteBitEncoding.prod,
      Machine.FiniteBitEncoding.bitstring, h₀, h₁]

private theorem nonzero_of_power_one
    (modulus exponent candidate : Nat) (hExponent : 0 < exponent)
    (h : candidate ^ exponent % modulus = 1) : candidate ≠ 0 := by
  intro hZero
  subst candidate
  simp [zero_pow (by omega : exponent ≠ 0)] at h

/-- The subgroup power test already excludes zero because the scalar order
is positive. A native validator therefore need not rerun a separate
nonzero scan after successfully checking the modular power result. -/
theorem validChooseResponse_iff_numeric_without_nonzero
    (n : Nat) (x : Domain n) (bits : List Bool) :
    (∃ m₀ m₁ state,
      (responseCodeOfElement (elementCode n x)).decode bits =
        some (.inl (m₀, m₁, state))) ↔
    ∃ first second state,
      bits = Machine.canonicalMessageBits first second state ∧
      first.length = n + 3 ∧
      Machine.Binary.value first < x.down.modulus ∧
      Machine.Binary.value first ^ x.down.scalarOrder % x.down.modulus = 1 ∧
      second.length = n + 3 ∧
      Machine.Binary.value second < x.down.modulus ∧
      Machine.Binary.value second ^ x.down.scalarOrder % x.down.modulus = 1 := by
  constructor
  · intro h
    obtain ⟨first, second, state, hLayout, hWidth₀, hRange₀, _, hPower₀,
      hWidth₁, hRange₁, _, hPower₁⟩ :=
        (validChooseResponse_iff_numeric n x bits).mp h
    exact ⟨first, second, state, hLayout, hWidth₀, hRange₀, hPower₀,
      hWidth₁, hRange₁, hPower₁⟩
  · rintro ⟨first, second, state, hLayout, hWidth₀, hRange₀, hPower₀,
      hWidth₁, hRange₁, hPower₁⟩
    apply (validChooseResponse_iff_numeric n x bits).mpr
    refine ⟨first, second, state, hLayout, hWidth₀, hRange₀, ?_, hPower₀,
      hWidth₁, hRange₁, ?_, hPower₁⟩
    · exact nonzero_of_power_one _ _ _ x.down.scalarOrder_prime.pos hPower₀
    · exact nonzero_of_power_one _ _ _ x.down.scalarOrder_prime.pos hPower₁

/-- Every mathematically accepted choose reply passes the actual two-field
machine width test at the common all-input budget. Width acceptance alone
does not establish element validity. -/
theorem validChooseResponse_nativeWidths (n : Nat) (x : Domain n)
    (bits : List Bool)
    (hValid : ∃ m₀ m₁ state,
      (responseCodeOfElement (elementCode n x)).decode bits =
        some (.inl (m₀, m₁, state))) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits
    (Machine.evalConfigWithin Machine.ChooseTwoWidthsPrefix.program
      (Machine.Configuration.initial raw)
      (Machine.ChooseTwoWidthsPrefix.budget raw.length)).map
        (fun c => c.outputTape.current) = PMF.pure (some true) := by
  obtain ⟨first, second, state, hLayout, hFirst, _, _, _, hSecond, _, _, _⟩ :=
    (validChooseResponse_iff_numeric n x bits).mp hValid
  subst bits
  simpa [hFirst, hSecond] using chooseTwoWidthsPrefix_eval n x first second state

/-- A mathematically valid choose reply passes both comparisons in the
connected finite machine code. This is a necessary condition only;
subgroup membership and malformed-response rejection remain separate. -/
theorem validChooseResponse_nativeRanges (n : Nat) (x : Domain n)
    (bits : List Bool)
    (hValid : ∃ m₀ m₁ state,
      (responseCodeOfElement (elementCode n x)).decode bits =
        some (.inl (m₀, m₁, state))) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits
    ∃ first second state target used,
      bits = Machine.canonicalMessageBits first second state ∧
      Machine.RunsFor Machine.ChooseTwoRanges.program
        (Machine.Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.current = some true ∧
      target.inputTape.right.getD
        (Machine.DelimitedTapeComparison.marked second).length none =
        some true := by
  obtain ⟨first, second, state, hLayout, hWidth₀, hRange₀, _,
    hWidth₁, hRange₁, _⟩ :=
    (validChooseResponse_iff_numeric_without_nonzero n x bits).mp hValid
  subst bits
  obtain ⟨target, used, run, hHalt, hFirstDecision, hSecondDecision⟩ :=
    chooseTwoRanges_decisions n x first second state hWidth₀ hWidth₁
  refine ⟨first, second, state, target, used, rfl, run, hHalt, ?_, ?_⟩
  · simpa [hRange₀] using hFirstDecision
  · simpa [hRange₁] using hSecondDecision

/-- The existing finite bit-level exponentiation program computes the exact
subgroup-membership test on a raw fixed-width candidate. Its input here is
the interleaved arithmetic triple; physically assembling that triple from
the choose-response frame remains a separate machine-code obligation. -/
theorem elementCode_valid_iff_nativePower_one
    (n : Nat) (x : Domain n) (bits : List Bool)
    (hWidth : bits.length = n + 3)
    (hRange : Machine.Binary.value bits < x.down.modulus)
    (hNonzero : Machine.Binary.value bits ≠ 0) :
    let raw := Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
        x.down.modulus (Machine.Binary.value bits) x.down.scalarOrder)
    (∃ a : (embed n x).params.Element,
      (elementCode n x).decode bits = some a) ↔
    Machine.evalWithin Machine.BinaryPowerExternalWidth.program raw
      (Machine.BinaryPowerExternalWidth.budget raw.length) =
        PMF.pure (some (Machine.Binary.encode (n + 3) 1)) := by
  dsimp only
  let C := x.down
  let v := Machine.Binary.value bits
  have hExponent : C.scalarOrder < 2 ^ (n + 3) :=
    (C.scalarOrder_lt_modulus.trans C.modulus_lt)
  have hPower := Machine.BinaryPowerExternalWidth.eval_numbers
    (n + 3) C.modulus v C.scalarOrder C.modulus_prime.one_lt
    hRange hExponent C.modulus_lt
  change Machine.evalWithin Machine.BinaryPowerExternalWidth.program
    (Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
        C.modulus v C.scalarOrder))
    (Machine.BinaryPowerExternalWidth.budget
      (Machine.BinaryModularAddition.interleave
        (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
          C.modulus v C.scalarOrder)).length) = _ at hPower
  rw [hPower]
  have hOne : 1 < 2 ^ (n + 3) :=
    C.modulus_prime.one_lt.trans C.modulus_lt
  have hResidue : v ^ C.scalarOrder % C.modulus < 2 ^ (n + 3) :=
    (Nat.mod_lt _ C.modulus_prime.pos).trans C.modulus_lt
  have hCode : Machine.Binary.encode (n + 3)
      (v ^ C.scalarOrder % C.modulus) = Machine.Binary.encode (n + 3) 1 ↔
      v ^ C.scalarOrder % C.modulus = 1 := by
    constructor
    · intro h
      have hv := congrArg Machine.Binary.value h
      simpa only [Machine.Binary.value_encode hResidue,
        Machine.Binary.value_encode hOne] using hv
    · intro h
      rw [h]
  have hPure : PMF.pure (some (Machine.Binary.encode (n + 3)
      (v ^ C.scalarOrder % C.modulus))) =
      PMF.pure (some (Machine.Binary.encode (n + 3) 1)) ↔
      Machine.Binary.encode (n + 3) (v ^ C.scalarOrder % C.modulus) =
        Machine.Binary.encode (n + 3) 1 := by
    constructor
    · intro h
      have hMem : some (Machine.Binary.encode (n + 3)
          (v ^ C.scalarOrder % C.modulus)) ∈
          (PMF.pure (some (Machine.Binary.encode (n + 3) 1))).support := by
        rw [← h]
        simp
      simpa using hMem
    · intro h
      rw [h]
  rw [hPure, hCode]
  exact (x.down.elementCode_valid_iff bits).trans (by
    simp [hWidth, hRange, hNonzero, C, v])

/-- The finite one-bit result checker recognizes precisely the subgroup
test value produced by native exponentiation. The two standalone machine
certificates do not yet constitute a connected normalizer program. -/
theorem elementCode_valid_iff_powerResult_accepted
    (n : Nat) (x : Domain n) (bits : List Bool)
    (hWidth : bits.length = n + 3)
    (hRange : Machine.Binary.value bits < x.down.modulus)
    (hNonzero : Machine.Binary.value bits ≠ 0) :
    (∃ a : (embed n x).params.Element,
      (elementCode n x).decode bits = some a) ↔
    Machine.BinaryIsOne.accepts
      (Machine.Binary.encode (n + 3)
        (Machine.Binary.value bits ^ x.down.scalarOrder % x.down.modulus)) = true := by
  rw [Machine.BinaryIsOne.accepts_iff_value_one]
  have hResidue : Machine.Binary.value bits ^ x.down.scalarOrder %
      x.down.modulus < 2 ^ (n + 3) :=
    (Nat.mod_lt _ x.down.modulus_prime.pos).trans x.down.modulus_lt
  rw [Machine.Binary.value_encode hResidue]
  exact (x.down.elementCode_valid_iff bits).trans (by
    simp [hWidth, hRange, hNonzero])

/-- The connected finite power-and-test program accepts exactly the
subgroup membership condition on a valid fixed-width residue. This theorem
does not yet parse the choose reply or assemble its arithmetic triple. -/
theorem elementCode_valid_iff_nativePowerIsOne
    (n : Nat) (x : Domain n) (bits : List Bool)
    (hWidth : bits.length = n + 3)
    (hRange : Machine.Binary.value bits < x.down.modulus)
    (hNonzero : Machine.Binary.value bits ≠ 0) :
    let raw := Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
        x.down.modulus (Machine.Binary.value bits) x.down.scalarOrder)
    (∃ a : (embed n x).params.Element,
      (elementCode n x).decode bits = some a) ↔
    Machine.evalWithin Machine.BinaryPowerIsOne.program raw
      (Machine.BinaryPowerIsOne.budget raw.length) =
        PMF.pure (some [true]) := by
  dsimp only
  let C := x.down
  let v := Machine.Binary.value bits
  have hExponent : C.scalarOrder < 2 ^ (n + 3) :=
    C.scalarOrder_lt_modulus.trans C.modulus_lt
  have hEval := Machine.BinaryPowerIsOne.eval_numbers (n + 3)
    C.modulus v C.scalarOrder C.modulus_prime.one_lt hRange
    hExponent C.modulus_lt
  change Machine.evalWithin Machine.BinaryPowerIsOne.program
    (Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
        C.modulus v C.scalarOrder))
    (Machine.BinaryPowerIsOne.budget
      (Machine.BinaryModularAddition.interleave
        (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
          C.modulus v C.scalarOrder)).length) =
      PMF.pure (some [Machine.BinaryIsOneInPlace.accepts
        (Machine.Binary.encode (n + 3)
          (v ^ C.scalarOrder % C.modulus))]) at hEval
  rw [hEval]
  have hCriterion := elementCode_valid_iff_powerResult_accepted
    n x bits hWidth hRange hNonzero
  change (∃ a : (embed n x).params.Element,
    (elementCode n x).decode bits = some a) ↔
    Machine.BinaryIsOneInPlace.accepts
      (Machine.Binary.encode (n + 3)
        (v ^ C.scalarOrder % C.modulus)) = true at hCriterion
  constructor
  · intro hValid
    rw [hCriterion.mp hValid]
  · intro hPure
    have hMem : some [Machine.BinaryIsOneInPlace.accepts
        (Machine.Binary.encode (n + 3)
          (v ^ C.scalarOrder % C.modulus))] ∈
        (PMF.pure (some [true])).support := by
      rw [← hPure]
      simp
    have hAccepted : Machine.BinaryIsOneInPlace.accepts
        (Machine.Binary.encode (n + 3)
          (v ^ C.scalarOrder % C.modulus)) = true := by
      simpa using hMem
    exact hCriterion.mpr hAccepted

/-- Every reply other than a successfully decoded choose-stage triple,
including a guess-stage reply, must produce the generator-pair fallback.
Together with `normalizeChooseResponse_eq_self_of_valid` this specifies the
two native branches without pretending that the parser is a machine opcode. -/
theorem normalizeChooseResponse_eq_default_of_invalid
    (n : Nat) (x : Domain n) (bits : List Bool)
    (hInvalid : ¬ ∃ m₀ m₁ state,
      (responseCodeOfElement (elementCode n x)).decode bits =
        some (.inl (m₀, m₁, state))) :
    normalizeChooseResponse (elementCode n x) (embed n x).params.generator bits =
      Machine.canonicalMessageBits
        ((elementCode n x).encode (embed n x).params.generator)
        ((elementCode n x).encode (embed n x).params.generator) [] := by
  classical
  cases hDecode : (responseCodeOfElement (elementCode n x)).decode bits with
  | none =>
      simp [normalizeChooseResponse_eq_canonical, interpretChooseResponse, hDecode]
  | some value =>
      cases value with
      | inl messages =>
          rcases messages with ⟨m₀, m₁, state⟩
          exact False.elim (hInvalid ⟨m₀, m₁, state, hDecode⟩)
      | inr bit =>
          simp [normalizeChooseResponse_eq_canonical, interpretChooseResponse, hDecode]

/-- The native copy branch implements the specified normalizer on an
accepted choose response, including its entire arbitrary state suffix.
The decoder premise is a branch correctness premise, not an implementation
of the acceptance test. -/
theorem acceptedChooseOutput_runs_normalization
    (n : Nat) (x : Domain n) (bits : List Bool)
    (m₀ m₁ : (embed n x).params.Element) (state : List Bool)
    (h : (responseCodeOfElement (elementCode n x)).decode bits =
      some (.inl (m₀, m₁, state))) :
    ∃ target used,
      Machine.RunsFor Machine.ChooseAcceptedOutput.program
        (Machine.Configuration.initial
          (Machine.encodeSecurityParameter n ++
            Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits)) target used ∧
      target.halted = true ∧
      target.outputBits = normalizeChooseResponse
        (elementCode n x) (embed n x).params.generator bits := by
  obtain ⟨target, used, run, hHalt, hBits⟩ :=
    Machine.ChooseAcceptedOutput.runs_valid n ((instanceCode n).encode x) bits
  exact ⟨target, used, run, hHalt,
    hBits.trans (normalizeChooseResponse_eq_self_of_valid n x bits m₀ m₁ state h).symm⟩

/-- The native fallback branch implements the specified normalizer once
the actual instance generator has been isolated on the working tape.
Isolating that field and selecting this branch are separate code obligations;
this theorem never installs a decoded generator as a machine instruction. -/
theorem defaultChooseOutput_runs_normalization
    (n : Nat) (x : Domain n) (bits : List Bool)
    (before tail : List (Option Bool)) (blanks : Nat)
    (hInvalid : ¬ ∃ m₀ m₁ state,
      (responseCodeOfElement (elementCode n x)).decode bits =
        some (.inl (m₀, m₁, state))) :
    ∃ target used,
      Machine.RunsFor Machine.ChooseDefaultOutput.program
        (Machine.writeDelimitedContextStart (none :: before) [] tail
          ((elementCode n x).encode (embed n x).params.generator) blanks) target used ∧
      target.halted = true ∧
      target.outputBits = normalizeChooseResponse
        (elementCode n x) (embed n x).params.generator bits := by
  obtain ⟨target, used, run, hHalt, hBits⟩ :=
    Machine.ChooseDefaultOutput.runs_generator before tail
      ((elementCode n x).encode (embed n x).params.generator) blanks
  exact ⟨target, used, run, hHalt,
    hBits.trans (normalizeChooseResponse_eq_default_of_invalid n x bits hInvalid).symm⟩

/-- The fallback branch now implements normalization directly from the
actual framed represented instance and an arbitrary rejected response.
There is no isolated-generator premise: the finite program performs the
field scan, blank writes, rewind, and duplicate output itself. Selecting
this branch after native validation remains the enclosing normalizer's task. -/
theorem framedDefaultChooseOutput_runs_normalization
    (n : Nat) (x : Domain n) (bits : List Bool)
    (hInvalid : ¬ ∃ m₀ m₁ state,
      (responseCodeOfElement (elementCode n x)).decode bits =
        some (.inl (m₀, m₁, state))) :
    ∃ target used,
      Machine.RunsFor Machine.FramedChooseDefaultOutput.program
        (Machine.Configuration.initial
          (Machine.encodeSecurityParameter n ++
            Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits)) target used ∧
      target.halted = true ∧
      target.outputBits = normalizeChooseResponse
        (elementCode n x) (embed n x).params.generator bits := by
  let C := x.down
  let p := Machine.Binary.encode (n+3) C.modulus
  let q := Machine.Binary.encode (n+3) C.scalarOrder
  let g := Machine.Binary.encode (n+3) C.generator.val.val
  obtain ⟨target, used, run, hHalt, hBits⟩ :=
    Machine.FramedChooseDefaultOutput.runs_valid n p q g bits
      (Machine.Binary.encode_length _ _) (by simp [p, q]) (by simp [p, g])
  refine ⟨target, used, ?_, hHalt, ?_⟩
  · simpa [C, p, q, g, instanceCode, PrimeOrderParameters.instanceCode,
      List.append_assoc] using run
  · rw [normalizeChooseResponse_eq_default_of_invalid n x bits hInvalid]
    simpa [C, g, elementCode, PrimeOrderParameters.elementCode,
      embed, PrimeOrderParameters.parameters] using hBits

/-- Exact evaluator agreement of the native accepted-output branch with
normalization, at its all-input polynomial budget. -/
theorem acceptedChooseOutput_eval_normalization
    (n : Nat) (x : Domain n) (bits : List Bool)
    (m₀ m₁ : (embed n x).params.Element) (state : List Bool)
    (h : (responseCodeOfElement (elementCode n x)).decode bits =
      some (.inl (m₀, m₁, state))) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits
    Machine.evalWithin Machine.ChooseAcceptedOutput.program raw
      (10000*(raw.length+1)) = PMF.pure (some
        (normalizeChooseResponse (elementCode n x) (embed n x).params.generator bits)) := by
  dsimp only
  rw [Machine.ChooseAcceptedOutput.eval_valid,
    normalizeChooseResponse_eq_self_of_valid n x bits m₀ m₁ state h]

/-- Exact evaluator agreement of the native framed fallback branch with
normalization for every rejected response. The code's time certificate also
covers malformed outer frames; the correctness instance here fixes valid
represented parameters. This remains a branch theorem, not a full `N`. -/
theorem framedDefaultChooseOutput_eval_normalization
    (n : Nat) (x : Domain n) (bits : List Bool)
    (hInvalid : ¬ ∃ m₀ m₁ state,
      (responseCodeOfElement (elementCode n x)).decode bits =
        some (.inl (m₀, m₁, state))) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits
    Machine.evalWithin Machine.FramedChooseDefaultOutput.program raw
      (10000000000000*(raw.length+1)) = PMF.pure (some
        (normalizeChooseResponse (elementCode n x) (embed n x).params.generator bits)) := by
  dsimp only
  let raw := Machine.encodeSecurityParameter n ++
    Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits
  obtain ⟨target, used, run, hHalt, hBits⟩ :=
    framedDefaultChooseOutput_runs_normalization n x bits hInvalid
  have hHalts : Machine.HaltsWith Machine.FramedChooseDefaultOutput.program raw
      (normalizeChooseResponse (elementCode n x) (embed n x).params.generator bits) used :=
    ⟨target, run, hHalt, hBits⟩
  rw [Machine.evalWithin_eq_of_haltsWithin Machine.FramedChooseDefaultOutput.program raw
    (10000000000000*(raw.length+1)) used
    (Machine.FramedChooseDefaultOutput.haltsWithin raw)
    (hHalts.haltsWithin_of_no_randomBit Machine.FramedChooseDefaultOutput.no_randomBit)]
  exact hHalts.evalWithin_eq_pure_of_no_randomBit Machine.FramedChooseDefaultOutput.no_randomBit

/-- A native range-check invocation returns only the conjunction bit.
The copied instance and temporary status cells are erased by actual code,
so this result can be used by a guarded caller that retains the request. -/
theorem chooseRangeDecision_eval (n : Nat) (x : Domain n)
    (first second state : List Bool)
    (hFirst : first.length = n+3) (hSecond : second.length = n+3) :
    let reply := Machine.canonicalMessageBits first second state
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame reply
    Machine.evalWithin Machine.ChooseRangeDecision.program raw
      (Machine.ChooseRangeDecision.budget raw.length) = PMF.pure (some
        [decide (Machine.Binary.value first < x.down.modulus ∧
          Machine.Binary.value second < x.down.modulus)]) := by
  let modulusCode := Machine.Binary.encode (n+3) x.down.modulus
  let suffix := Machine.Binary.encode (n+3) x.down.scalarOrder ++
    Machine.Binary.encode (n+3) x.down.generator.val.val
  have hCode : ((instanceCode n).encode x) = modulusCode ++ suffix := by
    simp [instanceCode, PrimeOrderParameters.instanceCode, modulusCode, suffix, List.append_assoc]
  have hInstance : (modulusCode ++ suffix).length = 3*(n+3) := by
    rw [← hCode, instanceCode_length]
  have h := Machine.ChooseRangeDecision.eval_decisions n (n+3) modulusCode suffix first second state
    (by omega) (by simp [modulusCode]) hInstance hFirst hSecond
  simpa [Machine.canonicalMessageBits, hCode, modulusCode,
    Machine.Binary.value_encode x.down.modulus_lt] using h

/-- Complete matching fields return a one-bit width decision on the actual
represented request, with the copied instance removed from the result. -/
theorem chooseWidthDecision_eval (n : Nat) (x : Domain n)
    (first second state : List Bool)
    (hFirst : first.length = n + 3) (hSecond : second.length = n + 3) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++
      Machine.frame (Machine.canonicalMessageBits first second state)
    Machine.evalWithin Machine.ChooseWidthDecision.program raw
      (Machine.ChooseWidthDecision.budget raw.length) = PMF.pure (some [true]) := by
  simpa [Machine.canonicalMessageBits] using
    Machine.ChooseWidthDecision.eval_matching n (n + 3) ((instanceCode n).encode x)
      first second state (instanceCode_length n x) hFirst hSecond

/-- Decoder acceptance implies success of the actual one-bit width code.
The converse for arbitrary malformed bitstrings is a separate obligation. -/
theorem validChooseResponse_widthDecision (n : Nat) (x : Domain n)
    (bits : List Bool)
    (hValid : ∃ m₀ m₁ state,
      (responseCodeOfElement (elementCode n x)).decode bits =
        some (.inl (m₀, m₁, state))) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits
    Machine.evalWithin Machine.ChooseWidthDecision.program raw
      (Machine.ChooseWidthDecision.budget raw.length) = PMF.pure (some [true]) := by
  obtain ⟨first, second, state, hLayout, hFirst, _, _, _, hSecond, _, _, _⟩ :=
    (validChooseResponse_iff_numeric n x bits).mp hValid
  subst bits
  exact chooseWidthDecision_eval n x first second state hFirst hSecond

/-- Any empty or wrong-stage reply returns just the rejecting bit. Element
fields and response state are not assumed well formed. -/
theorem chooseWidthDecision_eval_wrong_tag (n : Nat) (x : Domain n)
    (bits : List Bool)
    (hTag : (Machine.Tape.ofBits bits).current = none ∨
      (Machine.Tape.ofBits bits).current = some true) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits
    Machine.evalWithin Machine.ChooseWidthDecision.program raw
      (Machine.ChooseWidthDecision.budget raw.length) = PMF.pure (some [false]) :=
  Machine.ChooseWidthDecision.eval_wrong_tag n ((instanceCode n).encode x) bits hTag

/-- The native width decision covers every raw choose payload, not only
canonical fields. Missing delimiters and wrong widths return false after
physically erasing the copied instance counter. -/
theorem chooseWidthDecision_eval_raw (n : Nat) (x : Domain n) (payload : List Bool) :
    let bits := false :: payload
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits
    let decision := (Machine.FiniteBitEncoding.undelimit payload).any (fun pair =>
      decide (pair.1.length = n + 3) &&
        (Machine.FiniteBitEncoding.undelimit pair.2).any (fun next => decide (next.1.length = n + 3)))
    Machine.evalWithin Machine.ChooseWidthDecision.program raw
      (Machine.ChooseWidthDecision.budget raw.length) = PMF.pure (some [decision]) :=
  Machine.ChooseWidthDecision.eval_raw_decision n (n + 3) ((instanceCode n).encode x)
    payload (instanceCode_length n x)

/-- Acceptance by the actual framed native width checker guarantees the
exact two complete fields required by later range and subgroup scans.
The original reply may initially be any finite bitstring. -/
theorem nativeWidthAcceptance_fields (n : Nat) (x : Domain n) (bits : List Bool)
    {target : Machine.Configuration} {used : Nat}
    (run : Machine.RunsFor Machine.ChooseTwoWidthsPrefix.program
      (Machine.Configuration.initial (Machine.encodeSecurityParameter n ++
        Machine.frame ((instanceCode n).encode x) ++ Machine.frame bits)) target used)
    (hHalt : target.halted = true) (hAccept : target.outputTape.current = some true) :
    ∃ first second state,
      Machine.canonicalMessageBits first second state = bits ∧
      first.length = n + 3 ∧ second.length = n + 3 := by
  simpa [Machine.canonicalMessageBits] using
    Machine.ChooseTwoWidthsPrefix.fields_of_accepted_run n (n + 3) ((instanceCode n).encode x)
      bits (instanceCode_length n x) run hHalt hAccept

end ElGamal.PrimeOrderRepresentation
