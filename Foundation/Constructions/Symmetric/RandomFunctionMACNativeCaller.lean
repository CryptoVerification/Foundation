import Foundation.Constructions.Symmetric.RandomFunctionMACProofEdits
import Foundation.Examples.ScheduleCertificate
import Foundation.Crypto.Semantics.Machine.BinaryEncoding
import Foundation.Crypto.Semantics.Oracle.QueryTransfer
import Foundation.Crypto.Semantics.Oracle.StateMap

/-! Native caller for the SAME adaptive 8-message/256-tag MAC example.
The finite code selects the first request, selects the second from the first
tag's low bit, repeats the first, saves the actual candidate tag and compares
it with a fourth (verification) response. No host callback computes a request,
copies a byte or performs the final comparison. The packet oracle below is a
semantic adapter: its internal execution is not included in caller time.
The verification of individual native stages is separate from this syntax.
-/
namespace Foundation.Symmetric.RandomFunctionMACNativeCaller
open Foundation.Probability CryptoOracle CryptoOracle.Interactive
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

abbrev Message := Fin 8
abbrev Tag := Fin 256

def encodeMessage (message : Message) : List Bool := Machine.Binary.encode 3 message.val
def decodeMessage (packet : List Bool) : Message := ⟨Machine.Binary.value packet % 8, by omega⟩
def encodeTag (tag : Tag) : List Bool := Machine.Binary.encode 8 tag.val
def decodeTag (packet : List Bool) : Tag := ⟨Machine.Binary.value packet % 256, by omega⟩

@[simp] theorem message_roundtrip (message : Message) : decodeMessage (encodeMessage message) = message := by
  apply Fin.ext
  change Machine.Binary.value (Machine.Binary.encode 3 message.val) % 8 = message.val
  rw [Machine.Binary.value_encode (width := 3) (n := message.val) (by exact message.isLt)]
  exact Nat.mod_eq_of_lt message.isLt

@[simp] theorem tag_roundtrip (tag : Tag) : decodeTag (encodeTag tag) = tag := by
  apply Fin.ext
  change Machine.Binary.value (Machine.Binary.encode 8 tag.val) % 256 = tag.val
  rw [Machine.Binary.value_encode (width := 8) (n := tag.val) (by exact tag.isLt)]
  exact Nat.mod_eq_of_lt tag.isLt

@[simp] theorem message_width (message : Message) : (encodeMessage message).length = 3 :=
  Machine.Binary.encode_length _ _

@[simp] theorem tag_width (tag : Tag) : (encodeTag tag).length = 8 :=
  Machine.Binary.encode_length _ _

noncomputable def packetOracle {State : Type} (world : Oracle Message Tag State) : BitOracle State :=
  fun state request => (world state (decodeMessage request)).map (fun answer => (answer.1, encodeTag answer.2))

theorem packet_response_width {State : Type} (world : Oracle Message Tag State)
    (state : State) (request : List Bool) (answer : State × List Bool)
    (reachable : answer ∈ (packetOracle world state request).support) : answer.2.length = 8 := by
  rw [packetOracle, PMF.mem_support_map_iff] at reachable
  obtain ⟨typed, _, rfl⟩ := reachable
  exact tag_width _

theorem adapt_packet {State : Type} (world : Oracle Message Tag State) :
    Program.adaptOracle encodeMessage decodeTag (packetOracle world) = world := by
  funext state message
  simp only [Program.adaptOracle, packetOracle, message_roundtrip, PMF.map_comp,
    Function.comp_def, tag_roundtrip]
  change (world state message).map id = _
  exact PMF.map_id _

/-- Interface refinement retains the entire typed trace and the opaque
oracle state. It does not assign CPU costs to the mathematical codec. -/
theorem packet_run {State Result : Type} (p : CryptoOracle.Program Message Tag Result)
    (world : Oracle Message Tag State) (state : State) :
    ((p.mapQueries encodeMessage decodeTag).run (packetOracle world) state).map
        (Program.mapTranscript id decodeTag) =
      (p.run world state).map (Program.mapTranscript encodeMessage id) := by
  simpa only [adapt_packet] using Program.mapQueries_run encodeMessage decodeTag p (packetOracle world) state

theorem packet_result {State Result : Type} (p : CryptoOracle.Program Message Tag Result)
    (world : Oracle Message Tag State) (state : State) :
    ((p.mapQueries encodeMessage decodeTag).run (packetOracle world) state).map Outcome.result =
      (p.run world state).map Outcome.result := by
  have projected := congrArg (PMF.map Outcome.result) (packet_run p world state)
  simpa only [PMF.map_comp, Program.mapTranscript, Function.comp_def] using projected

def firstMessage (coin : Bool) : Message := if coin then 0 else 1
def secondMessage (tag : Tag) : Message := if tag.val % 2 = 0 then 2 else 3

theorem final_fresh (coin : Bool) (tag : Tag) :
    (7 : Message) ∉ [firstMessage coin, secondMessage tag, firstMessage coin] := by
  cases coin <;> by_cases parity : tag.val % 2 = 0 <;>
    simp [firstMessage, secondMessage, parity]

/-- The verification bit after statically proving that message seven is
unsigned. All four oracle queries, including the repeated one, remain. -/
def target : CryptoOracle.Program Message Tag Bool :=
  .coin fun coin => .query (firstMessage coin) fun first =>
    .query (secondMessage first) fun second =>
      .query (firstMessage coin) fun repeated =>
        .query 7 fun actual => .done (decide (actual = if coin then repeated else second))

theorem target_eq_checked : target = RandomFunctionMACSchedules.checkedAttack []
    RandomFunctionMACSchedules.Examples.attack := by
  simp only [target, RandomFunctionMACSchedules.Examples.attack, RandomFunctionMACSchedules.checkedAttack,
    List.nil_append, List.cons_append]
  congr 1
  funext coin
  change CryptoOracle.Program.query (firstMessage coin) _ = CryptoOracle.Program.query (firstMessage coin) _
  congr 1
  funext first
  change CryptoOracle.Program.query (secondMessage first) _ = CryptoOracle.Program.query (secondMessage first) _
  congr 1
  funext second
  congr 1
  funext repeated
  congr 1
  funext actual
  have fresh : (7 : Message) ∉
      [if coin then 0 else 1, if first.val % 2 = 0 then 2 else 3, if coin then 0 else 1] :=
    final_fresh coin first
  simp [fresh]

def packetTarget : CryptoOracle.Program (List Bool) (List Bool) Bool :=
  target.mapQueries encodeMessage decodeTag

theorem packet_queries : packetTarget.BoundedQueries 4 := by
  apply Program.mapQueries_queries
  rw [target_eq_checked]
  exact RandomFunctionMACSchedules.Examples.reduction_queries

/-- This bound is for the packet-level reference program. The native code
must be proved to implement it before this is a native security theorem. -/
theorem packet_ideal_bound :
    eventProb ((uniform (Message → Tag)).bind (fun key =>
      (packetTarget.run (packetOracle (RandomOracle.eager key)) []).map Outcome.result)) (· = true) ≤
      (256 : ℝ≥0∞)⁻¹ := by
  simp_rw [packetTarget, packet_result, target_eq_checked]
  have bound := RandomFunctionMACProofEdits.ideal_bound RandomFunctionMACSchedules.Examples.attack
  simpa only [RandomFunctionMACSchedules.idealExperiment,
    RandomFunctionMACProofEdits.distinguisher_eq, Fintype.card_fin, Nat.cast_ofNat] using bound

namespace Native
open Machine

/-- Write a three-bit request, clear its delimiter and rewind. The first bit
is selected from a physical tape cell; no host Boolean is a native operand. -/
def dynamicPacket (base reject : Nat) (source : TapeId) (zero one middle : Bool) : Code :=
  [.native (.branch source reject (base + 1) (base + 3)),
   .native (.write .output zero), .native (.jump (base + 5)),
   .native (.write .output one), .native (.jump (base + 5)),
   .native (.moveRight .output), .native (.write .output middle),
   .native (.moveRight .output), .native (.write .output false),
   .native (.moveRight .output), .native (.erase .output),
   .native (.moveLeft .output), .native (.moveLeft .output), .native (.moveLeft .output), .call]

/-- Both data branches take five transitions, then continue to the next bit.
The source is the actual response tape and the destination is caller memory. -/
def copyBit (base reject : Nat) : Code :=
  [.native (.branch .output reject (base + 1) (base + 3)),
   .native (.write .input false), .native (.jump (base + 5)),
   .native (.write .input true), .native (.jump (base + 5)),
   .native (.moveRight .input), .native (.moveRight .output)]

def copyBits : Nat → Nat → Nat → Code
  | 0, _, _ => []
  | count + 1, base, reject => copyBit base reject ++ copyBits count (base + 7) reject

/-- Keep the coin in memory cell zero, save eight tag bits at cells one
through eight, then physically rewind both heads. -/
def saveTag (base reject : Nat) : Code :=
  [.native (.moveRight .input)] ++ copyBits 8 (base + 1) reject ++
    List.replicate 9 (.native (.moveLeft .input)) ++
    List.replicate 8 (.native (.moveLeft .output))

def lastPacket : Code :=
  [.native (.write .output true), .native (.moveRight .output),
   .native (.write .output true), .native (.moveRight .output),
   .native (.write .output true), .native (.moveRight .output),
   .native (.erase .output), .native (.moveLeft .output),
   .native (.moveLeft .output), .native (.moveLeft .output), .call]

def compareBit (base reject : Nat) : Code :=
  [.native (.branch .input reject (base + 1) (base + 2)),
   .native (.branch .output reject (base + 3) reject),
   .native (.branch .output reject reject (base + 3)),
   .native (.moveRight .input), .native (.moveRight .output)]

def compareBits : Nat → Nat → Nat → Code
  | 0, _, _ => []
  | count + 1, base, reject => compareBit base reject ++ compareBits count (base + 5) reject

/-- One fixed caller throughout four calls. Forward addresses are explicit;
the input tape keeps the coin and saved tag while each response is loaded. -/
def code : Code :=
  [.native (.randomBit .input)] ++
  dynamicPacket 1 249 .input true false false ++
  dynamicPacket 16 249 .output false true true ++
  saveTag 31 249 ++
  dynamicPacket 105 249 .input true false false ++
  [.native (.branch .input 249 195 121)] ++
  saveTag 121 249 ++ lastPacket ++
  [.native (.moveRight .input)] ++ compareBits 8 207 249 ++
  [.native (.write .output true), .native .halt,
   .native (.write .output false), .native .halt]

theorem code_length : code.length = 251 := by decide_cbv

def callAddresses : List Nat :=
  ((code.zipIdx).filter (fun entry => entry.1 == .call)).map Prod.snd

theorem call_addresses : callAddresses = [15, 30, 119, 205] := by decide_cbv

/-- Every nonhalting native control transfer is forward. This static fact
does not alone prove the transfer controller's packet lengths or termination. -/
def forwardAt (pc : Nat) : Interactive.Instruction → Bool
  | .native (.jump target) => decide (pc < target)
  | .native (.branch _ blankPc zeroPc onePc) => decide (pc < blankPc ∧ pc < zeroPc ∧ pc < onePc)
  | _ => true

theorem forward_code : (code.zipIdx.all (fun entry => forwardAt entry.2 entry.1)) = true := by decide_cbv

end Native
end Foundation.Symmetric.RandomFunctionMACNativeCaller
