import Foundation.Constructions.Symmetric.RandomFunctionMACNativeCaller
import Foundation.Constructions.Hash.NativeTypedCompression
import Foundation.Constructions.Hash.PolygraphOracle

/-! Typed interface of the SAME 8-message/256-tag MAC with the existing
native compression-cache backend. A three-bit message occupies the low bits
of the eight-bit chaining field; marker and empty payload are fixed. The
runtime packet is produced by NativeCompactRequest, not by this proof codec.
-/
namespace Foundation.Symmetric.RandomFunctionMACNativeCaller.Backend
open Foundation.Probability CryptoOracle CryptoOracle.Interactive
open Foundation.Hash.Native Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

def padded (message : Message) : List Bool := encodeMessage message ++ List.replicate 5 false

theorem padded_length (message : Message) : (padded message).length = 8 := by simp [padded]

def bits (message : Message) : Bits 8 := fun index =>
  (padded message)[index.val]'(by rw [padded_length]; exact index.isLt)

theorem bits_list (message : Message) : (bits message).toList = padded message := by
  apply List.ext_getElem
  · simp [padded_length]
  · intro index left right
    simp only [Bits.toList, List.getElem_ofFn, bits]

def key (message : Message) : PolygraphOracle.Key 8 0 := (bits message, false, Fin.elim0)

def request (message : Message) : List Bool := compressionPacket (key message) ++ [false]

theorem request_eq (message : Message) : request message = encodeMessage message ++ List.replicate 7 false := by
  simp only [request, compressionPacket, key, bits_list]
  change ((padded message ++ [false]) ++ [false]) = _
  simp only [padded, List.append_assoc]
  rfl

theorem request_width (message : Message) : (request message).length = 10 := by
  simp [request_eq]

theorem decode_request (message : Message) : decodeMessage (request message) = message := by
  have zeros : Machine.Binary.value (List.replicate 7 false) = 0 := by decide
  simp only [request_eq, decodeMessage, Machine.Binary.value_append, zeros, Nat.mul_zero, Nat.add_zero]
  exact message_roundtrip message

theorem key_injective : Function.Injective key := by
  intro left right same
  have packets := congrArg (fun query => decodeMessage (compressionPacket query ++ [false])) same
  change decodeMessage (request left) = decodeMessage (request right) at packets
  simpa only [decode_request] using packets

def tagBits (tag : Tag) : Bits 8 := fun index =>
  (encodeTag tag)[index.val]'(by rw [tag_width]; exact index.isLt)

theorem tagBits_list (tag : Tag) : (tagBits tag).toList = encodeTag tag := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp only [Bits.toList, List.getElem_ofFn, tagBits]

theorem decode_tagBits (tag : Tag) : decodeTag (tagBits tag).toList = tag := by
  rw [tagBits_list, tag_roundtrip]

theorem tagBits_decode (value : Bits 8) : tagBits (decodeTag value.toList) = value := by
  apply List.ofFn_injective
  change (tagBits (decodeTag value.toList)).toList = value.toList
  rw [tagBits_list]
  have bound : Machine.Binary.value value.toList < 256 := by
    simpa using Machine.Binary.value_lt value.toList
  simp only [encodeTag, decodeTag, Nat.mod_eq_of_lt bound]
  simpa only [Bits.length_toList] using Machine.Binary.encode_value value.toList

def tagEquiv : Tag ≃ Bits 8 where
  toFun := tagBits
  invFun := fun value => decodeTag value.toList
  left_inv := decode_tagBits
  right_inv := tagBits_decode

theorem uniform_decoded :
    (uniform (Bits 8)).map (fun value => decodeTag value.toList) = uniform Tag :=
  uniform_map_equiv tagEquiv.symm

end Foundation.Symmetric.RandomFunctionMACNativeCaller.Backend
