import Foundation.Crypto.Semantics.Machine.DelimitedTapeComparison
import Foundation.Crypto.Semantics.Machine.FramedInput

namespace Machine.ChooseSavedRequest

/-- The retained prefix at the first candidate is exactly the reversal of
all bytes already consumed from the original framed request. This is a
layout identity, not an instruction that reconstructs the tape. -/
theorem first_candidate_saved (n : Nat)
    (modulus exponent generator candidate tail : List Bool) :
    let instanceBits := modulus ++ exponent ++ generator
    let reply := false :: FiniteBitEncoding.delimit candidate ++ tail
    let before := some false :: some false :: List.replicate reply.length (some true) ++
      generator.reverse.map some ++ exponent.reverse.map some ++ modulus.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++ some false :: List.replicate n (some true)
    none :: (false :: tail).reverse.map some ++
        (DelimitedTapeComparison.marked candidate).reverse.map some ++ before =
      none :: (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).reverse.map some := by
  simp [frame, encodeSecurityParameter, DelimitedTapeComparison.delimit_eq_marked,
    List.reverse_append, List.map_append, List.reverse_cons, List.append_assoc]

/-- After skipping the first field and testing the second, the same entire
request (including both original candidates and all trailing state) is saved. -/
theorem second_candidate_saved (n : Nat)
    (modulus exponent generator first candidate tail : List Bool) :
    let instanceBits := modulus ++ exponent ++ generator
    let reply := false :: FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit candidate ++ tail
    let before := (FiniteBitEncoding.delimit first).reverse.map some ++
      some false :: some false :: List.replicate reply.length (some true) ++
      generator.reverse.map some ++ exponent.reverse.map some ++ modulus.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++ some false :: List.replicate n (some true)
    none :: (false :: tail).reverse.map some ++
        (DelimitedTapeComparison.marked candidate).reverse.map some ++ before =
      none :: (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).reverse.map some := by
  simp [frame, encodeSecurityParameter, DelimitedTapeComparison.delimit_eq_marked,
    List.reverse_append, List.map_append, List.reverse_cons, List.append_assoc]

end Machine.ChooseSavedRequest
