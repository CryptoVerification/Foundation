import Foundation.Crypto.Semantics.Oracle.OneUseXorInvocation

/-! Compatibility names for the library's actual arbitrary-width call,
response delivery, continuation and source halt contracts. -/
namespace Foundation.OneUseInvocationExamples
export CryptoOracle.Interactive.OneUseXorInvocation
  (invocation budget distribution adaptive_resume final stop complete complete_budget run)
end Foundation.OneUseInvocationExamples
