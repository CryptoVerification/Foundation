import Foundation.Crypto.Semantics.Procedure

/-! Select a proved execution contract from an earlier runtime result.
Selection adds no machine transition: the selected contract's actual entry
must be the preceding physical exit when used with `Procedure.seq`. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w
variable {State : Type u} {Input : Type v} {Output : Type w} {step : State → PMF State}

noncomputable def dispatch (family : Input → Procedure step Unit Output) : Procedure step Input Output where
  entry := fun input => (family input).entry ()
  exit := fun input output => (family input).exit () output
  semantics := fun input => (family input).semantics ()
  costed := fun input => (family input).costed ()
  budget := fun input => (family input).budget ()
  bounded := fun input => (family input).bounded ()
  correct := fun input => (family input).correct ()
  law := fun input => (family input).law ()

end Foundation.Probability.TimedExecution.Procedure
