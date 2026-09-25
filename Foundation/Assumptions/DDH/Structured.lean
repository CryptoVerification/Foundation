import Foundation.Assumptions.DDH.DDH

/-- A DDH problem instance with an identifying tag. The tag carries no
algebraic or security claim; `params` contains the underlying DDH syntax. -/
structure DDHParameterInstance where
  params : DDHParameters
  parameterId : Nat

/-- Specialize DDH to tagged parameter instances by reindexing along `params`. -/
def StructuredDDH (M : Type → Type) (S : DDHSemantics M) : CryptoGoal :=
  (DDH M S).reindex (fun _ => DDHParameterInstance) (fun _ I => I.params)
