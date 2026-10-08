import Foundation.Crypto.Semantics.Machine.PrivateBitGeneration
import Foundation.Crypto.Semantics.Oracle.ReusableInitializationContinuation

/-! A fixed finite native sampler initializes the reusable caller at any
key width. Two real head moves align the generated tape for retained copying.
The original caller configuration is retained throughout initialization. -/
namespace CryptoOracle.Interactive.ReusableBitInitialization
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u v
set_option backward.isDefEq.respectTransparency false
variable {Component : Type v} {State : Type u}
    (componentStep : Component → PMF Component)
    (begin : Machine.Tape → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Machine.Tape))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Configuration State)

noncomputable def initialization (width : Nat) :=
  ReusableResponseInitialization.initialization componentStep begin ready native code oracle caller (Machine.PrivateBitGeneration.native width)
    Bits.toList (Machine.PrivateBitGeneration.halted width) (Machine.PrivateBitGeneration.tape width)
    (Machine.PrivateBitGeneration.read width) (Machine.PrivateBitGeneration.read_exit width)
    (fun _ => width) (fun _ key _ => by simp)
    (Machine.PrivateBitGeneration.decode width) (Machine.PrivateBitGeneration.decode_store width)

theorem budget (width : Nat) :
    (initialization componentStep begin ready native code oracle caller width).budget () = 6 * width + 6 := by
  unfold initialization
  rw [ReusableResponseInitialization.budget]
  change (5 * width + 2) + width + 4 = _
  omega

theorem distribution (width : Nat) :
    ((initialization componentStep begin ready native code oracle caller width).costed ()).map
      (fun result => (initialization componentStep begin ready native code oracle caller width).exit () result.1) =
      (uniform (Bits width)).map (fun key => ReusableResponseInitialization.Control.active
        (ReusableResponseSource.Control.source
          (Machine.ResponseExport.fromCells (key.toList.map some ++ [none])).moveLeft.moveRight caller)) := by
  unfold initialization
  rw [ReusableResponseInitialization.distribution]
  rfl

theorem key_distribution (width : Nat) :
    ((initialization componentStep begin ready native code oracle caller width).semantics ()).map Prod.fst =
      uniform (Bits width) := by
  unfold initialization
  rw [ReusableResponseInitialization.semantics, PMF.map_comp]
  change (uniform (Bits width)).map id = _
  rw [PMF.map_id]
end CryptoOracle.Interactive.ReusableBitInitialization
