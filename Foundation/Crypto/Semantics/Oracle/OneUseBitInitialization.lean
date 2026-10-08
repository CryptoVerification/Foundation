import Foundation.Crypto.Semantics.Machine.PrivateBitGeneration
import Foundation.Crypto.Semantics.Oracle.OneUseInitialization

/-! Uniform private bit generation starts the actual one-use source at any width.
The initial attacker configuration is retained throughout initialization. -/
namespace CryptoOracle.Interactive.OneUseBitInitialization
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Configuration State)

noncomputable def initialization (width : Nat) :=
  OneUseInitialization.initialization native code oracle caller (Machine.PrivateBitGeneration.native width)
    Bits.toList (Machine.PrivateBitGeneration.halted width) (Machine.PrivateBitGeneration.tape width)
    (Machine.PrivateBitGeneration.read width) (Machine.PrivateBitGeneration.read_exit width)
    (fun _ => width) (fun _ key _ => by simp)
    (Machine.PrivateBitGeneration.decode width) (Machine.PrivateBitGeneration.decode_store width)

theorem budget (width : Nat) :
    (initialization native code oracle caller width).budget () = 6 * width + 5 := by
  unfold initialization
  rw [OneUseInitialization.budget]
  change (5 * width + 2) + width + 3 = _
  omega

theorem distribution (width : Nat) :
    ((initialization native code oracle caller width).costed ()).map
      (fun result => (initialization native code oracle caller width).exit () result.1) =
      (uniform (Bits width)).map (fun key => OneUseInitialization.Control.active
        (OneUseSource.Control.source false
          (Machine.ResponseExport.fromCells (key.toList.map some ++ [none])) caller)) := by
  unfold initialization
  rw [OneUseInitialization.distribution]
  rfl

theorem key_distribution (width : Nat) :
    ((initialization native code oracle caller width).semantics ()).map Prod.fst =
      uniform (Bits width) := by
  unfold initialization
  rw [OneUseInitialization.semantics, PMF.map_comp]
  change (uniform (Bits width)).map id = _
  rw [PMF.map_id]
end CryptoOracle.Interactive.OneUseBitInitialization
