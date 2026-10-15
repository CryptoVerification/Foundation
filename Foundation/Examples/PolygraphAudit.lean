import Foundation.Examples.PolygraphLogic
import Foundation.Examples.PRGPolygraph
import Foundation.Examples.PRGPolygraphCompatibility

/-! Kernel axiom-dependency audit of reconstruction, interpretation, leaf
accounting, quantitative security, and the actual execution certificates. -/
#print axioms Foundation.Logic.Polygraph.Diagram.toForest_ofForest
#print axioms Foundation.Logic.Polygraph.Diagram.eval_toForest
#print axioms Foundation.Logic.Derivation.occurrences_substitute
#print axioms CryptoLogic.Polygraph.Derivation.plan_substitute
#print axioms CryptoLogic.Polygraph.Derivation.code_eval
#print axioms CryptoLogic.Polygraph.Derivation.advantage_eval
#print axioms CryptoLogic.Polygraph.Derivation.sound
#print axioms CryptoLogic.Polygraph.Derivation.bounded
#print axioms CryptoLogic.Polygraph.Derivation.runWitnesses_emitted
#print axioms Foundation.Symmetric.Generator.Polygraph.maskedGap_eq
#print axioms Foundation.Symmetric.Generator.Polygraph.idealPad_eq
#print axioms Foundation.Symmetric.Generator.Polygraph.bounded
#print axioms Foundation.Symmetric.Generator.Polygraph.secure
#print axioms Foundation.Symmetric.Generator.Polygraph.run
#print axioms Foundation.Symmetric.Generator.Polygraph.targetWitnesses_eq
