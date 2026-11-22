import tmp.sheaf.xif.paper.Mzk1P5QNormalizationInputActual
import tmp.sheaf.xif.paper.Mzk1P5PhaseRelationActual
import tmp.sheaf.xif.paper.Mzk1P5CJConditionActual
import tmp.sheaf.xif.paper.Mzk1P5PhaseDerivedActual
import tmp.sheaf.xif.paper.Mzk1P5CJDerivedActual
import tmp.sheaf.xif.paper.Mzk1P5RootChoiceOrderActual
import tmp.sheaf.xif.paper.Mzk1P5HunitDerivedActual
import tmp.sheaf.xif.paper.Mzk1P5ComparisonDerivedActual
import tmp.sheaf.xif.paper.Mzk1P5PhaseExponentDataActual
import tmp.sheaf.xif.paper.Mzk1P5FinalSummaryActual

/-!
# P5 axiom audit only

This file adds no theorem.  It imports the green P5 chain and prints the
axioms of the main theorems for the audit log.
-/

namespace LeanFormal.IUT.XiFPaper

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1P5QNormalizationInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PhaseRelationActual
open LeanFormal.IUT.XiFPaper.Mzk1P5CJConditionActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PhaseDerivedActual
open LeanFormal.IUT.XiFPaper.Mzk1P5CJDerivedActual
open LeanFormal.IUT.XiFPaper.Mzk1P5RootChoiceOrderActual
open LeanFormal.IUT.XiFPaper.Mzk1P5HunitDerivedActual
open LeanFormal.IUT.XiFPaper.Mzk1P5ComparisonDerivedActual
open LeanFormal.IUT.XiFPaper.Mzk1P5FinalSummaryActual

#print axioms p5_bridge_compare
#print axioms p5_bridge_compare_of_qNormalizationInput
#print axioms p5_phase_relation
#print axioms p5_phase_pow
#print axioms p5_c_eq_one_iff
#print axioms root_image_zpow
#print axioms phase_relation
#print axioms c_eq_one_iff
#print axioms root_pow_l_square
#print axioms root_pow_one_order
#print axioms actualP5Bridge_hunit
#print axioms paperRootThetaUnit_eq_qRoot_zpow
#print axioms toRoot_zpow
#print axioms comparison_cOfPhase
#print axioms p5_final_comparison

end LeanFormal.IUT.XiFPaper
