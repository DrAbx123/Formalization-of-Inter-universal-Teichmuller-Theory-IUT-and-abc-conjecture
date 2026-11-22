/- U-L actual root in the algebraic closure: alpha^(2l)=q. -/
import tmp.sheaf.xif.paper.LGPThetaActionActual
import tmp.sheaf.xif.paper.TwoLthRootKummerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.LGPThetaActionActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
namespace LeanFormal.IUT.XiFPaper.Mzk1ULActualRootActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Actual algebraic-closure root: the 2l-th power is the actual q unit. -/
theorem uL_actual_root_pow :
    (hodgeTwoLthRoot T b) ^ (2 * l.value) = qVAlgClosedUnit T b :=
  hodgeTwoLthRoot_pow T b
/-- Actual algebraic-closure root system for the same q unit. -/
theorem uL_actual_rootSystem_nonempty :
    Nonempty (NatRootSystem (qVAlgClosedUnit T b)) :=
  ⟨hodgeTwoLRootSystem T b⟩
/-- Actual indexed theta action data at the algebraic-closure root. -/
noncomputable def uL_actualThetaAction : LGPThetaActionData T b :=
  lgpThetaActionData T b
#print axioms uL_actual_root_pow
#print axioms uL_actual_rootSystem_nonempty
#print axioms uL_actualThetaAction
end LeanFormal.IUT.XiFPaper.Mzk1ULActualRootActual
end
