/- Projections of the accepted P6 display source constants (route-valid under
the 2026-11-16 correction: S2959/CTheta is legacy auxiliary, not a route input). -/
import tmp.sheaf.xif.paper.Mzk1P6DisplaySourceConstantsActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6DisplayTermsConstantsFieldsActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplaySourceConstantsActual
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
open LeanFormal.IUT.XiFPaper.S3136IVThm110ConstantsActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

theorem p6Fields_l : (p6DisplaySourceDataConstants T b).l = p6LSeven := rfl
theorem p6Fields_dmod : (p6DisplaySourceDataConstants T b).dmod = lgpDStarMod 1 := rfl
theorem p6Fields_dFpd : (p6DisplaySourceDataConstants T b).dFpd = S2990DFpd := rfl
theorem p6Fields_fFpd : (p6DisplaySourceDataConstants T b).fFpd = S2990FFpd 1 1 1 := rfl
theorem p6Fields_eStar : (p6DisplaySourceDataConstants T b).eStar = (lgpEStarMod 1 : Real) := rfl
theorem p6Fields_logQ : (p6DisplaySourceDataConstants T b).logQ =
    -Real.log (qVFamNormalizedNorm T b) := rfl
theorem p6Fields_dmod_ge_one : 1 ≤ (p6DisplaySourceDataConstants T b).dmod :=
  (p6DisplaySourceDataConstants T b).dmod_ge_one
#print axioms p6Fields_l
#print axioms p6Fields_logQ
end LeanFormal.IUT.XiFPaper.Mzk1P6DisplayTermsConstantsFieldsActual
end
