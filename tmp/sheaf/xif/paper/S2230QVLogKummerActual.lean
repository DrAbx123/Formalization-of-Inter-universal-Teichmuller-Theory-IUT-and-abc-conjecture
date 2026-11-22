import tmp.sheaf.xif.paper.S2222PaperOUnitsMuAttachmentActual
import tmp.sheaf.xif.paper.S2040PaperOtriFromS2092Actual

/-! # S2230: actual q_v candidate in the integral closure; logKummer exact missing

Takes the actual paper q_v of S2092 in its completed local field and maps it into
the S2147 integral closure.  Nonvanishing is proved.  Integrality, norm < 1, and
the log-Kummer compatibility are recorded as exact missing (the norms of the
original completion and the normalized completion are different instances). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2230QVLogKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2092PaperOtriActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2222PaperOUnitsMuAttachmentActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Candidate paper q_v in the integral closure, obtained from the actual S2092
paper q_v by the algebra map into the normed algebraic closure. -/
noncomputable def s2230qv : S2147PaperIntegralClosure T b :=
  algebraMap (NormalizedCompletion (sectionKPlace T b))
    (S2147PaperIntegralClosure T b)
    (((paperQV T b : paperOtri T b) : paperKv T b))

/-- Exact missing q_v/logKummer data on the selected paper O^×μ carrier. -/
structure S2230QVLogKummerRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  qv_ne_zero : s2230qv T b ≠ 0
  qv_integral : s2230qv T b ∈ Integers (S2147PaperIntegralClosure T b)
  qv_norm_lt_one : ‖s2230qv T b‖ < 1
  logKummer : S2219PaperOUnits T b →* S2219PaperOUnits T b
  logKummer_qv_compatible : Prop

def S2230QVLogKummerRequiredProp
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (S2230QVLogKummerRequired T b)

#check s2230qv
#check S2230QVLogKummerRequired
#check S2230QVLogKummerRequiredProp

end LeanFormal.IUT.XiFPaper.S2230QVLogKummerActual
end
