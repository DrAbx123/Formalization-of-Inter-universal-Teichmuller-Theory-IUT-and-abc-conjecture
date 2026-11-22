import tmp.sheaf.xif.paper.S2238QVNormActual

/-! # S2245: log-Kummer API gap on the selected paper O^× carrier

The S2238 q_v is actual.  The remaining S2238 logKummer datum asks for an actual
endomorphism of `S2219PaperOUnits` compatible with q_v.  The paper log-Kummer of
`OrigXiFPaperLogKummerActual` is a `SourceKummerArrow` between F-prime-strips, not
an endomorphism of the selected integral-closure unit group, and no p-adic log is
available on the non-complete algebraic closure.  This file records the exact
missing transfer data; no endomorphism is fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2245LogKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2230QVLogKummerActual
open LeanFormal.IUT.XiFPaper.S2238QVNormActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing log-Kummer datum on the selected paper O^× carrier. -/
structure S2245LogKummerRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  logKummer : S2219PaperOUnits T b →* S2219PaperOUnits T b
  logKummer_qv_compatible : Prop

def S2245LogKummerRequiredProp
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (S2245LogKummerRequired T b)

/-- The S2245 datum is exactly the S2238 logKummer datum. -/
noncomputable def s2245ToS2238
    (M : S2245LogKummerRequired T b) :
    S2238LogKummerRequired T b where
  logKummer := M.logKummer
  logKummer_qv_compatible := M.logKummer_qv_compatible

theorem s2245ToS2238_Prop
    (M : S2245LogKummerRequired T b) :
    S2238LogKummerRequiredProp T b :=
  ⟨s2245ToS2238 T b M⟩

#check S2245LogKummerRequired
#check S2245LogKummerRequiredProp
#check s2245ToS2238
#check s2245ToS2238_Prop

end LeanFormal.IUT.XiFPaper.S2245LogKummerActual
end
