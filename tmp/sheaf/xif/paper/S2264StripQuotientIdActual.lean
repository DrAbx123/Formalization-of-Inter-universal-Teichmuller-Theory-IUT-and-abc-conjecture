import tmp.sheaf.xif.paper.S2249LogKummerTransportActual
import tmp.sheaf.xif.paper.S2034OperationKummerActual

/-! # S2264: strip quotient identification via the S2034 local Kummer transport

S2034 gives an actual `kummerMuEquiv v : actualOUnitsMu v ≃*
TimesMuQuotient ((localOFieldStrip.Mon v)^x)`.  Composing its inverse with a
bridge `actualOUnitsMu v ≃* S2219PaperOUnitsMu` yields the source strip-quotient
identification for the localOFieldStrip.  The bridge itself is the exact missing
datum. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2264StripQuotientIdActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2249LogKummerTransportActual
open LeanFormal.IUT.XiFPaper.S2034OperationKummerActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.Theorem311Source

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing bridge from the S1978/S2034 actual local O^×μ carrier to the
selected S2219 paper O^×μ carrier. -/
structure S2264ActualLocalBridgeRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  v : LocV
  bridge : actualOUnitsMu v ≃* S2219PaperOUnitsMu T b

/-- Conditional source strip-quotient identification for `localOFieldStrip v`. -/
noncomputable def s2264LocalStripQuotientIso
    (B : S2264ActualLocalBridgeRequired T b) :
    TimesMuQuotient ((localOFieldStrip.Mon B.v)ˣ) ≃* S2219PaperOUnitsMu T b :=
  (kummerMuEquiv B.v).symm.trans B.bridge

/-- Exact remaining q-pilot side: source row identifications plus the arrow. -/
structure S2264QPilotSideRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  V : Type u
  upper : FPrimeStrip V
  lower : FPrimeStrip V
  v : V
  G : Type u
  [groupG : Group G]
  [topG : TopologicalSpace G]
  arrow : @SourceKummerArrow V G _ _ upper lower
  targetIso : TimesMuQuotient ((lower.Mon v)ˣ) ≃* S2219PaperOUnitsMu T b

#check S2264ActualLocalBridgeRequired
#check s2264LocalStripQuotientIso
#check S2264QPilotSideRequired

end LeanFormal.IUT.XiFPaper.S2264StripQuotientIdActual
end
