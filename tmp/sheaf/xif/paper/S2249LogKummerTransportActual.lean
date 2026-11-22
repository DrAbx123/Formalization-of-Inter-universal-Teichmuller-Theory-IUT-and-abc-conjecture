import tmp.sheaf.xif.paper.S2222PaperOUnitsMuAttachmentActual
import tmp.sheaf.xif.paper.S2245LogKummerActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

/-! # S2249: transport from a SourceKummerArrow to the paper O^×μ carrier

The paper log-Kummer arrow is a `SourceKummerArrow G upper lower` whose layer
contains a `TimesMuKummer.Isomorphism` at each place.  Given canonical
identifications of the upper and lower strip unit quotients with the selected
S2219 O^×μ carrier, this yields an actual automorphism of S2219PaperOUnitsMu.
The identification itself is the exact missing datum. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2249LogKummerTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2222PaperOUnitsMuAttachmentActual
open LeanFormal.IUT.XiFPaper.S2245LogKummerActual
open LeanFormal.IUT.Theorem311Source

universe uG uV uMon uPi

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing strip-unit-quotient identification needed for the transport. -/
structure S2249StripQuotientIdentificationRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  V : Type uV
  upper : FPrimeStrip.{uMon, uV, uPi} V
  lower : FPrimeStrip.{uMon, uV, uPi} V
  v : V
  G : Type uG
  [groupG : Group G]
  [topG : TopologicalSpace G]
  arrow : @SourceKummerArrow V G _ _ upper lower
  sourceIso :
    TimesMuQuotient ((upper.Mon v)ˣ) ≃* S2219PaperOUnitsMu T b
  targetIso :
    TimesMuQuotient ((lower.Mon v)ˣ) ≃* S2219PaperOUnitsMu T b

/-- Conditional canonical transport: a strip quotient identification produces an
actual automorphism of the paper O^×μ carrier from the Kummer arrow. -/
noncomputable def s2249MuAut
    (D : S2249StripQuotientIdentificationRequired T b) :
    S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b := by
  letI := D.groupG
  letI := D.topG
  exact D.sourceIso.symm.trans ((D.arrow.layer.kummer D.v).equiv.trans D.targetIso)

/-- Exact missing lift of the Kummer quotient automorphism to an endomorphism of
the integral-closure unit group, compatible with the quotient map. -/
structure S2249LogKummerOnUnitsRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  muAut : S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b
  unitMap : S2219PaperOUnits T b →* S2219PaperOUnits T b
  compat : ∀ u : S2219PaperOUnits T b,
    s2219QuotientMap T b (unitMap u) = muAut (s2219QuotientMap T b u)

def S2249LogKummerOnUnitsRequiredProp
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (S2249LogKummerOnUnitsRequired T b)

/-- The unit-level transport datum maps to the S2245 log-Kummer obligation. -/
noncomputable def s2249ToS2245
    (D : S2249LogKummerOnUnitsRequired T b) :
    S2245LogKummerRequired T b where
  logKummer := D.unitMap
  logKummer_qv_compatible := ∀ u : S2219PaperOUnits T b,
    s2219QuotientMap T b (D.unitMap u) =
      D.muAut (s2219QuotientMap T b u)

#check S2249StripQuotientIdentificationRequired
#check s2249MuAut
#check S2249LogKummerOnUnitsRequired
#check S2249LogKummerOnUnitsRequiredProp

end LeanFormal.IUT.XiFPaper.S2249LogKummerTransportActual
end
