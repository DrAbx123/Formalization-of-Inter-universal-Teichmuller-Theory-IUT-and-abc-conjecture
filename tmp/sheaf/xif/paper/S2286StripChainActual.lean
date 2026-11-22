import tmp.sheaf.xif.paper.S2280PaperVPrimeMatchActual
import tmp.sheaf.xif.paper.S2249LogKummerTransportActual

/-! # S2286: strip chain under the S2135 prime-alignment input

Combines S2280 (paper V-prime matching from S2135) and S2264 (local strip
quotient identification) with the S2034 actual local Kummer arrow to construct
`S2249StripQuotientIdentificationRequired`, conditional on the known exact missing
input `S2135PrimeAlignmentRequired`.  The remaining gaps are exactly S2135 and the
unit-level log-Kummer lift. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2286StripChainActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2268LocalBridgeActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2280PaperVPrimeMatchActual
open LeanFormal.IUT.XiFPaper.S2264StripQuotientIdActual
open LeanFormal.IUT.XiFPaper.S2249LogKummerTransportActual
open LeanFormal.IUT.XiFPaper.S2232Layer1PrimeAlignmentActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2034OperationKummerActual
open LeanFormal.IUT.Theorem311Source

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Under S2135 prime alignment, the S2249 strip-quotient identification exists
using the actual local Kummer arrow and the S2264/S2280 chain. -/
noncomputable def s2286StripQuotientIdentification
    (h : S2135PrimeAlignmentRequired T b) :
    S2249StripQuotientIdentificationRequired T b := by
  let B : S2264ActualLocalBridgeRequired T b := s2280S2264BridgeOfStrip T b h
  exact
    { V := LocV
      upper := localOFieldStrip
      lower := localOFieldStrip
      v := B.v
      G := LocG
      arrow := actualKummerArrow
      sourceIso := s2264LocalStripQuotientIso T b B
      targetIso := s2264LocalStripQuotientIso T b B }

/-- The conditional automorphism of paper O^×μ from S2135. -/
noncomputable def s2286MuAut
    (h : S2135PrimeAlignmentRequired T b) :
    S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b :=
  s2249MuAut T b (s2286StripQuotientIdentification T b h)

/-- Remaining exact missing data: S2135 plus the unit-level log-Kummer lift. -/
structure S2286RemainingRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  primeAlignment : S2135PrimeAlignmentRequired T b
  logKummerUnits : S2249LogKummerOnUnitsRequired T b

def S2286RemainingRequiredProp
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (S2286RemainingRequired T b)

#check s2286StripQuotientIdentification
#check s2286MuAut
#check S2286RemainingRequired
#check S2286RemainingRequiredProp

end LeanFormal.IUT.XiFPaper.S2286StripChainActual
end
